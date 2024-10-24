import Mathlib

open Finset BigOperators

example (n : ℕ) : ∑ i in (Finset.range (n + 1)), i = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
  rw [Finset.sum_range_succ]
  rw [ih]
  apply (Nat.mul_right_inj two_ne_zero).1
  rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n+1)))]
  rw [mul_add]
  rw [← Nat.mul_div_assoc _ (even_iff_two_dvd.1 (Nat.even_mul_succ_self (n)))]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  ring

/- Exercise 1 -/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1)
 : ∑ i ∈ range (n + 1), a * r^i = (a * r^(n + 1) - a) / (r - 1) := by
 have h1 : r - 1 ≠ 0 := sub_ne_zero_of_ne h
 induction n with
 | zero =>
   simp
   rw [← mul_sub_one, mul_div_assoc, div_self, mul_one]
   exact h1
 | succ n ih =>
   rw [sum_range_succ]
   rw [ih]
   repeat rw [sub_div _ _ (r - 1)]
   rw [add_comm _ (a * r ^ (n + 1))]
   rw [← add_sub_assoc, sub_left_inj]
   rw [add_comm]
   rw [div_add' (a * r ^ (n + 1)) (a * r ^ (n + 1)) (r - 1) h1]
   rw [div_left_inj' h1]
   ring


/- Exercise 2

Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then

 (i) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.

-/

example (n k : ℕ) (_ : n > 0) (_ : k > 0) (_ : k ≤ n) :
 Nat.choose n 0 = Nat.choose n n ∧ Nat.choose n n = 1 := by
  apply And.intro
  { rw [Nat.choose_zero_right, Nat.choose_self] }
  { rw [Nat.choose_self] }

example (n k : ℕ) (_ : n > 0) (_ : k > 0) (h3 : k ≤ n) :
 Nat.choose n k = Nat.choose n (n - k) := by
  rw [Nat.choose_symm h3]


/- Exercise 3

We define a function recursively for all positive integers $n$ by
$f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$.

Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second principle
of mathematical induction.
-/

section Solution1

theorem test (f : ℕ → ℤ)
 (h0 : f 0 = 2)
 (h1 : f 1 = 1)
 (h2 : f 2 = 5)
 (h : ∀ n, f (n + 2) = f (n + 1) + 2 * f n)
 : ∀ n, f n = 2 ^ n + (-1) ^ n
 | 0 => h0
 | 1 => h1
 | 2 => h2
 | (n + 2) => by
  rw [h n]
  rw [test f h0 h1 h2 h (n + 1)]
  rw [test f h0 h1 h2 h n]
  ring

end Solution1

section Solution2

example {f : ℕ → ℤ}
    (h0 : f 0 = 2) (h1 : f 1 = 1) (_ : f 2 = 5)
    (h : ∀ n, f (n + 2) = f (n + 1) + 2 * f n) :
    ∀ n, f n = 2 ^ n + (-1) ^ n := by
  intro n
  induction' n using Nat.strongRecOn with n ihn
  rcases n
  . simp
    exact h0
  . rename_i n'
    cases n'
    . simp
      exact h1
    . rename_i n'
      have t0: n' + 1 + 1 = n' + 2 := by linarith
      have t1: n' + 1 < n' + 2 := by linarith
      have t2: n' < n' + 2 := by linarith
      rw [t0] at ihn ⊢; rw [h]
      apply ihn at t1; rw [t1]
      apply ihn at t2; rw [t2]
      ring

end Solution2
