-- Prove2me | solution 1 for OAI.Laughlin.pairCoefficient_unit_norm_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:42:47.409629+00:00
-- url     : https://prove2.me/submissions/4427efa7-77f2-421e-a2a2-a7ba968cd199

import Mathlib
import Definitions.Def_OAIQ050L006

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.PairNormalization
open scoped BigOperators
open Finset Finset.Nat

theorem binomial_convolution (m n k : ℕ) :
    (∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+n).choose k : ℝ) := by
  exact_mod_cast (Nat.add_choose_eq m n k).symm

theorem weighted_choose (m i : ℕ) :
    ((i+1 : ℕ) : ℝ) * ((m+1).choose (i+1) : ℝ) =
      ((m+1 : ℕ) : ℝ) * (m.choose i : ℝ) := by
  have h : (i+1) * (m+1).choose (i+1) = (m+1) * m.choose i := by
    simpa only [mul_comm] using (Nat.add_one_mul_choose_eq m i).symm
  exact_mod_cast h

theorem weighted_shift (m k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * f ij.1 ij.2) =
      ((m+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * f (ij.1+1) ij.2 := by
  rw [sum_antidiagonal_succ]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_first_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  rw [weighted_shift m k (fun _ j => (n.choose j : ℝ)), binomial_convolution]

theorem weighted_shift_right (n k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ) * f ij.1 ij.2) =
      ((n+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * f ij.1 (ij.2+1) := by
  rw [sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_second_falling (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      ((m+2).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
    ((m+2 : ℕ) : ℝ) * ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+2).choose ij.1 : ℝ) *
          (((ij.1 : ℝ)-1) * (n.choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          ((m+1).choose ij.1 : ℝ) *
            (((ij.1+1 : ℕ) : ℝ)-1) * (n.choose ij.2 : ℝ) := by
      simpa only [mul_assoc] using weighted_shift (m+1) (k+1)
        (fun i j => ((i : ℝ)-1) * (n.choose j : ℝ))
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      push_cast
      ring
    _ = _ := by rw [binomial_first_moment]; ring

theorem binomial_cross_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * (ij.2 : ℝ) *
      ((m+1).choose ij.1 : ℝ) * ((n+1).choose ij.2 : ℝ)) =
    ((m+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (m.choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) :=
      weighted_shift m (k+1) (fun _ j => (j : ℝ) * ((n+1).choose j : ℝ))
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) *
          ((n+1).choose ij.2 : ℝ) * (m.choose ij.1 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * (m.choose ij.1 : ℝ)) := by
      rw [weighted_shift_right n k (fun i _ => (m.choose i : ℝ))]
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = _ := by rw [binomial_convolution]; ring

theorem difference_decomposition (Q n : ℕ) :
    (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
  have hfirst : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hfall : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * ((ij.1 : ℝ)-1) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hpoint : (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [hpoint, hfirst, hfall]
  ring

theorem pair_binomial_moment (m p : ℕ) :
    (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      ((m+2).choose ij.1 : ℝ) * ((m+2).choose ij.2 : ℝ)) =
      2 * ((m+2 : ℕ) : ℝ) * ((2*m+2).choose p : ℝ) := by
  cases p with
  | zero =>
    rw [sum_antidiagonal_succ]
    simp [Nat.choose_one_right]
    ring
  | succ k =>
    rw [difference_decomposition, binomial_second_falling m (m+2) k,
      binomial_first_moment (m+1) (m+2) (k+1), binomial_cross_moment (m+1) (m+1) k]
    have hA : m+(m+2) = 2*m+2 := by omega
    have hB : m+1+(m+2) = (2*m+2)+1 := by omega
    have hC : m+1+(m+1) = 2*m+2 := by omega
    rw [hA, hB, hC]
    have hp : (((2*m+2)+1).choose (k+1) : ℝ) =
        ((2*m+2).choose k : ℝ) + ((2*m+2).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (2*m+2) k
    rw [hp]
    push_cast
    ring

end Laughlin.PairNormalization

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoefficientSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairCoefficient_sq_choose (Q p : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    (pairCoefficient Q p x y)^2 =
      if x.val+y.val = p+1 then
        (((x.val : ℝ)-(y.val : ℝ))^2 * (Q.choose x.val : ℝ) * (Q.choose y.val : ℝ)) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
      else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs with h
  · rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators
open Finset Finset.Nat

theorem finite_pair_antidiagonal (Q n : ℕ) (f : ℕ → ℕ → ℝ)
    (hz : ∀ i j, Q < i ∨ Q < j → f i j = 0) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = n then f x.val y.val else 0) =
        ∑ ij ∈ antidiagonal n, f ij.1 ij.2 := by
  classical
  rw [← Fintype.sum_prod_type (f := fun a : Fin (Q+1) × Fin (Q+1) =>
    if a.1.val+a.2.val = n then f a.1.val a.2.val else 0)]
  refine Finset.sum_bij_ne_zero (fun a _ _ => (a.1.val,a.2.val)) ?_ ?_ ?_ ?_
  · intro a ha hn
    apply HasAntidiagonal.mem_antidiagonal.mpr
    by_contra h
    exact hn (by simp [h])
  · intro a ha hna b hb hnb hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hab)
    · exact Fin.ext (congrArg Prod.snd hab)
  · rintro ⟨i,j⟩ hij hn
    have hi : i < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inl (by omega)))
    have hj : j < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inr (by omega)))
    have hs : i+j = n := HasAntidiagonal.mem_antidiagonal.mp hij
    let a : Fin (Q+1) × Fin (Q+1) := (⟨i,hi⟩,⟨j,hj⟩)
    refine ⟨a, mem_univ a, ?_, rfl⟩
    simpa [a, hs] using hn
  · intro a ha hn
    have hs : a.1.val+a.2.val = n := by
      by_contra h
      exact hn (by simp [h])
    simp [hs]

theorem pairCoefficient_unit_norm_s50_oai (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1), (pairCoefficient Q p x y)^2) = 1 := by
  let f : ℕ → ℕ → ℝ := fun i j =>
    ((i : ℝ)-(j : ℝ))^2 * (Q.choose i : ℝ) * (Q.choose j : ℝ) /
      (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
  have hz : ∀ i j, Q < i ∨ Q < j → f i j = 0 := by
    intro i j h
    rcases h with h | h
    · simp [f, Nat.choose_eq_zero_of_lt h]
    · simp [f, Nat.choose_eq_zero_of_lt h]
  simp_rw [pairCoefficient_sq_choose Q p (by omega) hp]
  change (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = p+1 then f x.val y.val else 0) = 1
  rw [finite_pair_antidiagonal Q (p+1) f hz]
  simp only [f, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  have hmoment : (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      2*(Q : ℝ)*((2*Q-2).choose p : ℝ) := by
    have h := PairNormalization.pair_binomial_moment (Q-2) p
    have h₁ : Q-2+2 = Q := by omega
    have h₂ : 2*(Q-2)+2 = 2*Q-2 := by omega
    simpa only [h₁, h₂] using h
  rw [hmoment]
  apply div_self
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  exact mul_ne_zero (mul_ne_zero (by norm_num) hq) hc

end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.pairCoefficient_unit_norm_s50_oai := @OAI.Laughlin.pairCoefficient_unit_norm_s50_oai
