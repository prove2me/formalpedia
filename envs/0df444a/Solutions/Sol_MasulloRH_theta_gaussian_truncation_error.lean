-- Prove2me | solution 1 for MasulloRH.theta_gaussian_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:24:34.171061+00:00
-- url     : https://prove2.me/submissions/97af6e8c-bf3a-4edd-a74d-4be62b0e2721

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_MasulloRH_GaussianThetaApproximation

open scoped BigOperators
set_option autoImplicit false

namespace MasulloRH.ThetaTail

noncomputable def combo (a t : ℝ) : ℂ :=
  ((Real.exp (-a * t ^ 2) - 3 * Real.exp (-4 * a * t ^ 2) +
    2 * Real.exp (-16 * a * t ^ 2) : ℝ) : ℂ)

lemma combo_zero (a : ℝ) : combo a 0 = 0 := by
  norm_num [combo]

lemma combo_neg (a t : ℝ) : combo a (-t) = combo a t := by
  simp only [combo, neg_sq]

lemma norm_combo_le (a t : ℝ) (ha : 0 ≤ a) :
    ‖combo a t‖ ≤ 6 * Real.exp (-a * t ^ 2) := by
  have hB : Real.exp (-4 * a * t ^ 2) ≤ Real.exp (-a * t ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sq_nonneg t)])
  have hC : Real.exp (-16 * a * t ^ 2) ≤ Real.exp (-a * t ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sq_nonneg t)])
  rw [combo, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [Real.exp_nonneg (-a * t ^ 2),
    Real.exp_nonneg (-4 * a * t ^ 2), Real.exp_nonneg (-16 * a * t ^ 2)]

lemma gaussian_geometric_majorant (a C : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (K n : ℕ) :
    C * Real.exp (-a * ((n : ℝ) + K + 1) ^ 2) ≤
      (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2)) *
        Real.exp (-a * (2 * (K : ℝ) + 3)) ^ n := by
  have hn : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    exact_mod_cast Nat.le_mul_self n
  have hexp : -a * ((n : ℝ) + K + 1) ^ 2 ≤
      -a * ((K : ℝ) + 1) ^ 2 + (n : ℝ) * (-a * (2 * (K : ℝ) + 3)) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hn)]
  calc
    _ ≤ C * Real.exp
        (-a * ((K : ℝ) + 1) ^ 2 + (n : ℝ) * (-a * (2 * (K : ℝ) + 3))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]; ring

lemma gaussian_geometric_hasSum (a C : ℝ) (ha : 0 < a) (K : ℕ) :
    HasSum (fun n : ℕ => (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2)) *
      Real.exp (-a * (2 * (K : ℝ) + 3)) ^ n)
      (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3)))) := by
  have hq : Real.exp (-a * (2 * (K : ℝ) + 3)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [show (0 : ℝ) ≤ K by positivity])
  simpa only [div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one (Real.exp_nonneg _) hq).mul_left
      (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2))

lemma summable_of_gaussian_bound (f : ℕ → ℂ) (a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖f n‖ ≤ C * Real.exp (-a * ((n : ℝ) + 1) ^ 2)) : Summable f := by
  apply (gaussian_geometric_hasSum a C ha 0).summable.of_norm_bounded
  intro n
  exact (h n).trans (by simpa using gaussian_geometric_majorant a C ha.le hC 0 n)

lemma norm_gaussian_tsum_tail_le (f : ℕ → ℂ) (a C : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖f n‖ ≤ C * Real.exp (-a * ((n : ℝ) + 1) ^ 2)) (K : ℕ) :
    ‖(∑' n : ℕ, f n) - ∑ n ∈ Finset.range K, f n‖ ≤
      C * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3))) := by
  have hf := summable_of_gaussian_bound f a C ha hC h
  have hs := gaussian_geometric_hasSum a C ha K
  have htail : ∀ n : ℕ, ‖f (n + K)‖ ≤
      (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2)) *
        Real.exp (-a * (2 * (K : ℝ) + 3)) ^ n := by
    intro n
    have h' := h (n + K)
    simp only [Nat.cast_add] at h'
    exact h'.trans (gaussian_geometric_majorant a C ha.le hC K n)
  have hfn : Summable (fun n : ℕ => ‖f (n + K)‖) :=
    hs.summable.of_nonneg_of_le (fun n => norm_nonneg _) htail
  calc
    _ = ‖∑' n : ℕ, f (n + K)‖ := by
      rw [← hf.sum_add_tsum_nat_add K]
      congr 1
      abel
    _ ≤ ∑' n : ℕ, ‖f (n + K)‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' n : ℕ, (C * Real.exp (-a * ((K : ℝ) + 1) ^ 2)) *
        Real.exp (-a * (2 * (K : ℝ) + 3)) ^ n :=
      hfn.tsum_le_tsum htail hs.summable
    _ = _ := hs.tsum_eq

lemma combo_int_tsum_eq (a : ℝ) (ha : 0 < a) :
    (∑' k : ℤ, combo a (k : ℝ)) = 2 * ∑' n : ℕ, combo a ((n : ℝ) + 1) := by
  have hp := summable_of_gaussian_bound (fun n : ℕ => combo a ((n : ℝ) + 1))
    a 6 ha (by norm_num) (fun n => norm_combo_le a _ ha.le)
  have hpos : Summable (fun n : ℕ => combo a (((n : ℤ) + 1 : ℤ) : ℝ)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hp
  have hneg : Summable (fun n : ℕ => combo a ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, combo_neg] using hp
  have hs := tsum_of_add_one_of_neg_add_one (f := fun k : ℤ => combo a (k : ℝ)) hpos hneg
  simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero,
    combo_neg, combo_zero, add_zero, two_mul] using hs

/-- Explicit error for the finite symmetric truncation of the dyadic Gaussian lattice sum. -/
theorem norm_combo_int_tail_le (a : ℝ) (ha : 0 < a) (K : ℕ) :
    ‖(∑' k : ℤ, combo a (k : ℝ)) -
      2 * ∑ n ∈ Finset.range K, combo a ((n : ℝ) + 1)‖ ≤
      12 * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3))) := by
  have h := norm_gaussian_tsum_tail_le
    (fun n : ℕ => combo a ((n : ℝ) + 1)) a 6 ha (by norm_num)
    (fun n => norm_combo_le a _ ha.le) K
  rw [combo_int_tsum_eq a ha, ← mul_sub, norm_mul, Complex.norm_two]
  calc
    _ ≤ 2 * (6 * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3)))) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring


end MasulloRH.ThetaTail

open scoped BigOperators
open MasulloRH.GaussianApproximation
set_option autoImplicit false

/-- A fully explicit enclosure for truncating the actual dyadic Gaussian theta sum.
The finite approximation pairs the equal positive and negative integer terms; its zero term is zero.
No RH, Mertens bound, or analytic-density hypothesis is needed. -/
theorem solution (x : ℝ) (K : ℕ) :
    ‖theta x - 2 * ∑ n ∈ Finset.range K,
      ((Real.exp (-Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2) -
        3 * Real.exp (-Real.pi * (2 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) +
        2 * Real.exp (-Real.pi * (4 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) : ℝ) : ℂ)‖ ≤
      12 * Real.exp (-Real.pi * (Real.exp x) ^ 2 * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-Real.pi * (Real.exp x) ^ 2 * (2 * (K : ℝ) + 3))) := by
  have hpos : 0 < Real.pi * (Real.exp x) ^ 2 := by positivity
  have he₁ (t : ℝ) : -Real.pi * (t * Real.exp x) ^ 2 =
      -(Real.pi * (Real.exp x) ^ 2) * t ^ 2 := by ring
  have he₂ (t : ℝ) : -Real.pi * (2 * (t * Real.exp x)) ^ 2 =
      -4 * (Real.pi * (Real.exp x) ^ 2) * t ^ 2 := by ring
  have he₄ (t : ℝ) : -Real.pi * (4 * (t * Real.exp x)) ^ 2 =
      -16 * (Real.pi * (Real.exp x) ^ 2) * t ^ 2 := by ring
  simpa only [theta, MasulloRH.ThetaTail.combo, he₁, he₂, he₄, neg_mul] using
    MasulloRH.ThetaTail.norm_combo_int_tail_le (Real.pi * (Real.exp x) ^ 2) hpos K
