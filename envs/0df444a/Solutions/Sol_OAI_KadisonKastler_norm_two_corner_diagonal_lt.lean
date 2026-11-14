-- Prove2me | solution 1 for OAI.KadisonKastler.norm_two_corner_diagonal_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:28.962794+00:00
-- url     : https://prove2.me/submissions/1f69d6f1-0674-4f43-bafd-100a1b56d9d9

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Module

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaCornerGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal-corner norm calculations

These are the elementary norm estimates behind Tomiyama's projection
argument. They do not assume positivity or a representation of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Two mutually orthogonal operator blocks have the maximum norm. -/
theorem norm_add_eq_max_of_orthogonal_products (a b : A)
    (hab : star a * b = 0) (hab' : a * star b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hp : (star a * a) * (star b * b) = 0 := by
    calc
      (star a * a) * (star b * b) = star a * (a * star b) * b := by simp only [mul_assoc]
      _ = 0 := by rw [hab', mul_zero, zero_mul]
  have he : ‖a + b‖ ^ 2 = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
    calc
      ‖a + b‖ ^ 2 = ‖star (a + b) * (a + b)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖star a * a + star b * b‖ := by
        congr 1
        simp only [star_add, add_mul, mul_add, hab, hba, add_zero, zero_add]
      _ = max ‖star a * a‖ ‖star b * b‖ :=
        (IsSelfAdjoint.star_mul_self a).norm_add_eq_max (IsSelfAdjoint.star_mul_self b) hp
      _ = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
        rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self, pow_two, pow_two]
  rcases le_total ‖a‖ ‖b‖ with h | h
  · rw [max_eq_right h]
    rw [max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg b]
  · rw [max_eq_left h]
    rw [max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg a]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoCornerStrictContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strict decrease after removing a bounded-below off-diagonal corner

The spatial innerness argument uses a self-adjoint two-by-two operator
whose off-diagonal corner is bounded below on both summands. Removing
that corner strictly decreases the norm. The estimate is purely a
C-star algebra calculation.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem projection_column_square (p z : A) (hp : IsStarProjection p) :
    star (p * z) * (p * z) + star ((1 - p) * z) * ((1 - p) * z) = star z * z := by
  have hq := hp.one_sub
  calc
    _ = star z * (p * p) * z + star z * ((1 - p) * (1 - p)) * z := by
      simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_assoc]
    _ = star z * p * z + star z * (1 - p) * z := by
      rw [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
    _ = star z * z := by noncomm_ring

theorem norm_projection_diagonal_sq_le (p T : A) (hp : IsStarProjection p)
    (ε : ℝ) (hε : 0 ≤ ε) (hεT : ε ≤ ‖T‖)
    (hcorner : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p))) :
    ‖p * T * p‖ ^ 2 ≤ ‖T‖ ^ 2 - ε ^ 2 := by
  have hsquare := projection_column_square p (T * p) hp
  have hbound : star (T * p) * (T * p) ≤ ‖T‖ ^ 2 • p := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := T)) p
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      mul_one, hp.isIdempotentElem.eq] using h
  have ha : star (p * T * p) * (p * T * p) ≤ (‖T‖ ^ 2 - ε ^ 2) • p := by
    have hsum := add_le_add_right hcorner (star (p * (T * p)) * (p * (T * p)))
    rw [hsquare] at hsum
    have h := hsum.trans hbound
    rw [sub_smul]
    exact (le_sub_iff_add_le).mpr (by simpa only [mul_assoc] using h)
  have hc : 0 ≤ ‖T‖ ^ 2 - ε ^ 2 := by nlinarith
  have hp1 : p ≤ (1 : A) := hp.le_one
  have hfinal : star (p * T * p) * (p * T * p) ≤
      algebraMap ℝ A (‖T‖ ^ 2 - ε ^ 2) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact ha.trans (smul_le_smul_of_nonneg_left hp1 hc)
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap _ hc
    (star_mul_self_nonneg _)).mpr hfinal
  simpa only [CStarRing.norm_star_mul_self, pow_two] using hn

theorem norm_two_corner_diagonal_lt_oai (p T : A) (hp : IsStarProjection p)
    (hT : IsSelfAdjoint T) (ε : ℝ) (hε : 0 < ε) (hεT : ε ≤ ‖T‖)
    (hpq : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p)))
    (hqp : ε ^ 2 • (1 - p) ≤ star (p * (T * (1 - p))) * (p * (T * (1 - p)))) :
    ‖p * T * p + (1 - p) * T * (1 - p)‖ < ‖T‖ := by
  have hpbound := norm_projection_diagonal_sq_le p T hp ε hε.le hεT hpq
  have hqbound := norm_projection_diagonal_sq_le (1 - p) T hp.one_sub ε hε.le hεT
    (by simpa only [sub_sub_cancel] using hqp)
  have hpstrict : ‖p * T * p‖ < ‖T‖ := by
    nlinarith [norm_nonneg (p * T * p)]
  have hqstrict : ‖(1 - p) * T * (1 - p)‖ < ‖T‖ := by
    nlinarith [norm_nonneg ((1 - p) * T * (1 - p))]
  rw [norm_add_eq_max_of_orthogonal_products]
  · exact max_lt hpstrict hqstrict
  · simp only [star_mul, hp.isSelfAdjoint.star_eq, hT.star_eq, mul_assoc,
      ← mul_assoc p (1 - p), hp.mul_one_sub_self, zero_mul, mul_zero]
  · simp only [star_mul, hp.one_sub.isSelfAdjoint.star_eq, hT.star_eq, mul_assoc,
      ← mul_assoc p (1 - p), hp.mul_one_sub_self, zero_mul, mul_zero]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.norm_two_corner_diagonal_lt_oai.{u_1} := @OAI.KadisonKastler.norm_two_corner_diagonal_lt_oai.{u_1}
