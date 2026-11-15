-- Prove2me | solution 1 for InfoLossLAR.WorstCase.IntegerBasis.queryTrajectory_stopping
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:31:10.955428+00:00
-- url     : https://prove2.me/submissions/3155d0a2-af44-44c2-9d12-8e7990e6ce53

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_residual_error_norm

set_option autoImplicit false

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

/-- Every correct modular stage contracts the full actual Euclidean error
by exactly 1/q; there is no coordinatewise-only invariant. -/
theorem queryTrajectory_error_norm
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet))
    (query : Space (dimension:=dimension)) (count : ℕ) :
    ‖queryTrajectory basis hdet q nearest count query-
      (nearestTrajectory basis hdet q count nearest : Space (dimension:=dimension))‖=
      ‖query-(nearest : Space (dimension:=dimension))‖/(q : ℝ)^count := by
  induction count with
  | zero => simp only [queryTrajectory,nearestTrajectory,pow_zero,div_one]
  | succ count ih =>
    rw [queryTrajectory,nearestTrajectory,residual_error_norm,ih,pow_succ]
    ring

end

end InfoLossLAR.WorstCase.IntegerBasis



open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv InfoLossLAR.WorstCase.GaussianProjection InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

theorem solution {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (nearest : dual (inputLattice basis hdet)) (query : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))
    (radius : ℝ) (exponent : ℕ)
    (hquery : ‖query-(nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖ ≤ radius)
    (hcolumns : ∀ index : Fin dimension,radius*‖(integerBasis basis hdet index : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖ ≤ (2 : ℝ)^exponent) :
    ∀ index : Fin dimension,
      ‖queryTrajectory basis hdet q nearest (exponent+2) query-
        (nearestTrajectory basis hdet q (exponent+2) nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖*
        ‖(integerBasis basis hdet index : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖ < 1/2 := by
  intro index
  rw [queryTrajectory_error_norm,div_mul_eq_mul_div]
  have hproduct := (mul_le_mul_of_nonneg_right hquery (norm_nonneg _)).trans (hcolumns index)
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpower : (2 : ℝ)^(exponent+2) ≤ (q : ℝ)^(exponent+2) :=
    pow_le_pow_left₀ (by norm_num) hqReal _
  have hqPositive : (0 : ℝ) < (q : ℝ)^(exponent+2) := by positivity
  have hratio : (2 : ℝ)^exponent/(q : ℝ)^(exponent+2) ≤ 1/4 := by
    apply (div_le_iff₀ hqPositive).mpr
    have hscaled : (2 : ℝ)^exponent ≤ (1/4 : ℝ)*(2 : ℝ)^(exponent+2) := by
      rw [pow_add]
      norm_num
      nlinarith
    exact hscaled.trans (mul_le_mul_of_nonneg_left hpower (by norm_num))
  exact ((div_le_div_of_nonneg_right hproduct hqPositive.le).trans hratio).trans_lt (by norm_num)
