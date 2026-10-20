-- Prove2me | solution 1 for OAI.Cotype.exists_type_extrapolation_parameters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:06:32.19208+00:00
-- url     : https://prove2.me/submissions/e7568fc4-0fca-4f9f-97ab-2c36b114c433

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


theorem solution {n : ℕ} (hn : 1 < n) {A : ℝ}
    (hA : 0 ≤ A) (hAn : A < n) :
    ∃ p r : ℝ, 1 < p ∧ p ≤ 2 ∧ 1 < r ∧ r^p = n ∧
      0 ≤ Real.sqrt (A*n)*r⁻¹ ∧ Real.sqrt (A*n)*r⁻¹ < 1 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set a := Real.logb n A with ha
  have haA : A < n → a < 1 := by
    intro h
    rcases hA.eq_or_lt with h0 | h0
    · rw [ha, ← h0, Real.logb_zero]; norm_num
    · rw [ha, Real.logb_lt_iff_lt_rpow hn1 h0, Real.rpow_one]; exact h
  have ha1 := haA hAn
  set u := max (3/4 : ℝ) ((a + 3) / 4) with hu
  have hu1 : u < 1 := max_lt (by norm_num) (by linarith)
  have hu0 : 3/4 ≤ u := le_max_left _ _
  have hua : (a + 1) / 2 < u := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hupos : 0 < u := by linarith
  refine ⟨u⁻¹, (n : ℝ) ^ u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_inv_comm₀ one_pos hupos, inv_one]; exact hu1
  · rw [inv_le_comm₀ hupos two_pos]; linarith
  · exact Real.one_lt_rpow hn1 hupos
  · rw [← Real.rpow_mul hn0.le, mul_inv_cancel₀ hupos.ne', Real.rpow_one]
  · positivity
  · have hr : 0 < (n : ℝ) ^ u := Real.rpow_pos_of_pos hn0 u
    rw [mul_inv_lt_iff₀ hr, one_mul]
    have key : A * n < ((n : ℝ) ^ u) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      have e : u * ((2 : ℕ) : ℝ) = (2 * u - 1) + 1 := by push_cast; ring
      rw [e, Real.rpow_add hn0, Real.rpow_one]
      apply mul_lt_mul_of_pos_right _ hn0
      rcases hA.eq_or_lt with h0 | h0
      · rw [← h0]; exact Real.rpow_pos_of_pos hn0 _
      · calc A = (n : ℝ) ^ a := by rw [ha, Real.rpow_logb hn0 hn1.ne' h0]
          _ < (n : ℝ) ^ (2 * u - 1) := Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith)
    calc Real.sqrt (A * n) < Real.sqrt (((n : ℝ) ^ u) ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) key
      _ = (n : ℝ) ^ u := Real.sqrt_sq hr.le

