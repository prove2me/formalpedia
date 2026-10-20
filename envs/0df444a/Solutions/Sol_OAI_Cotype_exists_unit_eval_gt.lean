-- Prove2me | solution 1 for OAI.Cotype.exists_unit_eval_gt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:53:38.313293+00:00
-- url     : https://prove2.me/submissions/cddd6061-02e1-4f62-ac5b-7bbc3b85239b

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω]
theorem t_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

theorem solution (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  exact t_eval φ ha

