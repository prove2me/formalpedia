-- Prove2me | solution 1 for OAI.Cotype.finiteSupDual_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:54:30.677972+00:00
-- url     : https://prove2.me/submissions/a07d4d8a-cc05-4f1b-93e4-d34a903b04ed

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
theorem h50s_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

theorem solution (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteSupDual g‖ = ∑ a, ‖g a‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun a _ => norm_nonneg _)
      (finiteSupDualLinear_bound g)
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hc : (0 : ℝ) < Fintype.card Ω + 1 := by positivity
    have hε' : 0 < ε / (Fintype.card Ω + 1) := div_pos hε hc
    choose x hx1 hx2 using fun a => h50s_eval (g a) (sub_lt_self (‖g a‖) hε')
    have hxn : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hx1
    have hv : ∑ a, (‖g a‖ - ε / (Fintype.card Ω + 1)) ≤ finiteSupDual g x := by
      rw [finiteSupDual_apply]
      exact Finset.sum_le_sum fun a _ => (hx2 a).le
    have hF : finiteSupDual g x ≤ ‖finiteSupDual g‖ := by
      calc finiteSupDual g x ≤ ‖finiteSupDual g x‖ := Real.le_norm_self _
        _ ≤ ‖finiteSupDual g‖ * ‖x‖ := (finiteSupDual g).le_opNorm x
        _ ≤ ‖finiteSupDual g‖ * 1 := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
        _ = _ := mul_one _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hv
    have : (Fintype.card Ω : ℝ) * (ε / (Fintype.card Ω + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hc]; nlinarith
    linarith

