-- Prove2me | solution 1 for OAI.Cotype.finiteL2Dual_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:01:19.927706+00:00
-- url     : https://prove2.me/submissions/70dc7e74-3d6d-4832-ba76-4ece3c40b650

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

open OAI OAI.Cotype
open scoped BigOperators
open WithLp
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
omit [DecidableEq Ω] in
theorem h50l_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

omit [DecidableEq Ω] in
theorem solution (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by
  set N := ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ with hN
  have hN2 : N ^ 2 = ∑ a, ‖g a‖ ^ 2 := by
    rw [hN, PiLp.norm_sq_eq_of_L2]
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (finiteL2DualLinear_bound g)
  · set F := finiteL2Dual g
    have key : ∀ δ > 0, N ^ 2 ≤ ‖F‖ * N + δ := by
      intro δ hδ
      set S := ∑ a, ‖g a‖
      have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => norm_nonneg _
      have he : 0 < δ / (S + 1) := by positivity
      choose x hx1 hx2 using fun a => h50l_eval (g a) (sub_lt_self (‖g a‖) he)
      let z : PiLp 2 (fun _ : Ω => X) := toLp 2 (fun a => ‖g a‖ • x a)
      have hz : ‖z‖ ≤ N := by
        rw [hN, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum; intro a _
        simp only [z, PiLp.toLp_apply, norm_smul, norm_norm]
        exact pow_le_pow_left₀ (by positivity)
          (by simpa using mul_le_mul_of_nonneg_left (hx1 a) (norm_nonneg (g a))) 2
      have hFz : F z ≤ ‖F‖ * N :=
        (Real.le_norm_self _).trans ((F.le_opNorm z).trans
          (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
      have hlow : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) ≤ F z := by
        simp only [F, finiteL2Dual_apply, z, PiLp.toLp_apply, map_smul, smul_eq_mul]
        exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hx2 a).le (norm_nonneg _)
      have hlow' : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) = N ^ 2 - S * (δ / (S + 1)) := by
        rw [hN2]; simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq, S]
      have : S * (δ / (S + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have h2 : N ^ 2 ≤ ‖F‖ * N := le_of_forall_pos_le_add fun δ hδ => key δ hδ
    rcases (norm_nonneg _ : (0:ℝ) ≤ N).eq_or_lt with h0 | h0
    · rw [hN, ← h0]; exact norm_nonneg _
    · nlinarith

