-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.theta_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:57.896102+00:00
-- url     : https://prove2.me/submissions/a95f4630-ef0b-42d9-98ac-9759eb6c4fe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Theorems.Thm_GlobalTheory_SW_EisBdd_im_nonneg
import Theorems.Thm_GlobalTheory_SW_EisBdd_imH_scalar
import Theorems.Thm_GlobalTheory_SW_EisBdd_imH_sub
import Theorems.Thm_GlobalTheory_SW_EisBdd_posDef_scalar
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_T_hermitianTheta_summable_and_determines_testFn
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisBdd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
open Classical
namespace GlobalTheory.SW.EisBdd
theorem _root_.solution (hΨ : IsType Ψ) {R : ℕ} {δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) →
      ∀ Z ∈ HnGe Ψ N δ, ‖thH Ψ φ Z 0 0‖ ≤ C * B := by
  let φ₀ : Matrix (Fin n) (Fin N) E → ℂ := fun x => if IntM ((R : E) • x) then 1 else 0
  have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  have h₀ : IsSB φ₀ := by
    refine ⟨R, hR, fun x hx => by_contra fun h => hx (if_neg h), fun x y hy => ?_⟩
    refine if_congr (forall_congr' fun k => forall_congr' fun a => ?_) rfl rfl
    have hz : IsIntegral ℤ ((R : E) * ((R : E) * y k a)) := (c R).mul ((c R).mul (hy k a))
    simp only [smul_add, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add]
    exact ⟨fun h => by simpa using h.sub hz, fun h => h.add hz⟩
  let Z₀ : CM Ψ N N := fun _ => (I * δ) • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hZ₀ : Z₀ ∈ Hn Ψ N := fun τ => by
    simp only [Z₀, imH_scalar]; exact posDef_scalar hδ
  have hs := (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ₀ h₀ Z₀ hZ₀).1 0 0
  refine ⟨∑' x, ‖φ₀ x * cexp (2 * π * I * expo Ψ x Z₀ 0 0)‖, fun φ hφ B hB Z hZ => ?_⟩
  rw [← tsum_mul_right]
  refine tsum_of_norm_bounded (hs.mul_right B).hasSum fun x => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, norm_zero]; positivity
  have h1 : φ₀ x = 1 := if_pos (hφ.1 x hx)
  rw [h1, one_mul, norm_mul, mul_comm]
  refine mul_le_mul ?_ (hB x) (norm_nonneg _) (norm_nonneg _)
  rw [Complex.norm_exp, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have h2 : (expo Ψ x Z₀ 0 0).im ≤ (expo Ψ x Z 0 0).im := by
    unfold expo
    rw [Complex.im_sum, Complex.im_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [Complex.im_sum, Complex.im_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h3 := im_nonneg (W := Z τ - Z₀ τ) (by rw [imH_sub, imH_scalar]; exact hZ τ)
      fun a => τ.1 (x k a)
    rw [sub_mulVec, dotProduct_sub, Complex.sub_im, sub_nonneg] at h3
    simp only [Complex.add_im]
    exact add_le_add_left (add_le_add_left h3 _) _
  have h4 : ∀ e : ℂ, (2 * π * I * e).re = -(2 * π * e.im) := fun e => by simp
  rw [h4, h4]
  have := Real.pi_pos
  nlinarith
end GlobalTheory.SW.EisBdd
