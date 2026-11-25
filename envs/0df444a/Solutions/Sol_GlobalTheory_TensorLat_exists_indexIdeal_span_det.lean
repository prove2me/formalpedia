-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_indexIdeal_span_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:05.817095+00:00
-- url     : https://prove2.me/submissions/06f39568-0bd6-4e76-ad5a-b2d141a841f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Theorems.Thm_GlobalTheory_TensorLat_exists_coe_eq_span_det
import Theorems.Thm_GlobalTheory_TensorLat_smul_coe_fractionalIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ')
    (hfg : Λ'.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ ∧ Ideal.absNorm 𝔫 = Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ∧
      ∀ 𝔪 : Ideal (𝓞 K), Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} =
        𝔪 • Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ↔ 𝔪 = 𝔫 := by
  obtain ⟨J, J', h0, h0', hJ, hJ', hN⟩ := exists_coe_eq_span_det hle hfg hsp
  have hJJ : J ≤ J' := by
    rw [← FractionalIdeal.coe_le_coe, hJ, hJ']
    exact Submodule.span_mono fun _ ⟨v, hv, h⟩ => ⟨v, fun i => hle (hv i), h⟩
  have h1 : J * J'⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ h0']
    gcongr
  obtain ⟨𝔫, h𝔫⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 h1
  have h2 : J = 𝔫 * J' := by rw [h𝔫, inv_mul_cancel_right₀ h0']
  refine ⟨𝔫, ?_, ?_, fun 𝔪 => ?_⟩
  · rintro rfl
    simp [h0] at h2
  · rw [h2, map_mul, FractionalIdeal.coeIdeal_absNorm] at hN
    exact_mod_cast mul_right_cancel₀ (FractionalIdeal.absNorm_eq_zero_iff.not.2 h0') hN
  · rw [← hJ, ← hJ', smul_coe_fractionalIdeal, FractionalIdeal.coeToSubmodule_inj, h2,
      mul_left_inj' h0', FractionalIdeal.coeIdeal_inj, eq_comm]
end GlobalTheory.TensorLat
