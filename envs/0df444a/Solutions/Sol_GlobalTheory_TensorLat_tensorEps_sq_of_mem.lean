-- Prove2me | solution 1 for GlobalTheory.TensorLat.tensorEps_sq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:28:12.069834+00:00
-- url     : https://prove2.me/submissions/7a0531ec-6732-46cd-92c7-669bb8649247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_act_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_im_HC_int
import Theorems.Thm_GlobalTheory_TensorLat_tensorEps_of_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') : tensorEps w₀ γ ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := im_HC_int hfg hint hdual hγ (act_mem_tensorLat w₀ hγ)
  rw [tensorEps_of_int w₀ γ m hm, ← zpow_natCast, ← zpow_mul]
  exact Even.neg_one_zpow ⟨m, by push_cast; ring⟩
end GlobalTheory.TensorLat
