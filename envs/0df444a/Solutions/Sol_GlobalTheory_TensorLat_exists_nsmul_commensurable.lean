-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_nsmul_commensurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:00:38.387719+00:00
-- url     : https://prove2.me/submissions/2d1bc1da-f8b1-4330-af63-5f21b9c76b26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_nsmul_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_nsmul_apply_mem_of_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_exists_nsmul_stdLat_le
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
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L) := by
  obtain ⟨N, hN1, hN⟩ := exists_nsmul_stdLat_le hfg hint hdual
  exact ⟨N, hN1, fun γ hγ => nsmul_mem_tensorLat hint hN hγ,
    fun γ hγ k => nsmul_apply_mem_of_mem_tensorLat hN hγ k⟩
end GlobalTheory.TensorLat
