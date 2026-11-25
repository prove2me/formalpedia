-- Prove2me | solution 1 for GlobalTheory.TensorLat.tensorLat_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:29.370887+00:00
-- url     : https://prove2.me/submissions/dc8694e8-d9d7-4bd6-b590-dcf9f77980f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat
import Theorems.Thm_GlobalTheory_exists_dual_family
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
    tensorLat X Λ' = Submodule.span ℤ {γ | ∃ x ∈ X.L, ∃ v ∈ Λ', γ = tens x v} := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  apply le_antisymm
  · intro γ hγ
    rw [eq_sum_tens_contr hexp γ]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, mem_tensorLat.1 hγ (w i) (hw i), v i, hv i, rfl⟩
  · rw [Submodule.span_le]
    rintro γ ⟨x, hx, u, hu, rfl⟩
    exact tens_mem_of_integral hint hx hu
end GlobalTheory.TensorLat
