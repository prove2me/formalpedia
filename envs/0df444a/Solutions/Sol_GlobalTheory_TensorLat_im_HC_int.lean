-- Prove2me | solution 1 for GlobalTheory.TensorLat.im_HC_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:36:03.751052+00:00
-- url     : https://prove2.me/submissions/f9a57d3e-5b48-482e-ac94-eaa94134986e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_HC_sum_right
import Theorems.Thm_GlobalTheory_TensorLat_im_HC_tens_int
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
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {γ γ' : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (hγ' : γ' ∈ tensorLat X Λ') :
    ∃ k : ℤ, (HC γ γ').im = k := by
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  have hc := mem_tensorLat.1 hγ'
  choose k hk using fun i => im_HC_tens_int hγ (hc (w i) (hw i)) (hv i)
  refine ⟨∑ i, k i, ?_⟩
  rw [eq_sum_tens_contr hexp γ', HC_sum_right, Complex.im_sum]
  push_cast
  exact Finset.sum_congr rfl fun i _ => hk i
end GlobalTheory.TensorLat
