-- Prove2me | solution 1 for GlobalTheory.TensorLat.tensorLat_span_integral_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:24.956624+00:00
-- url     : https://prove2.me/submissions/a0180ef0-d95a-4f0e-8577-1e47dac6911c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_TensorLat_tensorLat_eq_span
import Theorems.Thm_GlobalTheory_TensorLat_im_HC_int
import Theorems.Thm_GlobalTheory_TensorLat_nsmul_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_nsmul_apply_mem_of_mem_tensorLat
import Theorems.Thm_GlobalTheory_TensorLat_exists_nsmul_stdLat_le
import Theorems.Thm_GlobalTheory_TensorLat_exists_nsmul_commensurable
import Theorems.Thm_GlobalTheory_TensorLat_act_mem_tensorLat
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
theorem _root_.solution (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ'.FG) (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    (∃ (m : ℕ) (v w : Fin m → Fin n → E), (∀ i, v i ∈ Λ') ∧ (∀ i, w i ∈ Λ') ∧
      (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) ∧
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    (∀ (m : ℕ) (v w : Fin m → Fin n → E), (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) →
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    tensorLat X Λ' = Submodule.span ℤ {γ | ∃ x ∈ X.L, ∃ v ∈ Λ', γ = tens x v} ∧
    (∀ (α : 𝓞 E), ∀ γ ∈ tensorLat X Λ', (fun k => act α (γ k)) ∈ tensorLat X Λ') ∧
    (∀ γ ∈ tensorLat X Λ', ∀ γ' ∈ tensorLat X Λ', ∃ k : ℤ, (HC γ γ').im = k) ∧
    (∀ φ : tensorLat X Λ' →+ ℤ, ∃ γ ∈ tensorLat X Λ', ∀ γ' : tensorLat X Λ',
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im) ∧
    (∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ stdLat E n, N • u ∈ Λ') ∧
    (∀ N : ℕ, (∀ u ∈ stdLat E n, N • u ∈ Λ') →
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → N • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (N • γ) k ∈ X.L)) ∧
    (∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L)) := by
  refine ⟨?_, fun m v w h γ => eq_sum_tens_contr h γ, tensorLat_eq_span hfg hint hdual,
    fun α γ hγ => act_mem_tensorLat α hγ, fun γ hγ γ' hγ' => im_HC_int hfg hint hdual hγ hγ',
    exists_im_HC_eq hfg hint hdual, exists_nsmul_stdLat_le hfg hint hdual,
    fun N hN => ⟨fun γ hγ => nsmul_mem_tensorLat hint hN hγ,
      fun γ hγ k => nsmul_apply_mem_of_mem_tensorLat hN hγ k⟩,
    exists_nsmul_commensurable hfg hint hdual⟩
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  exact ⟨m, v, w, hv, hw, hexp, fun γ => eq_sum_tens_contr hexp γ⟩
end GlobalTheory.TensorLat
