-- Prove2me | solution 1 for GlobalTheory.TensorLat.le_mul_norm_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:58.606471+00:00
-- url     : https://prove2.me/submissions/6afdcff8-6c57-426a-91a8-b7a7378c0522

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_GlobalTheory_TensorLat_norm_contr_le
import Theorems.Thm_GlobalTheory_TensorLat_exists_contr_ne_zero
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
open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) {ι : Type*}
    (v : ι → Fin n → E) (hv : ∀ i, v i ∈ Λ') (hspan : Submodule.span E (Set.range v) = ⊤)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlen : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ ρ * ‖flat γ‖ := by
  obtain ⟨i, hi⟩ := exists_contr_ne_zero v hspan h0
  exact (hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))
end GlobalTheory.TensorLat
