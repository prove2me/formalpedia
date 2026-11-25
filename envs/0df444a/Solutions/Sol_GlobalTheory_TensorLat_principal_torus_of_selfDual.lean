-- Prove2me | solution 1 for GlobalTheory.TensorLat.principal_torus_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:44.74467+00:00
-- url     : https://prove2.me/submissions/4bb9cc51-91b3-498b-8cf7-9ee9cf623829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_translate_comp_flat_symm
import Theorems.Thm_GlobalTheory_TensorLat_l2_comp_flat_symm_eq_l2
import Theorems.Thm_GlobalTheory_TensorLat_comp_flat_symm_mem_sec_iff
import Theorems.Thm_GlobalTheory_TensorLat_tensorEps_sq_of_mem
import Theorems.Thm_GlobalTheory_TensorLat_tensorEps_add_of_mem
import Theorems.Thm_GlobalTheory_TensorLat_HC_flat_symm
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_tensorEps_eq_prod_eps
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
theorem _root_.solution (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1) :
    (∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) ∧
    (∀ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') →
      (∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) →
      (∀ x ∈ lat Y.b, Y.ka x ^ 2 = 1) ∧
      ∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b,
        Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im)) ∧
    ((∀ x ∈ X.L, (X.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im)) →
      ∀ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X (stdLat E n)) →
        (∀ γ, Y.ka (flat γ) = tensorEps w₀ γ) →
        (∀ F, F ∘ flat.symm ∈ Y.Sec 1 ↔ F ∈ X.Sec 1 n) ∧
        ∀ F ∈ X.Sec 1 n, F ∘ flat.symm ∈ Y.Sec 1 ∧ Y.l2 1 (F ∘ flat.symm) = X.l2 1 F) ∧
    (∀ U : ℕ → EuclideanSpace ℂ (Fin n × Idx X.dim) →
        (EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ) → EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ,
      (∀ (q : ℕ) a F v,
        U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)) →
      ∀ (q : ℕ) (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ),
        U q (flat a) (F ∘ flat.symm) = X.U q a F ∘ flat.symm) := by
  refine ⟨exists_tensorTorus hfg hint hdual w₀, ?_, ?_,
    fun U hU q a F => translate_comp_flat_symm X U hU q a F⟩
  · intro Y hY hka
    have hmem : ∀ x, x ∈ lat Y.b ↔ flat.symm x ∈ tensorLat X Λ' := fun x => by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
    have hka' : ∀ x, Y.ka x = tensorEps w₀ (flat.symm x) := fun x => by
      rw [← hka, ContinuousLinearEquiv.apply_symm_apply]
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rw [hka']
      exact tensorEps_sq_of_mem hfg hint hdual w₀ ((hmem x).1 hx)
    · rw [hka', hka', hka', map_add,
        tensorEps_add_of_mem hfg hint hdual w₀ hw ((hmem x).1 hx) ((hmem y).1 hy), HC_flat_symm]
  · intro heps Y hY hka
    have hY' : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L := fun γ => by
      rw [hY, mem_tensorLat_stdLat]
    have hka1 : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) →
        Y.ka (flat γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ 1 := fun γ hγ => by
      rw [pow_one, hka, tensorEps_eq_prod_eps X w₀ heps hγ]
    exact ⟨fun F => comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F, fun F hF =>
      ⟨(comp_flat_symm_mem_sec_iff X Y hY' 1 hka1 F).2 hF, l2_comp_flat_symm_eq_l2 X Y hY' 1 hF⟩⟩
end GlobalTheory.TensorLat
