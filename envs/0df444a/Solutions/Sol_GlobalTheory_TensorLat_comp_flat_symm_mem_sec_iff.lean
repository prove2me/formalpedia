-- Prove2me | solution 1 for GlobalTheory.TensorLat.comp_flat_symm_mem_sec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:38.03898+00:00
-- url     : https://prove2.me/submissions/89198e5d-40aa-4f92-8053-90168096eb48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_HC_flat_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : PT E) (Y : GT (Fin n × Idx X.dim))
    (hY : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) (q : ℕ)
    (hka : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) →
      Y.ka (flat γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ q)
    (F : (Fin n → Vsp X.dim) → ℂ) : F ∘ flat.symm ∈ Y.Sec q ↔ F ∈ X.Sec q n := by
  constructor
  · intro hG
    refine ⟨?_, ?_⟩
    · have h := hG.1.comp (flat (n := n) (ι := Idx X.dim)).differentiable
      simpa [Function.comp_def] using h
    · intro γ hγ v
      have h := hG.2 (flat γ) ((hY γ).2 hγ) (flat v)
      simp only [Function.comp, ← map_add, ContinuousLinearEquiv.symm_apply_apply, hka γ hγ,
        Hf_flat] at h
      exact h
  · intro hF
    refine ⟨hF.1.comp (flat (n := n) (ι := Idx X.dim)).symm.differentiable, ?_⟩
    intro γ' hγ' w
    have hγ : ∀ k, flat.symm γ' k ∈ X.L := by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
      exact hγ'
    have h := hF.2 _ hγ (flat.symm w)
    have hk := hka _ hγ
    rw [ContinuousLinearEquiv.apply_symm_apply] at hk
    simp only [Function.comp, map_add, hk]
    rw [h, HC_flat_symm, HC_flat_symm]
end GlobalTheory.TensorLat
