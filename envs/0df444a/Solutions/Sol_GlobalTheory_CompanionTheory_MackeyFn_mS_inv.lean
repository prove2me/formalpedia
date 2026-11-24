-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MackeyFn.mS_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:35.294254+00:00
-- url     : https://prove2.me/submissions/80f77a71-7ae9-4156-9f78-e31b342d4e17

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_conj_mem_iff
import Theorems.Thm_ReciprocityTheory_Ty_Fin_mem_cj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.MackeyFn
theorem _root_.solution {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    {β α : Γ} (x : Γ) (hβ : β ∈ B) (hα : α ∈ A) :
    mS A B a b (β * x * α) = mS A B a b x := by
  classical
  unfold mS
  refine Fintype.sum_equiv (MulAut.conj α).toEquiv _ _ fun h => ?_
  have he : (MulAut.conj α).toEquiv h = α * h * α⁻¹ := rfl
  rw [he]
  have hk : (β * x * α) * h * (β * x * α)⁻¹ = β * (x * (α * h * α⁻¹) * x⁻¹) * β⁻¹ := by group
  have hmem : h ∈ (A ⊓ cj (β * x * α) B : Subgroup Γ) ↔
      α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ) := by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj, hk, conj_mem_iff B hβ,
      conj_mem_iff A hα]
  by_cases hm : α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ)
  · have hx2 : x * (α * h * α⁻¹) * x⁻¹ ∈ B := hm.2
    rw [if_pos hm, if_pos (hmem.2 hm), hk, hB β hβ _ hx2]
    have hinv : (α * h * α⁻¹)⁻¹ = α * h⁻¹ * α⁻¹ := by group
    have hhA : h ∈ A := (conj_mem_iff A hα).1 hm.1
    rw [hinv, hA α hα _ (A.inv_mem hhA)]
  · rw [if_neg hm, if_neg (fun q => hm (hmem.1 q))]
end GlobalTheory.CompanionTheory.MackeyFn
