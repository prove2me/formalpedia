-- Prove2me | solution 1 for GlobalTheory.TopForm.formMap_formMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:42.722192+00:00
-- url     : https://prove2.me/submissions/53b515de-7ee5-4507-9ee6-c038ffc970af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_TopForm_forms_ext
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.TopForm.formMap_dForm

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
theorem _root_.solution (ρ : A →+* B) (σ : B →+* C) (τ : A →+* C) (e : σ.comp ρ = τ)
    (h : ρ.comp α = β) (h' : σ.comp β = γ) (h'' : τ.comp α = γ) (x : Forms α D) :
    formMap D σ h' (formMap D ρ h x) = formMap D τ h'' x := by
  haveI : RingHomCompTriple ρ σ τ := ⟨e⟩
  refine LinearMap.congr_fun (forms_ext (φ := (formMap D σ h').comp (formMap D ρ h))
    (ψ := formMap D τ h'') fun f => ?_) x
  rw [LinearMap.comp_apply, formMap_dForm, formMap_dForm, formMap_dForm, ← e]
  rfl
end GlobalTheory.TopForm
