-- Prove2me | solution 1 for GlobalTheory.TopForm.forms_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:35.376893+00:00
-- url     : https://prove2.me/submissions/615c5914-41c4-4570-8342-32c8c771b7bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_span_dForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module B M] {ρ : A →+* B}
    {φ ψ : Forms α D →ₛₗ[ρ] M} (h : ∀ f, φ (dForm α f) = ψ (dForm α f)) : φ = ψ :=
  LinearMap.ext_on_range (span_dForm α D) h
end GlobalTheory.TopForm
