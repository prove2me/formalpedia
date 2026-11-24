-- Prove2me | solution 1 for GlobalTheory.TopForm.span_dForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:55.322825+00:00
-- url     : https://prove2.me/submissions/42cc839b-7469-4063-8456-2870742ad628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange

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
theorem _root_.solution (α : k →+* A) (D : ℕ) :
    Submodule.span A (Set.range (dForm α (D := D))) = ⊤ := by
  letI := α.toAlgebra
  rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span A D (Omega α)
    (KaehlerDifferential.span_range_derivation k A)]
  refine Submodule.span_mono ?_
  rintro _ ⟨w, hw, rfl⟩
  choose v hv using fun i => hw (Set.mem_range_self i)
  exact ⟨v, congrArg (exteriorPower.ιMulti A D) (funext hv)⟩
end GlobalTheory.TopForm
