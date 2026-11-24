-- Prove2me | solution 1 for GlobalTheory.Descent.linearIndependent_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:03.77398+00:00
-- url     : https://prove2.me/submissions/95014872-49bc-4b36-b944-b5ccc007e832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory.Descent
theorem _root_.solution {ι : Type*} (v : ι → M) :
    LinearIndependent A v ↔ LinearIndependent A' fun i ↦ (1 : A') ⊗ₜ[A] v i := by
  refine ⟨fun h ↦ Module.Flat.linearIndependent_one_tmul h, fun h ↦ ?_⟩
  have h' : LinearIndependent A fun i ↦ (1 : A') ⊗ₜ[A] v i :=
    h.restrict_scalars' A
  exact LinearIndependent.of_comp (TensorProduct.mk A A' M 1) h'
end GlobalTheory.Descent
