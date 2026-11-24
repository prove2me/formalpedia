-- Prove2me | solution 1 for GlobalTheory.Descent.algebraMap_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:23.200814+00:00
-- url     : https://prove2.me/submissions/718762ee-b8e9-4ade-96c9-f152f49f2629

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
theorem _root_.solution (a b : A) : algebraMap A A' a ∣ algebraMap A A' b ↔ a ∣ b := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := A') (Ideal.span {a}), Ideal.mem_comap,
    Ideal.map_span, Set.image_singleton]
end GlobalTheory.Descent
