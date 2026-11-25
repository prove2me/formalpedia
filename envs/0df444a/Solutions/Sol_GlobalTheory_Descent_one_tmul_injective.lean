-- Prove2me | solution 1 for GlobalTheory.Descent.one_tmul_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:34.673044+00:00
-- url     : https://prove2.me/submissions/3ead5220-2984-4403-9fb5-0bb664e18183

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
theorem _root_.solution : Function.Injective fun m : M ↦ (1 : A') ⊗ₜ[A] m :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := A') M
end GlobalTheory.Descent
