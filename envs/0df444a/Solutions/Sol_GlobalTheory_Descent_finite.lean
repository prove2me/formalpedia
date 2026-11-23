-- Prove2me | solution 1 for GlobalTheory.Descent.finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:48.069617+00:00
-- url     : https://prove2.me/submissions/9dabda98-c63f-40ae-b090-c3bc85f34d0e

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
theorem _root_.solution [Module.Finite A' (A' ⊗[A] M)] : Module.Finite A M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A'
end GlobalTheory.Descent
