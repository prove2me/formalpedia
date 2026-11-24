-- Prove2me | solution 1 for GlobalTheory.StabGen.subset_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.616806+00:00
-- url     : https://prove2.me/submissions/2ff1c0ea-824c-4bc6-8f54-5a80961ad4c2

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.StabGen
open GlobalTheory.TensHead
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.StabGen
theorem _root_.solution (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx
end GlobalTheory.StabGen
