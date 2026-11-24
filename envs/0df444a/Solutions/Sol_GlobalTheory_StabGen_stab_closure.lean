-- Prove2me | solution 1 for GlobalTheory.StabGen.stab_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.000822+00:00
-- url     : https://prove2.me/submissions/0c328824-b54e-49e3-a183-44c6a5ab32b1

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
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)
end GlobalTheory.StabGen
