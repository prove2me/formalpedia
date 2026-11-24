-- Prove2me | solution 1 for GlobalTheory.FinsetKernelTrivial.restr_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:20.813774+00:00
-- url     : https://prove2.me/submissions/32e7f746-2734-4b64-bbc0-fe999e6c40aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetKerEqBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinsetKernelTrivial
open scoped BigOperators
namespace GlobalTheory.FinsetKernelTrivial
theorem _root_.solution {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl
end GlobalTheory.FinsetKernelTrivial
