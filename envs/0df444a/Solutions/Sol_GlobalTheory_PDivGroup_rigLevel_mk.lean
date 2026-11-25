-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigLevel_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:34.699777+00:00
-- url     : https://prove2.me/submissions/a964b56d-a42c-4b3e-8c26-c0216d0c288c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero

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
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) (c : G.cocycles) (w : G.omega) :
    G.rigLevel n (G.rigMk (c, w)) = Submodule.Quotient.mk (⟨c.1 n, (c.2 n).1⟩, w.1 n) := rfl
end GlobalTheory.PDivGroup
