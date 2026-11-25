-- Prove2me | solution 1 for GlobalTheory.PDivGroup.transl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:38.578182+00:00
-- url     : https://prove2.me/submissions/a01b4589-ecbd-4e15-ab36-0011e261b2d0

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
theorem _root_.solution (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl
end GlobalTheory.PDivGroup
