-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.coe_diagHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:12.1408+00:00
-- url     : https://prove2.me/submissions/21da5d25-1fc9-464f-974c-e7c2d6bdb7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution (t : Fin n → Circle) :
    (diagHom n t : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (t i : ℂ) := rfl
end GlobalTheory.UnitaryChar
