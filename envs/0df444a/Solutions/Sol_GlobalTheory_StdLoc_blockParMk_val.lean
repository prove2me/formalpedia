-- Prove2me | solution 1 for GlobalTheory.StdLoc.blockParMk_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:14.104927+00:00
-- url     : https://prove2.me/submissions/38a1304b-0cf7-470e-8cf7-aff6d2ee67fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.StdLoc
namespace GlobalTheory.StdLoc
theorem _root_.solution {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) :
    ((blockParMk x).1 : Matrix (Fin (a + b)) (Fin (a + b)) R) = blockMat x.1.1 x.2.2 x.2.1.1 := rfl
end GlobalTheory.StdLoc
