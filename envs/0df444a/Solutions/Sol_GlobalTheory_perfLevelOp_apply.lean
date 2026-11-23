-- Prove2me | solution 1 for GlobalTheory.perfLevelOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:43.711696+00:00
-- url     : https://prove2.me/submissions/1b27ac83-22a3-47aa-862e-0736c1080655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    perfLevelOp p S Q n w = (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k) :=
  rfl
end GlobalTheory
