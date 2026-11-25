-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.strictMono_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:01.891799+00:00
-- url     : https://prove2.me/submissions/a2ece36f-1757-4b78-a87b-8be50b834ad6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} (hj : StrictMono j) (hs : s < j 0) :
    StrictMono (Fin.cons s j : Fin (n + 2) → ι) := by
  refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
  cases k using Fin.cases with
  | zero => simpa using hs
  | succ k =>
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    exact hj Fin.castSucc_lt_succ
end GroundTheory.Arith.SchemeCoh
