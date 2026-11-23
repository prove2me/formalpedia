-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:29.939903+00:00
-- url     : https://prove2.me/submissions/2393c0b5-5774-405b-97d4-8dc84c190973

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
omit [CharP k p]
include hp
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he
end GroundTheory.PAdicHodge.SemilinearResidue
