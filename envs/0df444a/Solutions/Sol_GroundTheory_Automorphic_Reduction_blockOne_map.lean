-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.blockOne_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:50.252135+00:00
-- url     : https://prove2.me/submissions/cd3f56c3-1b8a-432c-a0ca-f2031c725aed

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction
variable {R : Type*} [CommRing R] {m : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin m) R) :
    (blockOne M).map f = blockOne (M.map f) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp
end GroundTheory.Automorphic.Reduction
