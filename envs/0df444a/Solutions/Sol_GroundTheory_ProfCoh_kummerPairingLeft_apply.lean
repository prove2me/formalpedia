-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerPairingLeft_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:38.531958+00:00
-- url     : https://prove2.me/submissions/937faaa2-34f0-4a58-a304-d3387afbad3f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}
variable (K n L)
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairingLeft K n L σ x = kummerPairing K n L σ x := rfl
end GroundTheory.ProfCoh
