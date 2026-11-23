-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerPairingRight_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:38.717731+00:00
-- url     : https://prove2.me/submissions/18094b72-65fe-413b-8078-f6692bb9dd1e

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
theorem _root_.solution (x : kummerGroup K n L) (σ : Gal(L/K)) :
    kummerPairingRight K n L x σ = kummerPairing K n L σ x := rfl
end GroundTheory.ProfCoh
