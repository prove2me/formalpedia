-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerGroupEquivDual_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:38.674556+00:00
-- url     : https://prove2.me/submissions/1120fba2-4315-4b6d-9981-2380897d48db

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite

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
theorem _root_.solution [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) (x : kummerGroup K n L)
    (σ : Gal(L/K)) : kummerGroupEquivDual K n L hexp x σ = kummerPairing K n L σ x := rfl
end GroundTheory.ProfCoh
