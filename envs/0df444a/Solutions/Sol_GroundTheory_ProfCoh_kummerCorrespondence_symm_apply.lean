-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerCorrespondence_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:47.698916+00:00
-- url     : https://prove2.me/submissions/cf35ef75-0ef3-411c-95d2-e3210439faf2

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution [IsSepClosed Ω]
    (E : {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n}) :
    (kummerCorrespondence K n Ω).symm E = kummerGroup K n E.1 := rfl
end GroundTheory.ProfCoh
