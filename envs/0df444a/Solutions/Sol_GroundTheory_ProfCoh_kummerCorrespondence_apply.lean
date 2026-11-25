-- Prove2me | solution 1 for GroundTheory.ProfCoh.kummerCorrespondence_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:50:18.345826+00:00
-- url     : https://prove2.me/submissions/0dc07cff-5f9b-45b3-b78f-1bed26c17fc5

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
theorem _root_.solution [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    (kummerCorrespondence K n Ω Δ : IntermediateField K Ω) = kummerField K n Ω Δ := rfl
end GroundTheory.ProfCoh
