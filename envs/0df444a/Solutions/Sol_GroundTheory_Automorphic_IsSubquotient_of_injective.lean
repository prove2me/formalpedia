-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:05.486497+00:00
-- url     : https://prove2.me/submissions/580aad59-d691-4e73-9c5f-c4f555abf574

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_IsSubquotient_of_injective_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
namespace GroundTheory.Automorphic
namespace IsSubquotient
theorem _root_.solution (i : Representation.IntertwiningMap π ρ) (hi : Injective i) :
    IsSubquotient π ρ :=
  .of_injective_of_surjective i hi (Representation.IntertwiningMap.id π) surjective_id
end IsSubquotient
end GroundTheory.Automorphic
