-- Prove2me | solution 1 for GroundTheory.Automorphic.IsSubquotient.of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:35.930543+00:00
-- url     : https://prove2.me/submissions/e565bc90-b8ca-4167-a389-5744a450f61b

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
theorem _root_.solution (q : Representation.IntertwiningMap ρ π) (hq : Surjective q) :
    IsSubquotient π ρ :=
  .of_injective_of_surjective (Representation.IntertwiningMap.id ρ) injective_id q hq
end IsSubquotient
end GroundTheory.Automorphic
