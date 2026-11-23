-- Prove2me | solution 1 for GroundTheory.GroupCoh.hasHerbrandQuotient_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:37.127726+00:00
-- url     : https://prove2.me/submissions/c3ea532c-df74-46d3-920b-54282b6721c2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Finite A] (f g : A →+ A) : HasHerbrandQuotient f g :=
  ⟨inferInstance, inferInstance⟩
end GroundTheory.GroupCoh
