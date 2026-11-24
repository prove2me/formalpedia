-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.mk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:08.978532+00:00
-- url     : https://prove2.me/submissions/e628da3d-78e0-4e3f-a869-15fef3243208

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
open GroundTheory.ProfCoh.QZ
namespace GroundTheory.ProfCoh.QZ
theorem _root_.solution : Function.Surjective mk := fun x =>
  QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (toAddCircle x)
end GroundTheory.ProfCoh.QZ
