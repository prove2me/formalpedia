-- Prove2me | solution 1 for GroundTheory.Global.orbitPoint_orbitPoint
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:28:33.089474+00:00
-- url     : https://prove2.me/submissions/a609ad2f-44b9-4bf0-ac13-ce3717dce170

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}


theorem solution (x : X) : orbitPoint G (orbitPoint G x) = orbitPoint G x := by
  unfold orbitPoint; rw [Quotient.out_eq]
