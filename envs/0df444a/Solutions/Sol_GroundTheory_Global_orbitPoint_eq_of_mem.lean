-- Prove2me | solution 1 for GroundTheory.Global.orbitPoint_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:30.330034+00:00
-- url     : https://prove2.me/submissions/7d0da799-1ce8-4845-b79f-9923faced0d1

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
namespace GroundTheory.Global
theorem _root_.solution {x y : X} (h : y ∈ orbit G x) : orbitPoint G y = orbitPoint G x := by
  unfold orbitPoint
  rw [Quotient.sound (orbitRel_apply.2 h)]
end GroundTheory.Global
