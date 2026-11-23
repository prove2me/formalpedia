-- Prove2me | solution 1 for GroundTheory.Global.norm_algebraMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.856123+00:00
-- url     : https://prove2.me/submissions/83fb85d3-cda2-4ed1-b30f-27cf1ad76195

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice

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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (k : K) (w : InfinitePlace K) :
    ‖algebraMap K K∞ k w‖ = w k := by
  simp [InfiniteAdeleRing.algebraMap_apply, WithAbs.norm_toAbs_eq]
  rfl
end GroundTheory.Global
