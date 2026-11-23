-- Prove2me | solution 1 for IsLocallyConstant.eq_of_eqOn_dense
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:05.705029+00:00
-- url     : https://prove2.me/submissions/f8de4c6f-5831-4fb2-88d4-5dc6448a609d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs

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
variable {G : Type*} [Group G] [TopologicalSpace G]
namespace GroundTheory.ProfCoh
namespace _root_.IsLocallyConstant
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {s : Set X} (hs : Dense s)
    (h : Set.EqOn f g s) : f = g := by
  let _ : TopologicalSpace Y := ⊥
  have : DiscreteTopology Y := ⟨rfl⟩
  exact Continuous.ext_on hs hf.continuous hg.continuous h
end _root_.IsLocallyConstant
end GroundTheory.ProfCoh
