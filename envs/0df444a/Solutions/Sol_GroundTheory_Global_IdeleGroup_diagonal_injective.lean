-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.diagonal_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:31.451385+00:00
-- url     : https://prove2.me/submissions/7cc44328-db4a-4b4c-90cb-1cbfc3b68287

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : Function.Injective (diagonal K) := by
  intro x y h
  ext
  exact AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Units.val h)
end GroundTheory.Global.IdeleGroup
