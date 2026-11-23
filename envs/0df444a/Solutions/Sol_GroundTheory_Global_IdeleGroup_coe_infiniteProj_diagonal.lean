-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:51.092404+00:00
-- url     : https://prove2.me/submissions/3fea4c05-0ddc-40a7-b1e0-6f33ea3fd96c

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
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) (x : Kˣ) :
    ((infiniteProj w (diagonal K x) : (w.Completion)ˣ) : w.Completion) =
      ((x : K) : w.Completion) :=
  rfl
end GroundTheory.Global.IdeleGroup
