-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:16.228394+00:00
-- url     : https://prove2.me/submissions/d723dbbb-c42f-4d2a-a365-a770519fbd0e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField K] [NumberField L]
omit [NumberField K] [NumberField L]
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (k : K) :
    infiniteAdeleRingMap (algebraMap K (InfiniteAdeleRing K) k) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L k) := by
  funext w
  rw [infiniteAdeleRingMap_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply, ← Completion.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L]
  rfl
end GroundTheory.Global.InfinitePlace
