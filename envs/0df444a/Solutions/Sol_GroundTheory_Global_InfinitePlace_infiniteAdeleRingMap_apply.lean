-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:07.01241+00:00
-- url     : https://prove2.me/submissions/bd78c424-6b69-4b74-b9ec-13907948452c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
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
theorem _root_.solution (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleRingMap x w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := rfl
end GroundTheory.Global.InfinitePlace
