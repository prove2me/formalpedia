-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:01.745296+00:00
-- url     : https://prove2.me/submissions/6e33fe29-0df0-4a16-9f38-f4d77d392d4e

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
theorem _root_.solution :
    Continuous (infiniteAdeleRingMap (K := K) (L := L)) :=
  continuous_pi fun w =>
    (NumberField.LiesOver.continuous_completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (continuous_apply (w.comap (algebraMap K L)))
end GroundTheory.Global.InfinitePlace
