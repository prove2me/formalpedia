-- Prove2me | solution 1 for GroundTheory.Global.mapComplexCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.74432+00:00
-- url     : https://prove2.me/submissions/860c61c9-ec4a-423e-a87a-34a9c2cad664

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier

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
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (a : ℂ ≃L[ℝ] ℂ) (x : mixedSpace K) :
    mapComplexCoord K a x = (x.1, fun w => a (x.2 w)) := rfl
end GroundTheory.Global
