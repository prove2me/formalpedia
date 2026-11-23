-- Prove2me | solution 1 for GroundTheory.Global.mixedTraceForm_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:55.720289+00:00
-- url     : https://prove2.me/submissions/a499c0ff-208c-4d95-b48e-30b378d52a42

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_apply

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
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTraceForm K y x := by
  rw [mixedTraceForm_apply, mixedTraceForm_apply, mul_comm]
end GroundTheory.Global
