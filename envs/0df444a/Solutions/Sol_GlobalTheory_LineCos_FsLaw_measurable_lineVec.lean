-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.measurable_lineVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:47.638865+00:00
-- url     : https://prove2.me/submissions/09184e9f-9a21-4334-8cb6-8fd281a682bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution (s : Bool) (i : Fin 2) : Measurable fun x : ℂ => lineVec s x i := by
  cases s
  · fin_cases i
    · exact measurable_const
    · exact measurable_id
  · fin_cases i
    · exact measurable_id
    · exact measurable_const
end GlobalTheory.LineCos.FsLaw
