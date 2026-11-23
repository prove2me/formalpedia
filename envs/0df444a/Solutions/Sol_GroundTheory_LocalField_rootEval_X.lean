-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:09.718721+00:00
-- url     : https://prove2.me/submissions/1fc7133d-7000-4492-9b65-7ff8c787e70f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_rootEval_coe

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
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)
namespace GroundTheory.LocalField
theorem _root_.solution : rootEval hP X = AdjoinRoot.root P := by
  rw [← Polynomial.coe_X, rootEval_coe]
  rfl
end GroundTheory.LocalField
