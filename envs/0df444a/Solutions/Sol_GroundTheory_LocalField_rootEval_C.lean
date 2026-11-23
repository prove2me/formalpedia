-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:27.96567+00:00
-- url     : https://prove2.me/submissions/8cc1c784-fb11-4472-9e73-3be6009af3cf

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
theorem _root_.solution (b : B) : rootEval hP (C b) = AdjoinRoot.of P b := by
  rw [← Polynomial.coe_C, rootEval_coe, AdjoinRoot.mk_C]
end GroundTheory.LocalField
