-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:03.775164+00:00
-- url     : https://prove2.me/submissions/cb45b8b8-5a94-4bbc-a890-d04a81f82c6b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval

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
theorem _root_.solution (p : Polynomial B) : rootEval hP (p : B⟦X⟧) = AdjoinRoot.mk P p := by
  apply hP.algEquivQuotient.injective
  change hP.algEquivQuotient (hP.algEquivQuotient.symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl
end GroundTheory.LocalField
