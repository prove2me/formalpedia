-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:35.152911+00:00
-- url     : https://prove2.me/submissions/5a4803eb-0437-441e-abad-06487fbda92e

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
theorem _root_.solution {G : B⟦X⟧} (hG : constantCoeff G = 0) (p : Polynomial B) :
    rootEval hP (subst G (p : B⟦X⟧)) = Polynomial.aeval (rootEval hP G) p := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' hG), Polynomial.aeval_algHom_apply]
end GroundTheory.LocalField
