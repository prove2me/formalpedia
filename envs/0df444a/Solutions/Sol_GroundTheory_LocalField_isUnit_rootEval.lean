-- Prove2me | solution 1 for GroundTheory.LocalField.isUnit_rootEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:46.437593+00:00
-- url     : https://prove2.me/submissions/153a3a1b-d7b1-4b7d-b3f0-5d6268cd38e8

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
theorem _root_.solution {G : B⟦X⟧} (hG : IsUnit (constantCoeff G)) :
    IsUnit (rootEval hP G) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hG).map _
end GroundTheory.LocalField
