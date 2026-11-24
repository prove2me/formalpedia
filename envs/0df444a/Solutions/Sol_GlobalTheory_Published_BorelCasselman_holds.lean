-- Prove2me | solution 1 for GlobalTheory.Published.BorelCasselman_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:06.136362+00:00
-- url     : https://prove2.me/submissions/47a17dc6-348f-4ae0-ba95-7f1105654457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelCasselmanHolds
import Theorems.Thm_GlobalTheory_IwahoriInj_iwahoriProj_injective
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_iwahoriProj_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Published
namespace GlobalTheory.Published
theorem _root_.solution : GlobalTheory.Published.BorelCasselman :=
  fun k _ _ _ _ n _ _ _ V _ _ π hπ =>
    ⟨GlobalTheory.IwahoriInj.iwahoriProj_injective k n V π hπ.1,
      GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective k n V π hπ⟩
end GlobalTheory.Published
