-- Prove2me | solution 1 for GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:10.680979+00:00
-- url     : https://prove2.me/submissions/d9dac720-5a0b-4e7c-aea0-1a37fddbd92f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOKStatement
import Theorems.Thm_GlobalTheory_JR_OKCompact_okCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  first | exact @GlobalTheory.JR.OKCompact.okCompact | exact GlobalTheory.JR.OKCompact.okCompact | (intros; apply GlobalTheory.JR.OKCompact.okCompact <;> assumption)
end _root_.GlobalTheory.T
