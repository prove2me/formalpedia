-- Prove2me | solution 1 for GlobalTheory.T.exists_etaleHermitianPair_isGen_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:49.141401+00:00
-- url     : https://prove2.me/submissions/ce57d6dd-2f10-4d02-ab95-d18d35211ecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanionStatement
import Theorems.Thm_GlobalTheory_JR_exists_et_isGen_companion


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F), (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  first | exact @GlobalTheory.JR.exists_et_isGen_companion | exact GlobalTheory.JR.exists_et_isGen_companion | (intros; apply GlobalTheory.JR.exists_et_isGen_companion <;> assumption)
end _root_.GlobalTheory.T
