-- Prove2me | solution 1 for GlobalTheory.JR.exists_et_isGen_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:33:27.351747+00:00
-- url     : https://prove2.me/submissions/a99e63fe-8b8a-44ac-90db-413be5ead65a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanion
import Theorems.Thm_GlobalTheory_JR_charpoly_companion
import Theorems.Thm_GlobalTheory_JR_EtExist_exists_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  intro F E _ _ _ _ _ r p hs
  rw [charpoly_companion] at hs
  exact EtExist.exists_isGen F E r p hs
end GlobalTheory.JR
