-- Prove2me | solution 1 for GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:40.015883+00:00
-- url     : https://prove2.me/submissions/b27a5671-039f-4ed8-9787-097148fb3710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyCompanionMatrixEtaleGeneratorSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyCompanionMatrixEtaleGeneratorSeparableStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_charpoly_companion_separable


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → (companion p).charpoly.Separable := by
  first | exact @GlobalTheory.JR.LinDesc.charpoly_companion_separable | exact GlobalTheory.JR.LinDesc.charpoly_companion_separable | (intros; apply GlobalTheory.JR.LinDesc.charpoly_companion_separable <;> assumption)
end _root_.GlobalTheory.T
