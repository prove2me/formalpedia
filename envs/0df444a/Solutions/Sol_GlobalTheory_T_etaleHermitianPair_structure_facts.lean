-- Prove2me | solution 1 for GlobalTheory.T.etaleHermitianPair_structure_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:33.849792+00:00
-- url     : https://prove2.me/submissions/c1ed96e0-bbf8-4472-b015-847d1afe680e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFacts
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Theorems.Thm_GlobalTheory_JR_EtFacts_main


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  first | exact @GlobalTheory.JR.EtFacts.main | exact GlobalTheory.JR.EtFacts.main | (intros; apply GlobalTheory.JR.EtFacts.main <;> assumption)
end _root_.GlobalTheory.T
