-- Prove2me | solution 1 for GlobalTheory.T.absK_multiplicative_unitOne_haarScaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:18.593802+00:00
-- url     : https://prove2.me/submissions/52a38ffe-0421-4848-b100-d021fd858109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScalingStatement
import Theorems.Thm_GlobalTheory_JR_Et_absK_facts


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  first | exact @GlobalTheory.JR.Et.absK_facts | exact GlobalTheory.JR.Et.absK_facts | (intros; apply GlobalTheory.JR.Et.absK_facts <;> assumption)
end _root_.GlobalTheory.T
