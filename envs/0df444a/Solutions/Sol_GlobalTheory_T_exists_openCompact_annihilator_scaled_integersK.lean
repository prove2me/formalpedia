-- Prove2me | solution 1 for GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:48.915696+00:00
-- url     : https://prove2.me/submissions/4b748a35-ce95-4c99-b632-0737ba27baf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersKStatement
import Theorems.Thm_GlobalTheory_JR_DualScaledIntegers_exists_open_compact_annihilator


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  first | exact @GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | exact GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | (intros; apply GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator <;> assumption)
end _root_.GlobalTheory.T
