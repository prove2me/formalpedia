-- Prove2me | solution 1 for GlobalTheory.T.idempotent_decomposition_of_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:32.891798+00:00
-- url     : https://prove2.me/submissions/fb4246ad-789e-42d4-baae-fe96459dbd61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegrality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Theorems.Thm_GlobalTheory_IntegralPi_main
import Theorems.Thm_GlobalTheory_JR_Et_Idem_main


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  first | exact @GlobalTheory.JR.Et.Idem.main | exact GlobalTheory.JR.Et.Idem.main | (intros; apply GlobalTheory.JR.Et.Idem.main <;> assumption)
end _root_.GlobalTheory.T
