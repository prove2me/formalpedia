-- Prove2me | solution 1 for GlobalTheory.T.test_function_locally_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:24.99297+00:00
-- url     : https://prove2.me/submissions/7c602255-095c-4f63-b20a-bfbdb328ae61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TestFunctionLocallyInvariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TestFunctionLocallyInvariantStatement
import Theorems.Thm_GlobalTheory_RowSmooth_row_smooth


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  first | exact @GlobalTheory.RowSmooth.row_smooth | exact GlobalTheory.RowSmooth.row_smooth | (intros; apply GlobalTheory.RowSmooth.row_smooth <;> assumption)
end _root_.GlobalTheory.T
