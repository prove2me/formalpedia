-- Prove2me | solution 1 for GlobalTheory.T.partialFourierHermitianBlock_unitIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:13.23015+00:00
-- url     : https://prove2.me/submissions/22050c69-f5e4-4cc4-97ca-fec39ddb3c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicatorStatement
import Theorems.Thm_GlobalTheory_JR_FourUnit_fourU_unitU


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → (∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) → fourU M ψ (unitU r F E) = unitU r F E := by
  first | exact @GlobalTheory.JR.FourUnit.fourU_unitU | exact GlobalTheory.JR.FourUnit.fourU_unitU | (intros; apply GlobalTheory.JR.FourUnit.fourU_unitU <;> assumption)
end _root_.GlobalTheory.T
