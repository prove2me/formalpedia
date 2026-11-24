-- Prove2me | solution 1 for GlobalTheory.T.partialFourierGLBlock_unitIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:12.473984+00:00
-- url     : https://prove2.me/submissions/57964bb6-2109-4de4-a8f4-859836d52152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicatorStatement
import Theorems.Thm_GlobalTheory_JR_fourG_unitG


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → fourG M ψ (unitG r F) = unitG r F := by
  first | exact @GlobalTheory.JR.fourG_unitG | exact GlobalTheory.JR.fourG_unitG | (intros; apply GlobalTheory.JR.fourG_unitG <;> assumption)
end _root_.GlobalTheory.T
