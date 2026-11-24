-- Prove2me | solution 1 for GlobalTheory.JR.UnitGLift.norm_eL_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:47.995001+00:00
-- url     : https://prove2.me/submissions/69a7b338-7912-45ce-9637-6920464a4c5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitGLift
namespace GlobalTheory.JR.UnitGLift
theorem _root_.solution {F : Type} [NormedField F] {r : ℕ} (i : Fin (r + 1)) :
    ‖GlobalTheory.JR.Step.eL r F i‖ ≤ 1 := by
  unfold GlobalTheory.JR.Step.eL
  by_cases h : i = Fin.last r
  · subst h; simp
  · simp [Pi.single_apply, h]
end GlobalTheory.JR.UnitGLift
