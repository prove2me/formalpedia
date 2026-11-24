-- Prove2me | solution 1 for GlobalTheory.HCA.dw_hasCompactSupport_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:32.54622+00:00
-- url     : https://prove2.me/submissions/acbe62f8-abe5-456a-97b9-0c3b6e2638b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} (w : List (Fin d)) {f : E d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (dw w f) ∧ tsupport (dw w f) ⊆ tsupport f := by
  induction w with
  | nil => exact ⟨hf, subset_rfl⟩
  | cons j w ih =>
    refine ⟨ih.1.fderiv_apply (𝕜 := ℝ) (ev j), ?_⟩
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := dw w f) (ev j)).trans ih.2
end GlobalTheory.HCA
