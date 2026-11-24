-- Prove2me | solution 1 for GlobalTheory.differentiableAt_det_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:48.724435+00:00
-- url     : https://prove2.me/submissions/816b0f4e-e1de-44fd-97cd-94f09cbe2cd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableOnCoordOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology
namespace GlobalTheory
theorem _root_.solution {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype I] [DecidableEq I] (A : E → Matrix I I ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun e => A e i j) x) :
    DifferentiableAt ℂ (fun e => (A e).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact (HasFDerivAt.finset_prod (fun i _ => (h (σ i) i).hasFDerivAt)).differentiableAt
end GlobalTheory
