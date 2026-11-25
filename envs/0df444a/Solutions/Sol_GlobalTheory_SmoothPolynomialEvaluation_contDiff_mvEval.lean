-- Prove2me | solution 1 for GlobalTheory.SmoothPolynomialEvaluation.contDiff_mvEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:40.048865+00:00
-- url     : https://prove2.me/submissions/ac0b90bf-45ac-48a1-9750-049725d0a64e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SmoothPolynomialEvaluation
namespace GlobalTheory.SmoothPolynomialEvaluation
theorem _root_.solution {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => MvPolynomial.eval v.1 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    have hX : ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => v.1 i) := (contDiff_apply ℂ ℂ i).comp contDiff_fst
    simpa using hp.mul hX
end GlobalTheory.SmoothPolynomialEvaluation
