-- Prove2me | solution 1 for GlobalTheory.DPEval2.ex_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:42.624083+00:00
-- url     : https://prove2.me/submissions/8db9baad-e433-4c3a-a28a-0544c8d258f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DPEval2
namespace GlobalTheory.DPEval2
theorem _root_.solution (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel
end GlobalTheory.DPEval2
