-- Prove2me | solution 1 for GlobalTheory.HermFrame.ofReal_re_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:09.990471+00:00
-- url     : https://prove2.me/submissions/9698b6a1-e036-449c-8d8e-73d43ebcf5d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution {M : Matrix n n ℂ} (hM : M.IsHermitian) : (M.det.re : ℂ) = M.det := by
  refine conj_eq_iff_re.1 ?_
  rw [← star_def, ← det_conjTranspose, hM.eq]
end GlobalTheory.HermFrame
