-- Prove2me | solution 1 for GlobalTheory.RealWeil.PosDet.det_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:55.147518+00:00
-- url     : https://prove2.me/submissions/33dc62ee-34f7-42b5-ac0d-42208cd0bb7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_det_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.PosDet
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RealWeil.PosDet
theorem _root_.solution {p : Matrix ι ι ℂ} (pp : p * p = p) {g h : Matrix ι ι ℂ} (hg : h * g = 1) :
    (p + (1 - p) * g * (1 - p)).det = (p * h + (1 - p)).det * g.det := by
  have qq : (1 - p) * (1 - p) = 1 - p := by
    simp only [mul_sub, sub_mul, pp, one_mul, mul_one]; abel
  have := det_left qq g
  rw [sub_sub_cancel] at this
  rw [add_comm p, ← this, ← det_mul, add_mul, mul_assoc p, hg, mul_one, add_comm]
end GlobalTheory.RealWeil.PosDet
