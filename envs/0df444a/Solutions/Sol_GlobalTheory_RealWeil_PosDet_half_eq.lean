-- Prove2me | solution 1 for GlobalTheory.RealWeil.PosDet.half_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:55.843888+00:00
-- url     : https://prove2.me/submissions/aa1b9bf8-ec74-43e4-8bcd-3ed44d8bb7a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_half_add_self

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
    (1 / 2 : ℂ) • (1 + (p - (1 - p)) * h * (p - (1 - p)) * g) =
      (p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)) := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have hg' : ∀ x, h * (g * x) = x := fun x => by rw [← mul_assoc, hg, one_mul]
  rw [← half_add_self ((p - (1 - p)) * h * (p * g * p - (1 - p) * g * (1 - p)))]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc, pp, hg, hg', one_mul, mul_one]; abel
end GlobalTheory.RealWeil.PosDet
