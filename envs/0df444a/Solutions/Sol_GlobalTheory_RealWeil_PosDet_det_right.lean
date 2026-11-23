-- Prove2me | solution 1 for GlobalTheory.RealWeil.PosDet.det_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:23.522797+00:00
-- url     : https://prove2.me/submissions/7fea1df2-58ae-4eac-88c4-67abf3c632f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf

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
theorem _root_.solution {p : Matrix ι ι ℂ} (pp : p * p = p) (g : Matrix ι ι ℂ) :
    (g * p + (1 - p)).det = (p * g * p + (1 - p)).det := by
  have pp' : ∀ x, p * (p * x) = p * x := fun x => by rw [← mul_assoc, pp]
  have e : g * p + (1 - p) = (p * g * p + (1 - p)) * (1 + ((1 - p) * g) * p) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, pp, pp', one_mul, mul_one]; abel
  have e2 : p * ((1 - p) * g) = 0 := by
    simp only [mul_sub, sub_mul, pp', one_mul, sub_self]
  rw [e, det_mul, det_one_add_mul_comm, e2, add_zero, det_one, mul_one]
end GlobalTheory.RealWeil.PosDet
