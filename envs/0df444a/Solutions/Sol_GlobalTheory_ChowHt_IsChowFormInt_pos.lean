-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowFormInt.pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:43.043446+00:00
-- url     : https://prove2.me/submissions/bfd67828-980f-40c2-9ae9-f3f7c71d19b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_isHomogeneous
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
open GlobalTheory.ChowHt.IsChowFormInt
variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
namespace GlobalTheory.ChowHt.IsChowFormInt
theorem _root_.solution (h : IsChowFormInt I e dl f) : 0 < dl := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  have h1 := (isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous
  simp only [Finset.sum_const_zero] at h1
  have h2 := h1.totalDegree_le
  rw [Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at h2
  refine h.irred.not_isUnit ?_
  rw [h2]
  refine (IsUnit.mk0 _ fun h3 => h.ne_zero ?_).map C
  rw [h2, h3, C_0]
end GlobalTheory.ChowHt.IsChowFormInt
