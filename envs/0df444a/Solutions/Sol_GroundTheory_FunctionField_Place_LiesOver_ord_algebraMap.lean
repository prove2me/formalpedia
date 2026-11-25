-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.LiesOver.ord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:16.176623+00:00
-- url     : https://prove2.me/submissions/30791d33-de91-4423-a0fc-61b50b0e910a

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_valuation_algebraMap
import Theorems.Thm_P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']
namespace GroundTheory.FunctionField.Place
namespace LiesOver
theorem _root_.solution {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    w.ord (algebraMap K K' x) = w.ramificationIdx v * v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  let := h.algebra
  have h1 := h.valuation_algebraMap x
  have hx' : algebraMap K K' x ≠ 0 := (map_ne_zero _).2 hx
  rw [v.valuation_eq_exp_neg_ord hx, w.valuation_eq_exp_neg_ord hx', ← WithZero.exp_nsmul,
    WithZero.exp_inj, nsmul_eq_mul, h.ramificationIdx'_eq] at h1
  linarith
end LiesOver
end GroundTheory.FunctionField.Place
