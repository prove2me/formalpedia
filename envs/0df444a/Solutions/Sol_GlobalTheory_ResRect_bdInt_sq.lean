-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:15:33.276372+00:00
-- url     : https://prove2.me/submissions/bea9e8ab-721d-40d1-bbb5-bbca9856ea51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_bdInt_eq_zero_of_primitive
import Theorems.Thm_GlobalTheory_ResRect_sidesIn_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p) ^ 2) = 0 := by
  refine bdInt_eq_zero_of_primitive (sidesIn_compl h1 h2 h3 h4) (F := fun s => -k * (s - p)⁻¹)
    ?_ fun s hs => ?_
  · exact ContinuousOn.div (by fun_prop) (by fun_prop)
      fun s hs => pow_ne_zero _ (sub_ne_zero.2 hs)
  · have hs' : s - p ≠ 0 := sub_ne_zero.2 hs
    have := (((hasDerivAt_id s).sub_const p).inv hs').const_mul (-k)
    refine this.congr_deriv ?_
    simp only [id]
    ring
end GlobalTheory.ResRect
