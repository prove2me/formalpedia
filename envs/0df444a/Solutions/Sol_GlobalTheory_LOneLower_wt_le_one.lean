-- Prove2me | solution 1 for GlobalTheory.LOneLower.wt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:11.659449+00:00
-- url     : https://prove2.me/submissions/a613e413-363e-4647-8a9d-f4be80f3f749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {x : ℝ} (hx : 0 < x) : wt x ≤ 1 := by
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos x
  have h5 : 0 < Real.exp x - 1 := by linarith
  unfold wt
  rw [inv_sub_inv hx.ne' h5.ne', div_le_one (by positivity)]
  nlinarith
end GlobalTheory.LOneLower
