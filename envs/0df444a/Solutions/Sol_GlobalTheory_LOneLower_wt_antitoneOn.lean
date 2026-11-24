-- Prove2me | solution 1 for GlobalTheory.LOneLower.wt_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:10.706387+00:00
-- url     : https://prove2.me/submissions/da9c4d23-b9e5-4885-8c92-9d9c1dfee480

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
theorem _root_.solution : AntitoneOn wt (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt wt (-(x ^ 2)⁻¹ - (-Real.exp x / (Real.exp x - 1) ^ 2)) x := by
    intro x hx
    have h5 : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    exact (hasDerivAt_inv hx.ne').sub (((Real.hasDerivAt_exp x).sub_const 1).inv h5.ne')
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    rw [(hd x hx).deriv]
    have h5 : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h6 : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.2 (by linarith)
    rw [Real.sinh_eq] at h6
    have h7 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h8 : Real.exp x = Real.exp (x / 2) ^ 2 := by rw [sq, ← Real.exp_add]; simp
    have h9 := Real.exp_pos (x / 2)
    have h10 : x * Real.exp (x / 2) ≤ Real.exp x - 1 := by rw [h8]; nlinarith
    have h11 : (x * Real.exp (x / 2)) ^ 2 ≤ (Real.exp x - 1) ^ 2 := by gcongr
    rw [mul_pow, ← h8] at h11
    have : Real.exp x / (Real.exp x - 1) ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    rw [neg_div]
    linarith
end GlobalTheory.LOneLower
