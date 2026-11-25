-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.differentiable_hurwitzComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:22.364413+00:00
-- url     : https://prove2.me/submissions/a891da7f-caf1-4c6c-8b0f-8df402876ea7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution (x : ℝ) : Differentiable ℂ (hurwitzComb x) := by
  have hd : ∀ a b : UnitAddCircle, Differentiable ℂ (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) := by
    intro a b
    have h := (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add
      ((differentiable_hurwitzZetaOdd a).sub (differentiable_hurwitzZetaOdd b))
    have e : (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) =
        (fun s ↦ hurwitzZetaEven a s - hurwitzZetaEven b s) + (hurwitzZetaOdd a - hurwitzZetaOdd b) := by
      funext s
      simp only [hurwitzZeta, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    exact h
  have h := (hd (x : UnitAddCircle) ((1 : ℝ) : UnitAddCircle)).add
    ((hd ((1 / 2 : ℝ) : UnitAddCircle) ((1 : ℝ) : UnitAddCircle)).const_mul ((2 * x - 2 : ℝ) : ℂ))
  have e : hurwitzComb x = (fun s ↦ hurwitzZeta (x : UnitAddCircle) s -
      hurwitzZeta ((1 : ℝ) : UnitAddCircle) s) + fun s ↦ ((2 * x - 2 : ℝ) : ℂ) *
        (hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s - hurwitzZeta ((1 : ℝ) : UnitAddCircle) s) := by
    funext s
    simp only [hurwitzComb, Pi.add_apply]
    push_cast
    ring
  rw [e]
  exact h
end GroundTheory.Global.Quadratic
