-- Prove2me | solution 1 for MarginalUtility.successive_gains_decrease_of_strictConcaveOn
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:54:28.605815+00:00
-- url     : https://prove2.me/submissions/ad9e9c00-095e-47b6-8369-e664533f2cc3

import Definitions.Def_MarginalUtility_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Lean.Elab.Tactic.Omega
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MarginalUtility

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hU : StrictConcaveOn ℝ D U) (x h : ℝ) (hh : 0 < h)
    (hx : x ∈ D) (hx2 : x + 2 * h ∈ D) :
    utilityChange U (x + h) (x + 2 * h) < utilityChange U x (x + h) := by
  have hne : x ≠ x + 2*h := by linarith
  have hc := hU.2 hx hx2 hne
    (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  have hm : (1/2:ℝ)*x+(1/2:ℝ)*(x+2*h)=x+h := by ring
  simp only [smul_eq_mul,hm] at hc
  unfold utilityChange
  linarith



