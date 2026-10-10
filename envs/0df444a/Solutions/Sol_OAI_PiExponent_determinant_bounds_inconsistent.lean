-- Prove2me | solution 1 for OAI.PiExponent.determinant_bounds_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:29:12.970618+00:00
-- url     : https://prove2.me/submissions/041a843f-a431-4119-83a1-854254a4be50

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

theorem solution
    (nu theta x b ear ean err collision d : ℝ)
    (hnu : 1 < nu) (hb0 : 0 ≤ b) (hb : b ≤ theta)
    (hgap : ear + ean + err < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean + err < collision)
    (hlower : -(1 - b) - ear ≤ d)
    (hupper : d ≤ ean + err + max (-collision) (-nu * (x - b))) : False := by
  have hfirst : ean + err - collision < -(1 - b) - ear := by linarith
  have hmono :
      nu * (x - theta) - (1 - theta) ≤ nu * (x - b) - (1 - b) := by
    nlinarith
  have hsecond : ean + err - nu * (x - b) < -(1 - b) - ear := by linarith
  rcases le_total (-collision) (-nu * (x - b)) with h | h
  · rw [max_eq_right h] at hupper
    linarith
  · rw [max_eq_left h] at hupper
    linarith