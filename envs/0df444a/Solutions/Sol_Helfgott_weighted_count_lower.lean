-- Prove2me | solution 1 for Helfgott.weighted_count_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T23:53:26.861044+00:00
-- url     : https://prove2.me/submissions/cc7f6ca8-4052-4269-be26-a50baeac9419
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_actual_major_arc_lower
import Theorems.Thm_Helfgott_actual_minor_arc_upper
import Theorems.Thm_Helfgott_weighted_count_lower_of_numerical_arcs
import Mathlib.Analysis.Real.Pi.Bounds

/-! Tracked reduction draft. The two actual arc bounds remain Open.
Only submit after all three imported targets have published and their exact
statements are confirmed. This is not a full direct Goldbach proof.
Written by Codex. -/

open MeasureTheory Helfgott
open scoped BigOperators

namespace HelfgottArcBridge

lemma goldbach_denominator_bounds :
    (2 : ℝ) ≤ 2+9/(196*Real.sqrt (2*Real.pi)) ∧
    2+9/(196*Real.sqrt (2*Real.pi)) ≤ (203/100 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt (2*Real.pi) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)
  have hs : (2 : ℝ) ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  have hsp : 0 < 196*Real.sqrt (2*Real.pi) := by positivity
  constructor
  · have h : 0 ≤ 9/(196*Real.sqrt (2*Real.pi)) := by positivity
    linarith
  · have h : 9/(196*Real.sqrt (2*Real.pi)) ≤ (3/100 : ℝ) := by
      apply (div_le_iff₀ hsp).mpr
      nlinarith
    linarith

lemma goldbachScale_pos (N : ℕ) (hN : 0 < N) : 0 < goldbachScale N := by
  have hd := goldbach_denominator_bounds.1
  unfold goldbachScale
  apply div_pos (by exact_mod_cast hN)
  linarith

lemma goldbachScale_le_relation (N : ℕ) :
    (N : ℝ) ≤ (203/100 : ℝ)*goldbachScale N := by
  have hd := goldbach_denominator_bounds
  have hp : 0 < 2+9/(196*Real.sqrt (2*Real.pi)) := by linarith [hd.1]
  have hx : 0 ≤ goldbachScale N := by unfold goldbachScale; positivity
  have he : goldbachScale N*(2+9/(196*Real.sqrt (2*Real.pi))) = (N : ℝ) := by
    unfold goldbachScale
    exact div_mul_cancel₀ _ hp.ne'
  have h := mul_le_mul_of_nonneg_left hd.2 hx
  rw [he] at h
  simpa only [mul_comm] using h

lemma goldbachScale_analytic_range (N : ℕ) (hN : 10^27 ≤ N) :
    (49 : ℝ)*10^25 ≤ goldbachScale N := by
  have hn : (10 : ℝ)^27 ≤ (N : ℝ) := by exact_mod_cast hN
  have hs := goldbachScale_le_relation N
  linarith


end HelfgottArcBridge

theorem solution (N : ℕ) (hN : 10 ^ 27 ≤ N) (hodd : Odd N) :
    let x : ℝ := (N : ℝ) / (2 + 9 / (196 * Real.sqrt (2 * Real.pi)))
    (1 / 2500 : ℝ) * (N : ℝ)^2 ≤
      ∑ t ∈ tripleIndices N,
        weightedTripleTerm (fun n => etaPlus ((n : ℝ) / x))
          (fun n => etaStar ((n : ℝ) / x)) t := by
  have hp : 0 < N := lt_of_lt_of_le (by norm_num : 0 < (10 : ℕ)^27) hN
  exact Helfgott.weighted_count_lower_of_numerical_arcs N hp
    (Helfgott.actual_major_arc_lower N hN hodd)
    (Helfgott.actual_minor_arc_upper (goldbachScale N)
      (HelfgottArcBridge.goldbachScale_analytic_range N hN))

#print axioms solution
