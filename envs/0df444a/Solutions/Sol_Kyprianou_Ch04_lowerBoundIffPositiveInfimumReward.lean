-- Prove2me | solution 1 for Kyprianou.Ch04.lowerBoundIffPositiveInfimumReward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:34.320743+00:00
-- url     : https://prove2.me/submissions/434ba4d1-6e71-4ca0-b34f-89b9264f486b

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Finite lower path bounds are equivalent to a positive infimum of exponential rewards. -/
theorem solution
    (x : NNReal → ℝ) (beta : ℝ) (hb : 0 < beta)
    (hbd : ∀ t : NNReal, BddBelow (x '' Iic t)) :
    BddBelow (range x) ↔
      0 < ⨅ n : ℕ, Real.exp (beta * sInf (x '' Iic (n : NNReal))) := by
  let g : ℕ → ℝ := fun n => Real.exp (beta * sInf (x '' Iic (n : NNReal)))
  have hgb : BddBelow (range g) := ⟨0, by rintro a ⟨n,rfl⟩; exact (Real.exp_pos _).le⟩
  change BddBelow (range x) ↔ 0 < ⨅ n, g n
  constructor
  · rintro ⟨b,hbnd⟩
    have hle (n : ℕ) : Real.exp (beta*b) ≤ g n := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hb.le
      have hn : (x '' Iic (n : NNReal)).Nonempty := ⟨x 0,0,by simp,rfl⟩
      apply le_csInf hn
      rintro y ⟨s,hs,rfl⟩
      exact hbnd ⟨s,rfl⟩
    exact (Real.exp_pos _).trans_le (le_ciInf hle)
  · intro hpos
    refine ⟨Real.log (⨅ n, g n) / beta, ?_⟩
    rintro a ⟨t,rfl⟩
    obtain ⟨n,hn⟩ := exists_nat_ge t
    have h1 : (⨅ k, g k) ≤ g n := ciInf_le hgb n
    have h2 : g n ≤ Real.exp (beta * x t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (csInf_le (hbd _) ⟨t,hn,rfl⟩) hb.le
    have hlog := Real.log_le_log hpos (h1.trans h2)
    rw [Real.log_exp] at hlog
    exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hlog)
