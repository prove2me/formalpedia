-- Prove2me | solution 1 for Grothendieck.constant_bookkeeping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:44:29.950209+00:00
-- url     : https://prove2.me/submissions/43570be9-8afe-47f5-8453-ae64ff1da93b

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- `Γ((r+2)/2) = (r/2)·Γ(r/2)` for `r ≥ 1`. -/
theorem Gamma_half_succ (r : ℕ) (hr : 1 ≤ r) :
    Real.Gamma (((r : ℝ) + 2) / 2) = ((r : ℝ) / 2) * Real.Gamma ((r : ℝ) / 2) := by
  have hpos : (0:ℝ) < (r : ℝ) / 2 := by
    have : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have harg : ((r : ℝ) + 2) / 2 = (r : ℝ) / 2 + 1 := by ring
  rw [harg, Real.Gamma_add_one (ne_of_gt hpos)]

/-- **The constant bookkeeping of Lemma 2.1.** With `M = (r+2)/2`, the prefactor
`2rτ/π · ½Γ(½)Γ(M-½)/Γ(M) · ½` equals `τ·Γ((r+1)/2)/(√π·Γ(r/2))`, the constant in the paper's
`E_r`. -/
theorem constant_bookkeeping_proof (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) :
    2 * (r : ℝ) * τ * Real.pi⁻¹ *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
          Real.Gamma (((r : ℝ) + 2) / 2)) * (1 / 2)
      = τ * Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) := by
  have hr1 : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r : ℝ) := by linarith
  have hG : Real.Gamma (((r : ℝ) + 2) / 2) = ((r : ℝ) / 2) * Real.Gamma ((r : ℝ) / 2) :=
    Gamma_half_succ r hr
  have hhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have harg : ((r : ℝ) + 2) / 2 - 1 / 2 = ((r : ℝ) + 1) / 2 := by ring
  rw [harg, hG, hhalf]
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hg : (0:ℝ) < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg1 : (0:ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) :
    2 * (r : ℝ) * τ * Real.pi⁻¹ *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
          Real.Gamma (((r : ℝ) + 2) / 2)) * (1 / 2)
      = τ * Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) :=
  constant_bookkeeping_proof r hr τ
