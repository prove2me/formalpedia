-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.log_nat_polynomial_bound_div_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:20.033455+00:00
-- url     : https://prove2.me/submissions/bfaafc93-db82-4cdf-b85e-78d9597fdf8b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

section
open MeasureTheory Filter Topology
theorem O3logH : Tendsto (fun H : Real => Real.log (H + 1) / H) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_id)
  refine h.congr' (Eventually.of_forall fun H => ?_)
  simp

theorem O3gen (g : Real → Real) (C : Real) (N : Nat) (hC : 0 < C)
    (h : ∀ᶠ H : Real in atTop, 1 ≤ g H ∧ g H ≤ C * (H + 1) ^ N) :
    Tendsto (fun H : Real => Real.log (g H) / H) atTop (𝓝 0) := by
  have hup : Tendsto (fun H : Real => Real.log C * H⁻¹ + N * (Real.log (H + 1) / H)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.const_mul (Real.log C)).add (O3logH.const_mul (N : Real))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [h, eventually_gt_atTop 0] with H hH hpos
    exact div_nonneg (Real.log_nonneg hH.1) hpos.le
  · filter_upwards [h, eventually_gt_atTop 0] with H hH hpos
    have h1 : Real.log (g H) ≤ Real.log C + N * Real.log (H + 1) := by
      calc Real.log (g H) ≤ Real.log (C * (H + 1) ^ N) :=
            Real.log_le_log (by linarith [hH.1]) hH.2
        _ = Real.log C + N * Real.log (H + 1) := by
            rw [Real.log_mul hC.ne' (by positivity), Real.log_pow]
    rw [div_le_iff₀ hpos]
    have : (Real.log C * H⁻¹ + N * (Real.log (H + 1) / H)) * H = Real.log C + N * Real.log (H + 1) := by
      field_simp
    linarith

end

open MeasureTheory Filter Topology in

theorem solution (f : Real → Nat) (C : Real) (N : Nat) (hC : 0 < C) (hbound : ∀ᶠ H : Real in atTop, 0 < (f H : Real) ∧ (f H : Real) ≤ C * (H + 1) ^ N) : Tendsto (fun H : Real => Real.log (f H : Real) / H) atTop (𝓝 0) := by
  refine O3gen (fun H => (f H : Real)) C N hC ?_
  filter_upwards [hbound] with H hH
  refine ⟨?_, hH.2⟩
  have : 0 < f H := by exact_mod_cast hH.1
  exact_mod_cast this
