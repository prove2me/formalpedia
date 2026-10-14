-- Prove2me | solution 1 for OAI.PiExponent.log_nat_polynomial_growth_div_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:48:37.196476+00:00
-- url     : https://prove2.me/submissions/9766c313-063b-4b85-ad4a-fb0d2951802a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology
open Filter

theorem solution
    (f : ℝ → ℕ) (C : ℝ) (p : ℕ) (hC : 0 < C)
    (hbound : ∀ᶠ H : ℝ in atTop,
      0 < H ∧ 1 ≤ f H ∧ (f H : ℝ) ≤ C * H ^ p) :
    Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by
  have hconst : Tendsto (fun H : ℝ => Real.log C / H) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto id atTop atTop))
  have hlog : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hupper : Tendsto
      (fun H : ℝ => Real.log C / H + (p : ℝ) * (Real.log H / H)) atTop (𝓝 0) := by
    simpa using hconst.add (hlog.const_mul (p : ℝ))
  have hevent : ∀ᶠ H : ℝ in atTop, 0 ≤ Real.log (f H : ℝ) / H ∧
      Real.log (f H : ℝ) / H ≤ Real.log C / H + (p : ℝ) * (Real.log H / H) := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with H hHbound hH
    rcases hHbound with ⟨hHpos, hflo, hfhi⟩
    have hfpos : 0 < (f H : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hflo
    have hpowpos : 0 < H ^ p := pow_pos hHpos p
    have hloglo : 0 ≤ Real.log (f H : ℝ) := Real.log_nonneg (by exact_mod_cast hflo)
    have hloghi : Real.log (f H : ℝ) ≤ Real.log (C * H ^ p) :=
      Real.log_le_log hfpos hfhi
    have hlogprod : Real.log (C * H ^ p) = Real.log C + (p : ℝ) * Real.log H := by
      rw [Real.log_mul hC.ne' (ne_of_gt hpowpos), Real.log_pow]
    constructor
    · exact div_nonneg hloglo (le_of_lt hHpos)
    · rw [hlogprod] at hloghi
      have hdiv := div_le_div_of_nonneg_right hloghi (le_of_lt hHpos)
      simpa only [add_div, mul_div_assoc] using hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (hevent.mono fun H h => h.1) (hevent.mono fun H h => h.2)