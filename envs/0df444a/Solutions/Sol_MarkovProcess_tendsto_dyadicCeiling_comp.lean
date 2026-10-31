-- Prove2me | solution 1 for MarkovProcess.tendsto_dyadicCeiling_comp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:30:55.567467+00:00
-- url     : https://prove2.me/submissions/e988cd23-a32a-4ed0-98e6-13676a61755e

import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section





/-- The real coercion of a dyadic ceiling is its defining quotient. -/
private theorem coe_dyadicCeiling (n : ℕ) (t : NNReal) :
    ((dyadicCeiling n t : NNReal) : ℝ) = (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) / 2 ^ n := rfl



/-- The level-`n` dyadic ceiling is at least the time it approximates. -/
theorem le_dyadicCeiling (n : ℕ) (t : NNReal) : t ≤ dyadicCeiling n t := by
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  calc (t : ℝ) * 2 ^ n = (2 ^ n : ℝ) * (t : ℝ) := by ring
    _ ≤ (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _



/-- The level-`n` dyadic ceiling overshoots by at most one grid step. -/
theorem dyadicCeiling_le_add (n : ℕ) (t : NNReal) :
    dyadicCeiling n t ≤ t + (2 ^ n : NNReal)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt h2)
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, div_le_iff₀ h2]
  calc (⌈(2 ^ n : ℝ) * (t : ℝ)⌉₊ : ℝ) ≤ (2 ^ n : ℝ) * (t : ℝ) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ = ((t : ℝ) + ((2 : ℝ) ^ n)⁻¹) * 2 ^ n := by rw [add_mul, hinv]; ring









/-- The dyadic ceilings of a fixed time converge to that time. -/
theorem tendsto_dyadicCeiling (t : NNReal) :
    Tendsto (fun n ↦ dyadicCeiling n t) atTop (𝓝 t) := by
  have hhalf : ((2 : NNReal))⁻¹ < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
    norm_num
  have hinv : Tendsto (fun n : ℕ ↦ (2 ^ n : NNReal)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hhalf
  have hupper : Tendsto (fun n : ℕ ↦ t + (2 ^ n : NNReal)⁻¹) atTop (𝓝 t) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ le_dyadicCeiling n t) (fun n ↦ dyadicCeiling_le_add n t)













variable {Omega : Type*} {m : MeasurableSpace Omega}









end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic ceiling approximation of finite stopping times

The level-`n` dyadic ceiling of a nonnegative time is the least point of the grid `2⁻ⁿ ℕ` that is
at least the time.  Composed with a finite `NNReal`-valued stopping time it produces stopping
times with countable range that decrease to the original time.  This is ordinary stopping-time
infrastructure and proves no restart identity; the restart identity obtained from this
approximation is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal







































variable {Omega : Type*} {m : MeasurableSpace Omega}





namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (T : Omega → NNReal) (omega : Omega) :
    Tendsto (fun n ↦ dyadicCeiling n (T omega)) atTop (𝓝 (T omega)) :=
  tendsto_dyadicCeiling (T omega)
