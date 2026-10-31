-- Prove2me | solution 1 for MarkovProcess.antitone_dyadicCeiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:27:21.894987+00:00
-- url     : https://prove2.me/submissions/88cd82dc-8f90-43f0-b07e-a74ff23c0f30

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























namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (t : NNReal) : Antitone fun n ↦ dyadicCeiling n t := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  show dyadicCeiling (n + 1) t ≤ dyadicCeiling n t
  have hceil : ⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ ≤ 2 * ⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ := by
    rw [Nat.ceil_le]
    push_cast
    calc (2 : ℝ) ^ (n + 1) * (t : ℝ) = 2 * ((2 : ℝ) ^ n * (t : ℝ)) := by ring
      _ ≤ 2 * (⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℝ) := by gcongr; exact Nat.le_ceil _
  have hceilR : ((⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ : ℕ) : ℝ) ≤
      2 * ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hceil
  rw [← NNReal.coe_le_coe, coe_dyadicCeiling, coe_dyadicCeiling,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((⌈(2 : ℝ) ^ (n + 1) * (t : ℝ)⌉₊ : ℕ) : ℝ) * 2 ^ n
      ≤ (2 * ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ)) * 2 ^ n := by gcongr
    _ = ((⌈(2 : ℝ) ^ n * (t : ℝ)⌉₊ : ℕ) : ℝ) * 2 ^ (n + 1) := by ring
