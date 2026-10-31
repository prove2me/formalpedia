-- Prove2me | solution 1 for MarkovProcess.le_dyadicCeiling_comp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:17.762325+00:00
-- url     : https://prove2.me/submissions/b9a07387-bd82-4c9d-af1d-e9d5d299e47c

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
theorem solution (n : ℕ) (T : Omega → NNReal) :
    T ≤ fun omega ↦ dyadicCeiling n (T omega) := fun omega ↦ le_dyadicCeiling n (T omega)
