-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.lp_hlawka_le_exponent
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T20:49:13.876524+00:00
-- url     : https://prove2.me/submissions/5adc34d2-1334-47e1-a6d9-b255493d92eb

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_weighted_lp_power
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/








variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]



theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]





theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)





































end HlawkaSchatten.DiagonalConstruction

theorem weighted_abs_rpow_div {a : ℝ} (ha : 0 < a) (p x : ℝ) :
    a * |x / a| ^ p = |x| ^ p / a ^ (p - 1) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg x) ha.le,
    Real.rpow_sub ha, Real.rpow_one]
  field_simp

theorem normalized_power_deficit_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    a - b ^ p / a ^ (p - 1) ≤ p * (a - b) := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  have hbern := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ b / a - 1 by linarith [div_nonneg hb ha]) hp.le
  have habs : |b / a| = b / a := abs_of_nonneg (div_nonneg hb ha)
  have he := weighted_abs_rpow_div ha0 p b
  rw [habs, abs_of_nonneg hb] at he
  have hm := mul_le_mul_of_nonneg_left hbern ha
  have hr : a * (b / a) = b := mul_div_cancel₀ b ha0.ne'
  simp only [add_sub_cancel] at hm
  nlinarith

theorem normalized_power_le {p a b : ℝ} (hp : 1 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    b ^ p / a ^ (p - 1) ≤ b := by
  by_cases h : a = 0
  · have hb0 : b = 0 := le_antisymm (h ▸ hba) hb
    simp [h, hb0, (zero_lt_one.trans hp).ne']
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ha0 (p - 1))).mpr
  have hpow := Real.rpow_le_rpow hb hba (sub_nonneg.mpr hp.le)
  have he : b ^ p = b * b ^ (p - 1) := by
    by_cases hb0 : b = 0
    · simp [hb0, (zero_lt_one.trans hp).ne']
    · rw [Real.rpow_sub (lt_of_le_of_ne hb (Ne.symm hb0)), Real.rpow_one]
      field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hpow hb

theorem solution {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ) :
    tripleGap (lpNorm p) x y z ≤ p * pairGapSum (lpNorm p) x y z := by
  have hx := lpNorm_nonneg p x
  have hy := lpNorm_nonneg p y
  have hz := lpNorm_nonneg p z
  have hxy := lpNorm_add hp.le x y
  have hxz := lpNorm_add hp.le x z
  have hyz := lpNorm_add hp.le y z
  have htotal : lpNorm p (x + y + z) ≤ lpNorm p x + lpNorm p y + lpNorm p z :=
    (lpNorm_add hp.le (x + y) z).trans (add_le_add hxy le_rfl)
  have h0 := weighted_lp_power hp x y z
  have h1 := normalized_power_deficit_le hp (add_nonneg hx hy)
    (lpNorm_nonneg p (x + y)) hxy
  have h2 := normalized_power_deficit_le hp (add_nonneg hx hz)
    (lpNorm_nonneg p (x + z)) hxz
  have h3 := normalized_power_deficit_le hp (add_nonneg hy hz)
    (lpNorm_nonneg p (y + z)) hyz
  have h4 := normalized_power_le hp (add_nonneg (add_nonneg hx hy) hz)
    (lpNorm_nonneg p (x + y + z)) htotal
  dsimp only [tripleGap, pairGapSum, pairGap]
  nlinarith
