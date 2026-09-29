-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.normalized_pair_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T22:42:29.932805+00:00
-- url     : https://prove2.me/submissions/f8144b24-0bae-4eba-91bd-df6dfac6d345

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_lpNorm_eq_zero_iff
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_weighted_lp_power
import Theorems.Thm_HlawkaSchatten_convexOn_abs_rpow
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















theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))





























end HlawkaSchatten.DiagonalConstruction

theorem weighted_abs_rpow_div {a : ℝ} (ha : 0 < a) (p x : ℝ) :
    a * |x / a| ^ p = |x| ^ p / a ^ (p - 1) := by
  rw [abs_div, abs_of_pos ha, Real.div_rpow (abs_nonneg x) ha.le,
    Real.rpow_sub ha, Real.rpow_one]
  field_simp

theorem weighted_mean_power_le {p : ℝ} (hp : 1 < p) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i) (hs : ∑ i, a i = 2) :
    ((∑ i, b i) / 2) ^ p ≤ (∑ i, b i ^ p / a i ^ (p - 1)) / 2 := by
  have h := (convexOn_abs_rpow hp.le).map_sum_le (t := Finset.univ)
    (w := fun i ↦ a i / 2) (p := fun i ↦ b i / a i)
    (fun i _ ↦ div_nonneg (ha i).le (by norm_num))
    (by rw [← Finset.sum_div, hs]; norm_num) (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have hmean (i : ι) : a i / 2 * (b i / a i) = b i / 2 := by
    field_simp [(ha i).ne']
  have hpower (i : ι) : a i / 2 * |b i / a i| ^ p =
      (b i ^ p / a i ^ (p - 1)) / 2 := by
    calc
      _ = (a i * |b i / a i| ^ p) / 2 := by ring
      _ = _ := by rw [weighted_abs_rpow_div (ha i), abs_of_nonneg (hb i)]
  have habs : |(∑ i, b i) / 2| = (∑ i, b i) / 2 :=
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ ↦ hb i) (by norm_num))
  simpa only [hmean, hpower, ← Finset.sum_div, habs] using h

theorem solution {p : ℝ} (hp : 1 < p) (x y z : ι → ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1) :
    lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z) ≤
      2 * scalarEnvelopeRoot p (lpNorm p (x + y + z)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let a : Fin 3 → ℝ := ![lpNorm p x + lpNorm p y,
    lpNorm p x + lpNorm p z, lpNorm p y + lpNorm p z]
  let b : Fin 3 → ℝ := ![lpNorm p (x + y), lpNorm p (x + z), lpNorm p (y + z)]
  have ha : ∀ i, 0 < a i := by
    intro i
    fin_cases i
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hy)
    · exact add_pos (lpNorm_pos hp0 hx) (lpNorm_pos hp0 hz)
    · exact add_pos (lpNorm_pos hp0 hy) (lpNorm_pos hp0 hz)
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> exact lpNorm_nonneg p _
  have hsum : ∑ i, a i = 2 := by
    simp only [a, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linarith
  have hmean := weighted_mean_power_le hp a b ha hb hsum
  have hweighted := weighted_lp_power hp x y z
  rw [hS, Real.one_rpow, div_one] at hweighted
  simp only [a, b, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hmean
  have hpow : ((lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2) ^ p ≤
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by linarith
  have hbase : 0 ≤ (1 + lpNorm p (x + y + z) ^ p) / 2 :=
    div_nonneg (add_nonneg zero_le_one
      (Real.rpow_nonneg (lpNorm_nonneg p (x + y + z)) p)) (by norm_num)
  have hroot : scalarEnvelopeRoot p (lpNorm p (x + y + z)) ^ p =
      (1 + lpNorm p (x + y + z) ^ p) / 2 := by
    rw [scalarEnvelopeRoot, ← Real.rpow_mul hbase,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [← hroot] at hpow
  have h := (Real.rpow_le_rpow_iff
    (div_nonneg (add_nonneg (add_nonneg (lpNorm_nonneg p (x + y))
      (lpNorm_nonneg p (x + z))) (lpNorm_nonneg p (y + z))) (by norm_num))
    (Real.rpow_nonneg hbase _) hp0).mp hpow
  change (lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z)) / 2 ≤
    scalarEnvelopeRoot p (lpNorm p (x + y + z)) at h
  linarith
