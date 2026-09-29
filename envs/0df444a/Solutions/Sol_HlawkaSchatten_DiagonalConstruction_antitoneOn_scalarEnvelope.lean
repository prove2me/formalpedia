-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.antitoneOn_scalarEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T20:56:49.119415+00:00
-- url     : https://prove2.me/submissions/627d5d1c-660c-4ed3-875c-40af9cb3c245

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Monotonicity of the scalar envelope -/

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











theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)























end HlawkaSchatten.DiagonalConstruction

theorem scalarEnvelopeRoot_eq_lpNorm {p q : ℝ} (hq : 0 ≤ q) :
    scalarEnvelopeRoot p q = (1 / 2 : ℝ) ^ (1 / p) * lpNorm p ![1, q] := by
  simp only [scalarEnvelopeRoot, lpNorm, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, abs_one, abs_of_nonneg hq, Real.one_rpow]
  rw [show (1 + q ^ p) / 2 = (1 / 2 : ℝ) * (1 + q ^ p) by ring,
    Real.mul_rpow (by norm_num) (by positivity)]

theorem convexOn_scalarEnvelopeRoot {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.Ici 0) (scalarEnvelopeRoot p) := by
  refine ⟨convex_Ici _, ?_⟩
  intro q hq r hr a b ha hb hab
  have hqr : 0 ≤ a * q + b * r := add_nonneg (mul_nonneg ha hq) (mul_nonneg hb hr)
  have heq : ![1, a * q + b * r] = a • ![1, q] + b • ![1, r] := by
    ext i
    fin_cases i <;> simp [hab]
  have h := (convexOn_lpNorm (ι := Fin 2) (E := ℝ) hp).2
    (Set.mem_univ ![1, q]) (Set.mem_univ ![1, r]) ha hb hab
  simp only [smul_eq_mul]
  rw [scalarEnvelopeRoot_eq_lpNorm hqr, scalarEnvelopeRoot_eq_lpNorm hq,
    scalarEnvelopeRoot_eq_lpNorm hr, heq]
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / p))
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using hm

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

@[simp]
theorem scalarEnvelopeRoot_one (p : ℝ) : scalarEnvelopeRoot p 1 = 1 := by
  norm_num [scalarEnvelopeRoot]

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem solution {p : ℝ} (hp : 1 ≤ p) :
    AntitoneOn (scalarEnvelope p) (Set.Ico 0 1) := by
  intro r hr q hq hrq
  have hp0 := zero_lt_one.trans_le hp
  have hrne : 1 - r ≠ 0 := by linarith [hr.2]
  let a := (1 - q) / (1 - r)
  let b := (q - r) / (1 - r)
  have ha : 0 ≤ a := div_nonneg (by linarith [hq.2]) (by linarith [hr.2])
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hrq) (by linarith [hr.2])
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hrne]; ring
  have hpoint : a • r + b • (1 : ℝ) = q := by
    dsimp [a, b, smul_eq_mul]
    field_simp [hrne]
    ring
  have hconv := (convexOn_scalarEnvelopeRoot hp).2 hr.1 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    ha hb hab
  rw [hpoint, scalarEnvelopeRoot_one] at hconv
  simp only [smul_eq_mul] at hconv
  have hm := mul_le_mul_of_nonneg_left hconv (by linarith [hr.2] : 0 ≤ 1 - r)
  have heq : (1 - r) * (a * scalarEnvelopeRoot p r + b * 1) =
      (1 - q) * scalarEnvelopeRoot p r + (q - r) := by
    dsimp [a, b]
    field_simp [hrne]
  rw [heq] at hm
  rw [scalarEnvelope, scalarEnvelope,
    div_le_div_iff₀ (scalarEnvelope_denominator_pos hp0 hq.1 hq.2)
      (scalarEnvelope_denominator_pos hp0 hr.1 hr.2)]
  nlinarith
