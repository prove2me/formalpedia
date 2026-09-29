-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.euclideanSq_apply_lower
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T23:20:52.520819+00:00
-- url     : https://prove2.me/submissions/68ca0095-d502-449e-a07c-c76c36ec1a1a

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Abel
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

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate uses the convenient bound `300`. This weaker
intermediate constant leaves the exponent cutoff unchanged.
-/

open HlawkaSchatten.DiagonalConstruction

theorem euclideanSq_center_lower (a : Fin 3 → ℝ) :
    euclideanSq a ≤ euclideanSq (applyTriple cyclicCenter a) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hc
  have he : euclideanSq (applyTriple cyclicCenter a) = 4 * euclideanSq a - (∑ i, a i) ^ 2 := by
    have heq : applyTriple cyclicCenter a =
        ![-a 0 + a 1 + a 2, a 0 - a 1 + a 2, a 0 + a 1 - a 2] := by
      ext i
      fin_cases i <;>
        norm_num [applyTriple, cyclicCenter, Fin.sum_univ_three, Fin.ext_iff] <;> ring!
    rw [heq]
    simp only [euclideanSq, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring!
  rw [he]
  change (∑ i, a i) ^ 2 ≤ 3 * euclideanSq a at hc
  linarith

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

theorem euclideanSq_perturbation_upper {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    euclideanSq (applyTriple (X - cyclicCenter) a) ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a := by
  have hrow (i : Fin 3) : (∑ j, (X j i - cyclicCenter j i) ^ 2) ≤ 3 * (19 / 100 : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin 3, (19 / 100 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hX j i)
      _ = _ := by simp
  have hi (i : Fin 3) : (∑ j, a j * (X j i - cyclicCenter j i)) ^ 2 ≤
      euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) := by
    exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j ↦ X j i - cyclicCenter j i)).trans
      (mul_le_mul_of_nonneg_left (hrow i) (euclideanSq_nonneg a))
  calc
    _ ≤ ∑ _ : Fin 3, euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by simp; ring

theorem solution {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    (43 / 100 : ℝ) ^ 2 * euclideanSq a ≤ euclideanSq (applyTriple X a) := by
  let u := applyTriple cyclicCenter a
  let v := applyTriple (X - cyclicCenter) a
  have heq : applyTriple X a = u + v := by
    ext i
    simp only [u, v, applyTriple, Pi.sub_apply, Pi.add_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hid : (57 / 100 : ℝ) * euclideanSq (u + v) - (2451 / 10000 : ℝ) * euclideanSq u +
      (43 / 100 : ℝ) * euclideanSq v = euclideanSq ((57 / 100 : ℝ) • u + v) := by
    simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnon := euclideanSq_nonneg ((57 / 100 : ℝ) • u + v)
  have hu : euclideanSq a ≤ euclideanSq u := euclideanSq_center_lower a
  have hv : euclideanSq v ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a :=
    euclideanSq_perturbation_upper hX a
  rw [heq]
  nlinarith
