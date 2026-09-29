-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.joint_radial_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T23:26:56.306356+00:00
-- url     : https://prove2.me/submissions/5c6984b1-f49b-4466-b8c1-cf18d6e2190c

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_euclideanSq_apply_lower
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

theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]

theorem euclideanSq_column_upper {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    euclideanSq (X j) ≤ 3 * (119 / 100 : ℝ) ^ 2 := by
  have hi (i : Fin 3) : |X j i| ≤ 119 / 100 := by
    have hh := abs_le.mp (hX j i)
    have hc : cyclicCenter j i = -1 ∨ cyclicCenter j i = 1 := by
      simp only [cyclicCenter]; split_ifs <;> simp
    apply abs_le.mpr
    rcases hc with hc | hc <;> rw [hc] at hh <;> constructor <;> linarith
  calc
    _ ≤ ∑ _ : Fin 3, (119 / 100 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ ↦ by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hi i)
    _ = _ := by simp

theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)

theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]

theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)

theorem solution {X : Triple} (hX : X ∈ entryBox) (Z : Triple)
    (a : Fin 3 → ℝ) (b : ℝ) :
    frobeniusSq (Z - b • X) ≤ 300 *
      (frobeniusSq (fun j ↦ Z j - a j • X j) +
        euclideanSq (totalTriple Z - b • totalTriple X)) := by
  let U : Triple := fun j ↦ Z j - a j • X j
  let c : Fin 3 → ℝ := fun j ↦ a j - b
  let D := totalTriple Z - b • totalTriple X
  have he : applyTriple X c = D - totalTriple U := by
    ext i
    simp only [applyTriple, c, D, totalTriple, U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hinv := euclideanSq_apply_lower hX c
  rw [he] at hinv
  have hD := euclideanSq_sub_le D (totalTriple U)
  have hU := euclideanSq_total_le U
  have hcol (j : Fin 3) : euclideanSq ((Z - b • X) j) ≤
      2 * euclideanSq (U j) + 2 * ((a j - b) ^ 2 * (3 * (119 / 100 : ℝ) ^ 2)) := by
    have hh : (Z - b • X) j = U j + (a j - b) • X j := by
      ext i
      simp only [U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring
    rw [hh]
    have h := euclideanSq_add_le (U j) ((a j - b) • X j)
    rw [euclideanSq_smul] at h
    have hm := mul_le_mul_of_nonneg_left (euclideanSq_column_upper hX j) (sq_nonneg (a j - b))
    linarith
  have hbound : frobeniusSq (Z - b • X) ≤
      2 * frobeniusSq U + (6 * (119 / 100 : ℝ) ^ 2) * euclideanSq c := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hh
    change frobeniusSq (Z - b • X) ≤
      2 * frobeniusSq U + 2 * (euclideanSq c * (3 * (119 / 100 : ℝ) ^ 2)) at hh
    nlinarith
  have hUne := frobeniusSq_nonneg U
  have hDne := euclideanSq_nonneg D
  change frobeniusSq (Z - b • X) ≤ 300 * (frobeniusSq U + euclideanSq D)
  nlinarith
