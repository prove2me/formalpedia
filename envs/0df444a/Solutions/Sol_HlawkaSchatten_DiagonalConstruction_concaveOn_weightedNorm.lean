-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.concaveOn_weightedNorm
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T00:46:21.304666+00:00
-- url     : https://prove2.me/submissions/8a727509-ab5d-4dd2-a91b-7a4502f28e13

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedCoordinates
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Concavity under common coordinate reweighting -/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

omit [Fintype ι] in
theorem convex_nonnegative_weights : Convex ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
  intro w hw v hv a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hv i))

theorem solution {p : ℝ} (hp : 1 < p) (x : ι → ℝ) :
    ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} (weightedNorm p x) := by
  refine ⟨convex_nonnegative_weights, ?_⟩
  intro w hw v hv a b ha hb hab
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hwSum : 0 ≤ ∑ i, w i * |x i| ^ p :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (Real.rpow_nonneg (abs_nonneg _) _)
  have hvSum : 0 ≤ ∑ i, v i * |x i| ^ p :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hv i) (Real.rpow_nonneg (abs_nonneg _) _)
  have h := (Real.concaveOn_rpow (one_div_nonneg.mpr hp0.le)
    ((div_le_one hp0).mpr hp.le)).2
    hwSum hvSum ha hb hab
  simpa only [weightedNorm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] using h
