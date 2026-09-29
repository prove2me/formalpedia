-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.convex_entryBox
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T19:43:22.316341+00:00
-- url     : https://prove2.me/submissions/58a15eb8-563f-4601-9544-12822ee1663c

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Simultaneous permutation averaging on the cyclic box -/

open HlawkaSchatten.DiagonalConstruction

theorem solution : Convex ℝ entryBox := by
  intro X hX Y hY a b ha hb hab j i
  have heq : (a • X + b • Y) j i - cyclicCenter j i =
      a * (X j i - cyclicCenter j i) + b * (Y j i - cyclicCenter j i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * cyclicCenter j i) hab]
  rw [heq]
  calc
    _ ≤ |a * (X j i - cyclicCenter j i)| + |b * (Y j i - cyclicCenter j i)| := abs_add_le _ _
    _ = a * |X j i - cyclicCenter j i| + b * |Y j i - cyclicCenter j i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (19 / 100) + b * (19 / 100) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX j i) ha)
        (mul_le_mul_of_nonneg_left (hY j i) hb)
    _ = 19 / 100 := by nlinarith
