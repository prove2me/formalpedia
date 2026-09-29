-- Prove2me | solution 1 for HlawkaSchatten.convexOn_abs_rpow
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T17:36:27.83851+00:00
-- url     : https://prove2.me/submissions/e8e48ce3-a950-402d-a4b1-237bfe8bba79

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Scalar power Bregman data

These are the scalar objects used in the first layer of the audited
Bregman--Mazur proof. The normalization of `powerPotential` is important:
its derivative is the signed `(p - 1)`-power with no extra factor of `p`.
-/


open Filter
open scoped Topology

theorem solution {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hImage : (norm : ℝ → ℝ) '' Set.univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact norm_nonneg x
    · intro hy
      have hy' : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
      exact ⟨y, Set.mem_univ y, by simp [abs_of_nonneg hy']⟩
  have hOuter : ConvexOn ℝ ((norm : ℝ → ℝ) '' Set.univ) (fun y : ℝ ↦ y ^ p) := by
    rw [hImage]
    exact convexOn_rpow hp
  have hMono : MonotoneOn (fun y : ℝ ↦ y ^ p) ((norm : ℝ → ℝ) '' Set.univ) := by
    rw [hImage]
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (zero_lt_one.trans_le hp)).monotoneOn
  convert hOuter.comp convexOn_univ_norm hMono using 1
  ext x
  simp only [Function.comp_apply, Real.norm_eq_abs]
