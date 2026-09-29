-- Prove2me | solution 1 for HlawkaSchatten.finset_sum_scalarBregman_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:28:29.91159+00:00
-- url     : https://prove2.me/submissions/daa94de0-3021-4001-a76e-c0f7d0b112cc

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Theorems.Thm_HlawkaSchatten_scalarBregman_two_sided_of_compactified_bounds
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/


open scoped InnerProductSpace

open HlawkaSchatten

theorem solution {ι : Type*} {p m M : ℝ}
    (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    m * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
        ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ∧
      ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ≤
        M * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 := by
  have hpoint (i : ι) :
      m * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
          scalarBregman p (a i) (b i) ∧
        scalarBregman p (a i) (b i) ≤
          M * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 :=
    scalarBregman_two_sided_of_compactified_bounds hp hbound (a i) (b i)
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hpoint i).1 (hw i hi)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hpoint i).2 (hw i hi)
