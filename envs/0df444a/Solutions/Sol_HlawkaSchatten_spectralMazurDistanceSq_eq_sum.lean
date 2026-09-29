-- Prove2me | solution 1 for HlawkaSchatten.spectralMazurDistanceSq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T00:50:54.713819+00:00
-- url     : https://prove2.me/submissions/1ff78b6e-3efe-4dda-a769-4219dc1d4126

import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_SpectralLift
import Theorems.Thm_HlawkaSchatten_re_trace_comp_eq_sum_eigenbasis_overlap
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/


open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open HlawkaSchatten

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

namespace HlawkaSchatten

open scoped InnerProductSpace





section SpectralOverlap

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]





/-- Completeness of the second spectral basis makes each row of overlap
weights sum to one. -/
theorem sum_orthonormalBasisOverlap_right
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E) (i : ι) :
    ∑ j, orthonormalBasisOverlap e f (i, j) = 1 := by
  simp only [orthonormalBasisOverlap]
  rw [f.sum_sq_norm_inner_left, e.norm_eq_one, one_pow]

/-- Completeness of the first spectral basis makes each column of overlap
weights sum to one. -/
theorem sum_orthonormalBasisOverlap_left
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E) (j : κ) :
    ∑ i, orthonormalBasisOverlap e f (i, j) = 1 := by
  simp only [orthonormalBasisOverlap]
  rw [e.sum_sq_norm_inner_right, f.norm_eq_one, one_pow]



end SpectralOverlap

end HlawkaSchatten

/-- Trace-product expansion for two explicitly diagonal spectral maps. -/
theorem re_trace_spectralDiagonal_comp [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ) :
    (((spectralDiagonal e a).comp (spectralDiagonal f b)).trace ℂ E).re =
      ∑ ij : ι × κ,
        a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
  exact re_trace_comp_eq_sum_eigenbasis_overlap
    (spectralDiagonal e a) (spectralDiagonal f b)
    (spectralDiagonal_isSymmetric e a) e f a b
    (spectralDiagonal_apply_basis e a)
    (spectralDiagonal_apply_basis f b)

theorem sum_left_mul_orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (c : ι → ℝ) :
    ∑ ij : ι × κ, c ij.1 * orthonormalBasisOverlap e f ij = ∑ i, c i := by
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  change (∑ j, c i * orthonormalBasisOverlap e f (i, j)) = c i
  rw [← Finset.mul_sum, sum_orthonormalBasisOverlap_right, mul_one]

theorem sum_right_mul_orthonormalBasisOverlap
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (c : κ → ℝ) :
    ∑ ij : ι × κ, c ij.2 * orthonormalBasisOverlap e f ij = ∑ j, c j := by
  rw [Fintype.sum_prod_type_right]
  apply Fintype.sum_congr
  intro j
  change (∑ i, c j * orthonormalBasisOverlap e f (i, j)) = c j
  rw [← Finset.mul_sum, sum_orthonormalBasisOverlap_left, mul_one]

theorem solution [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralMazurDistanceSq p e a f b =
      ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
        (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 := by
  classical
  unfold spectralMazurDistanceSq
  rw [re_trace_spectralDiagonal, re_trace_spectralDiagonal_comp,
    re_trace_spectralDiagonal]
  rw [← sum_left_mul_orthonormalBasisOverlap e f
    (fun i ↦ scalarMazur p (a i) ^ 2)]
  rw [← sum_right_mul_orthonormalBasisOverlap e f
    (fun j ↦ scalarMazur p (b j) ^ 2)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro ij
  simp only [Function.comp_apply]
  ring
