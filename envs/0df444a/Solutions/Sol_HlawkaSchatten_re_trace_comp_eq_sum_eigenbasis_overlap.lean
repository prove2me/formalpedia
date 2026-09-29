-- Prove2me | solution 1 for HlawkaSchatten.re_trace_comp_eq_sum_eigenbasis_overlap
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T22:43:22.605271+00:00
-- url     : https://prove2.me/submissions/f11b3937-ef7d-442f-9cfa-52fb2afe05f0

import Definitions.Def_HlawkaSchatten_SpectralLift
import Theorems.Thm_HlawkaSchatten_re_inner_apply_eq_sum_eigenbasis
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

theorem solution [FiniteDimensional ℂ E]
    (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (a : ι → ℝ) (b : κ → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i)
    (hf : ∀ j, B (f j) = (b j : ℂ) • f j) :
    ((A.comp B).trace ℂ E).re =
      ∑ ij : ι × κ, a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
  calc
    ((A.comp B).trace ℂ E).re =
        ∑ j, (⟪f j, (A.comp B) (f j)⟫_ℂ).re := by
      rw [LinearMap.trace_eq_sum_inner (A.comp B) f, Complex.re_sum]
    _ = ∑ j, b j * ∑ i, a i * orthonormalBasisOverlap e f (i, j) := by
      apply Fintype.sum_congr
      intro j
      rw [LinearMap.comp_apply, hf j, map_smul, inner_smul_right,
        Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [re_inner_apply_eq_sum_eigenbasis A hA e a he]
      rfl
    _ = ∑ j, ∑ i, a i * b j * orthonormalBasisOverlap e f (i, j) := by
      apply Fintype.sum_congr
      intro j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ ij : ι × κ,
        a ij.1 * b ij.2 * orthonormalBasisOverlap e f ij := by
      rw [Fintype.sum_prod_type_right]
