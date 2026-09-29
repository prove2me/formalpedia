-- Prove2me | solution 1 for HlawkaSchatten.re_inner_apply_eq_sum_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T22:40:57.678555+00:00
-- url     : https://prove2.me/submissions/6efcc867-9873-43a6-997d-bea527c2dd0f

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

theorem solution
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (he : ∀ i, A (e i) = (a i : ℂ) • e i) (x : E) :
    (⟪x, A x⟫_ℂ).re = ∑ i, a i * ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
  rw [← e.sum_inner_mul_inner x (A x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hA (e i) x, he i, inner_smul_left]
  have ha : (starRingEnd ℂ) (a i : ℂ) = (a i : ℂ) := by
    apply Complex.ext <;> simp
  rw [ha]
  rw [show ⟪x, e i⟫_ℂ * ((a i : ℂ) * ⟪e i, x⟫_ℂ) =
      (a i : ℂ) * (⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ) by ring]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hinner : (⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ).re =
      ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
    calc
      _ = ‖(⟪x, e i⟫_ℂ * ⟪e i, x⟫_ℂ)‖ :=
        inner_mul_symm_re_eq_norm x (e i)
      _ = ‖(⟪e i, x⟫_ℂ)‖ ^ 2 := by
        rw [norm_mul, norm_inner_symm]
        ring
  rw [hinner]
