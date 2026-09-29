-- Prove2me | solution 1 for HlawkaSchatten.weightedHilbertObjective_eq
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T23:21:28.16357+00:00
-- url     : https://prove2.me/submissions/d018a7ba-510f-48fc-a6a4-5b721c9100d3

import Definitions.Def_HlawkaSchatten_Variational
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/


open scoped InnerProductSpace ComplexConjugate







variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open HlawkaSchatten

theorem solution
    (a : ι → ℝ) (u : ι → H) (v : H)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ‖v‖ = 1) :
    weightedHilbertObjective a u v =
      2 * (∑ i, a i -
        RCLike.re ⟪weightedHilbertSum (𝕜 := 𝕜) a u, v⟫_𝕜) := by
  unfold weightedHilbertObjective weightedHilbertSum
  simp_rw [norm_sub_sq (𝕜 := 𝕜), hu, hv, one_pow]
  rw [sum_inner, map_sum]
  simp only [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  have hterm : ∀ i, a i * (1 - 2 * RCLike.re ⟪u i, v⟫_𝕜 + 1) =
      2 * a i - 2 * (a i * RCLike.re ⟪u i, v⟫_𝕜) := by
    intro i
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring
