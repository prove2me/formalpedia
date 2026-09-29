-- Prove2me | solution 1 for HlawkaSchatten.weightedHilbertObjective_isGlobalMinimumValue
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T23:27:58.626056+00:00
-- url     : https://prove2.me/submissions/66c29ee7-fc86-44ad-ac32-c6b5f5d42bb2

import Definitions.Def_HlawkaSchatten_Basic
import Definitions.Def_HlawkaSchatten_Variational
import Theorems.Thm_HlawkaSchatten_weightedHilbertObjective_eq
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
    [Nonempty ι] (a : ι → ℝ) (u : ι → H)
    (hu : ∀ i, ‖u i‖ = 1) :
    IsGlobalMinimumValue
      (fun v : unitSphere H ↦ weightedHilbertObjective a u v.1)
      (2 * (∑ i, a i - ‖weightedHilbertSum (𝕜 := 𝕜) a u‖)) := by
  let w := weightedHilbertSum (𝕜 := 𝕜) a u
  constructor
  · intro v
    change 2 * (∑ i, a i - ‖w‖) ≤ weightedHilbertObjective a u v.1
    rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u v.1 hu v.property]
    have hinner := re_inner_le_norm (𝕜 := 𝕜) w v.1
    rw [v.property, mul_one] at hinner
    linarith
  · by_cases hw : w = 0
    · let i : ι := Classical.choice inferInstance
      refine ⟨⟨u i, hu i⟩, ?_⟩
      change weightedHilbertObjective a u (u i) =
        2 * (∑ j, a j - ‖w‖)
      rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u (u i) hu (hu i)]
      change 2 * (∑ j, a j - RCLike.re ⟪w, u i⟫_𝕜) =
        2 * (∑ j, a j - ‖w‖)
      rw [hw, inner_zero_left, map_zero, norm_zero]
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      let v : H := ((‖w‖⁻¹ : ℝ) : 𝕜) • w
      have hv : ‖v‖ = 1 := by
        dsimp only [v]
        rw [norm_smul, RCLike.norm_ofReal,
          abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
      refine ⟨⟨v, hv⟩, ?_⟩
      change weightedHilbertObjective a u v =
        2 * (∑ i, a i - ‖w‖)
      rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u v hu hv]
      change 2 * (∑ i, a i - RCLike.re ⟪w, v⟫_𝕜) =
        2 * (∑ i, a i - ‖w‖)
      have hinner : RCLike.re ⟪w, v⟫_𝕜 = ‖w‖ := by
        dsimp only [v]
        rw [inner_smul_right, RCLike.re_ofReal_mul,
          ← norm_sq_eq_re_inner (𝕜 := 𝕜) w]
        field_simp
      rw [hinner]
