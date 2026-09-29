-- Prove2me | solution 1 for HlawkaSchatten.rectangularMazurDistanceObjective_isGlobalMinimumValue
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T23:33:52.695679+00:00
-- url     : https://prove2.me/submissions/8b4e91ea-4117-4afa-a514-0ce9e07b60fa

import Definitions.Def_HlawkaSchatten_Basic
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HilbertSchmidt
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_Variational
import Theorems.Thm_HlawkaSchatten_weightedHilbertObjective_isGlobalMinimumValue
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











section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite-dimensional Schatten quantities

This file gives the definition needed by the Hlawka boundary. Mathlib's
singular-value sequence is finitely supported, so the power sum is finite
without choosing bases or matrix dimensions.
-/

namespace HlawkaSchatten

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]









theorem schattenPNorm_nonneg (p : ℝ) (T : E →ₗ[𝕜] F) :
    0 ≤ schattenPNorm p T :=
  Real.rpow_nonneg (singularValuePowerSum_nonneg p T) _















/-- Squaring the Schatten-2 quantity recovers its power sum. -/
theorem schattenPNorm_two_sq (T : E →ₗ[𝕜] F) :
    schattenPNorm 2 T ^ 2 = singularValuePowerSum 2 T := by
  unfold schattenPNorm
  norm_num
  convert Real.rpow_inv_natCast_pow (singularValuePowerSum_nonneg 2 T)
    (by norm_num : (2 : ℕ) ≠ 0) using 1
  norm_num

end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The Schatten-2 quantity as a Hilbert norm

This file realizes a finite-dimensional linear map by its values on an
orthonormal basis.  At exponent two, this coordinate map is an isometry for
the Schatten quantity defined from singular values.  Consequently the
Schatten-2 quantity satisfies Hlawka's inequality with constant one.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]









/-- The Schatten-2 quantity is exactly the Hilbert norm of the column
coordinate family. -/
theorem schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates
    (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] F) :
    schattenPNorm 2 T = ‖hilbertSchmidtCoordinates e T‖ := by
  rw [← sq_eq_sq₀ (schattenPNorm_nonneg 2 T) (norm_nonneg _),
    schattenPNorm_two_sq, PiLp.norm_sq_eq_of_L2]
  exact singularValuePowerSum_two_eq_sum_norm_sq e T







end HlawkaSchatten

/-- Global minimum values are unchanged by reparametrizing the domain by an
equivalence. -/
theorem isGlobalMinimumValue_comp_equiv
    {A B : Type*} (e : A ≃ B) (f : B → ℝ) (value : ℝ) :
    IsGlobalMinimumValue (f ∘ e) value ↔ IsGlobalMinimumValue f value := by
  constructor
  · rintro ⟨hlower, ⟨x, hx⟩⟩
    refine ⟨fun y ↦ ?_, ⟨e x, hx⟩⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using hlower (e.symm y)
  · rintro ⟨hlower, ⟨y, hy⟩⟩
    refine ⟨fun x ↦ hlower (e x), ⟨e.symm y, ?_⟩⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using hy

/-- The rectangular Mazur distance objective is precisely the weighted
Hilbert squared-distance objective in column coordinates. -/
theorem rectangularMazurDistanceObjective_eq_weightedHilbertObjective
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p)
    (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    rectangularMazurDistanceObjective p a u v =
      weightedHilbertObjective a
        (fun i => (rectangularMazurHilbertSphereEquiv e hp (u i)).1)
        (rectangularMazurHilbertSphereEquiv e hp v).1 := by
  unfold rectangularMazurDistanceObjective weightedHilbertObjective
    rectangularMazurHilbertSphereEquiv
  apply Fintype.sum_congr
  intro i
  congr 1
  rw [singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e]
  rfl

/-- Hilbert coordinates carry the weighted Mazur-image barycenter to the
weighted sum of the corresponding unit vectors. -/
theorem weightedHilbertSum_rectangularMazur_eq
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p)
    (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    weightedHilbertSum (𝕜 := ℂ) a
        (fun i => (rectangularMazurHilbertSphereEquiv e hp (u i)).1) =
      hilbertSchmidtCoordinates e (rectangularMazurBarycenter p a u) := by
  unfold weightedHilbertSum rectangularMazurHilbertSphereEquiv
    rectangularMazurBarycenter
  change (∑ i, (a i : ℂ) • hilbertSchmidtCoordinates e
    (rectangularMazurMap p (u i).1)) =
    hilbertSchmidtCoordinates e
      (∑ i, (a i : ℂ) • rectangularMazurMap p (u i).1)
  exact (map_sum (hilbertSchmidtLinearEquiv e)
    (fun i => (a i : ℂ) • rectangularMazurMap p (u i).1) Finset.univ).symm

theorem solution
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p : ℝ} (hp : 0 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularMazurDistanceObjective p a u)
      (2 * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u))) := by
  let mazur : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p ≃
      unitSphere (PiLp 2 (fun _ : κ => F)) :=
    rectangularMazurHilbertSphereEquiv (F := F) e hp
  have hu : ∀ i, ‖(mazur (u i)).1‖ = 1 :=
    fun i => (mazur (u i)).property
  have h := weightedHilbertObjective_isGlobalMinimumValue (𝕜 := ℂ)
    a (fun i => (mazur (u i)).1) hu
  have hc := (isGlobalMinimumValue_comp_equiv mazur
    (fun v : unitSphere (PiLp 2 (fun _ : κ => F)) =>
      weightedHilbertObjective a (fun i => (mazur (u i)).1) v.1)
    (2 * (∑ i, a i -
      ‖weightedHilbertSum (𝕜 := ℂ) a (fun i => (mazur (u i)).1)‖))).mpr h
  change IsGlobalMinimumValue
    (fun v => weightedHilbertObjective a
      (fun i => (mazur (u i)).1) (mazur v).1)
    (2 * (∑ i, a i -
      ‖weightedHilbertSum (𝕜 := ℂ) a (fun i => (mazur (u i)).1)‖)) at hc
  rw [show (fun v => weightedHilbertObjective a
      (fun i => (mazur (u i)).1) (mazur v).1) =
        rectangularMazurDistanceObjective p a u by
      funext v
      exact (rectangularMazurDistanceObjective_eq_weightedHilbertObjective
        e hp a u v).symm] at hc
  rw [show weightedHilbertSum (𝕜 := ℂ) a
      (fun i => (mazur (u i)).1) =
        hilbertSchmidtCoordinates e (rectangularMazurBarycenter p a u) from
      weightedHilbertSum_rectangularMazur_eq e hp a u,
    ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates e] at hc
  exact hc
