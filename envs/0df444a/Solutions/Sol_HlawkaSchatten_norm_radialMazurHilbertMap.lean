-- Prove2me | solution 1 for HlawkaSchatten.norm_radialMazurHilbertMap
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:52:29.529352+00:00
-- url     : https://prove2.me/submissions/29ce34fa-81fa-40f1-a236-e35c635ba3e3

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HilbertSchmidt
import Definitions.Def_HlawkaSchatten_SchattenNorm
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
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/


open scoped InnerProductSpace

variable {E F : Type*}
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









@[simp]
theorem singularValuePowerSum_zero (p : ℝ) :
    singularValuePowerSum p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [singularValuePowerSum]

@[simp]
theorem schattenPNorm_zero (p : ℝ) (hp : p ≠ 0) :
    schattenPNorm p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [schattenPNorm, hp]



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

@[simp]
theorem radialRectangularMazurMap_zero {p : ℝ} (hp : 0 < p) :
    radialRectangularMazurMap p (0 : E →ₗ[ℂ] F) = 0 := by
  simp [radialRectangularMazurMap, schattenNormalized, schattenPNorm_zero p hp.ne']

@[simp]
theorem radialMazurHilbertMap_zero {p : ℝ} (hp : 0 < p) :
    radialMazurHilbertMap p (0 : E →ₗ[ℂ] F) = 0 := by
  unfold radialMazurHilbertMap
  rw [radialRectangularMazurMap_zero hp]
  exact map_zero (hilbertSchmidtLinearEquiv (stdOrthonormalBasis ℂ E))

theorem solution {p : ℝ} (hp : 0 < p)
    (T : E →ₗ[ℂ] F) :
    ‖radialMazurHilbertMap p T‖ = schattenPNorm p T := by
  by_cases hT : T = 0
  · subst T
    simp [radialMazurHilbertMap_zero hp, schattenPNorm_zero p hp.ne']
  · have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
    have hpow : singularValuePowerSum 2
        (rectangularMazurMap p (schattenNormalized p T)) = 1 := by
      rw [singularValuePowerSum_two_rectangularMazurMap hp]
      exact singularValuePowerSum_normalized hp hT
    have htwo : schattenPNorm 2
        (rectangularMazurMap p (schattenNormalized p T)) = 1 :=
      (schattenPNorm_eq_one_iff (by norm_num) _).mpr hpow
    unfold radialMazurHilbertMap radialRectangularMazurMap
    change ‖((schattenPNorm p T : ℝ) : ℂ) •
      hilbertSchmidtCoordinates (stdOrthonormalBasis ℂ E)
        (rectangularMazurMap p (schattenNormalized p T))‖ = schattenPNorm p T
    rw [norm_smul, ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates,
      htwo, mul_one]
    simp [abs_of_pos hr]
