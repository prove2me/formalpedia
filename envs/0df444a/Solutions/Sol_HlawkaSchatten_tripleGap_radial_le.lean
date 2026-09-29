-- Prove2me | solution 1 for HlawkaSchatten.tripleGap_radial_le
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T00:53:24.713265+00:00
-- url     : https://prove2.me/submissions/4eb03fd1-8479-43c2-95ec-65a153931478

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HilbertSchmidt
import Definitions.Def_HlawkaSchatten_MazurGapComparison
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Theorems.Thm_HlawkaSchatten_finiteFamilyGap_two_sided
import Theorems.Thm_HlawkaSchatten_pairGap_radial_two_sided
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

/-- The three-operator specialization of the unnormalized variational gap. -/
theorem tripleGap_radial_two_sided_of_ne
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y z : E →ₗ[ℂ] F) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z ≤
        tripleGap (schattenPNorm p) x y z ∧
      tripleGap (schattenPNorm p) x y z ≤
        2 * M * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z := by
  have h := finiteFamilyGap_two_sided hp hm
    (![x, y, z] : Fin 3 → E →ₗ[ℂ] F)
    (by intro i; fin_cases i <;> assumption) hbound
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at h
  dsimp only [tripleGap, mappedTripleGap, radialMazurHilbertMap]
  simpa only [← hilbertSchmidtCoordinates_add,
    ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates, add_assoc] using h

theorem solution
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y z : E →ₗ[ℂ] F)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    tripleGap (schattenPNorm p) x y z ≤
      2 * M * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    have h := (pairGap_radial_two_sided hp hm y z hbound).2
    simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
      schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
  · by_cases hy : y = 0
    · subst y
      have h := (pairGap_radial_two_sided hp hm x z hbound).2
      simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
        schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
    · by_cases hz : z = 0
      · subst z
        have h := (pairGap_radial_two_sided hp hm x y hbound).2
        simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
          schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
      · exact (tripleGap_radial_two_sided_of_ne hp hm x y z hx hy hz hbound).2
