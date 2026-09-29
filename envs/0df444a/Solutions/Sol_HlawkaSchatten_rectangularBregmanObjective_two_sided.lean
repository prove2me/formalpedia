-- Prove2me | solution 1 for HlawkaSchatten.rectangularBregmanObjective_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T22:49:38.076984+00:00
-- url     : https://prove2.me/submissions/3851aa05-31bd-440d-b29a-caf32e59cbc2

import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_SchattenNorm
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
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]





































































































































/-- Basis-free form of the two-copy rectangular Hilbert--Schmidt formula. -/
theorem dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum'
    (p : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedMazurDistanceSq p S T =
      2 * singularValuePowerSum 2
        (rectangularMazurMap p S - rectangularMazurMap p T) :=
  dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum
    (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F) p S T











end HlawkaSchatten

theorem solution
    (p m M : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    m * rectangularMazurDistanceObjective p a u v ≤
        rectangularBregmanObjective p a u v ∧
      rectangularBregmanObjective p a u v ≤
        M * rectangularMazurDistanceObjective p a u v := by
  have hterm : ∀ i,
      m * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1) ≤
          dilatedBregmanTrace p (u i).1 v.1 / 2 ∧
        dilatedBregmanTrace p (u i).1 v.1 / 2 ≤
          M * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1) := by
    intro i
    have h := hbound (u i).1 v.1
    rw [dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum'] at h
    constructor <;> linarith
  constructor
  · unfold rectangularMazurDistanceObjective rectangularBregmanObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      m * (a i * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) =
          a i * (m * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) := by ring
      _ ≤ a i * (dilatedBregmanTrace p (u i).1 v.1 / 2) :=
        mul_le_mul_of_nonneg_left (hterm i).1 (ha i)
  · unfold rectangularMazurDistanceObjective rectangularBregmanObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      a i * (dilatedBregmanTrace p (u i).1 v.1 / 2) ≤
          a i * (M * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) :=
        mul_le_mul_of_nonneg_left (hterm i).2 (ha i)
      _ = M * (a i * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) := by ring
