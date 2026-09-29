-- Prove2me | solution 1 for HlawkaSchatten.dilatedBregmanTrace_self
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:25:47.747345+00:00
-- url     : https://prove2.me/submissions/b227e7ac-6105-434b-9b5d-7c418f3a3191

import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_ScalarBregman
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
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
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
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

















































































/-- Operator-functional-calculus form of the canonical Hermitian Bregman
quantity. This is the form used by the rectangular dilation step. -/
theorem hermitianBregmanTrace_eq_functionalCalculus [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianBregmanTrace p A B hA hB =
      ((hermitianFunctionalCalculus (powerPotential p) A hA).trace ℂ E).re -
      ((hermitianFunctionalCalculus (powerPotential p) B hB).trace ℂ E).re -
      ((A.comp (hermitianFunctionalCalculus (powerGradient p) B hB)).trace ℂ E).re +
      ((hermitianFunctionalCalculus
        (fun x ↦ powerGradient p x * x) B hB).trace ℂ E).re := by
  unfold hermitianBregmanTrace spectralBregmanTrace hermitianFunctionalCalculus
  rw [spectralDiagonal_eigenvectorBasis_eq A hA]
  congr 3

















end HlawkaSchatten

@[simp]
theorem solution (p : ℝ) (S : E →ₗ[ℂ] F) :
    dilatedBregmanTrace p S S = 0 := by
  unfold dilatedBregmanTrace
  rw [hermitianBregmanTrace_eq_functionalCalculus]
  have hcross : hermitianFunctionalCalculus
      (fun x => powerGradient p x * x) (hermitianDilation S)
        (hermitianDilation_isSymmetric S) =
      (hermitianDilation S).comp
        (hermitianFunctionalCalculus (powerGradient p) (hermitianDilation S)
          (hermitianDilation_isSymmetric S)) := by
    rw [show (fun x => powerGradient p x * x) =
        (fun x => x * powerGradient p x) by funext x; ring,
      hermitianFunctionalCalculus_mul]
    rw [show (fun x : ℝ => x) = id by rfl,
      hermitianFunctionalCalculus_id]
  rw [hcross]
  ring
