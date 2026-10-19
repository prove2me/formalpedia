-- Prove2me | solution 1 for MazurTransfer.Order13ReflectionParameterArithmetic.parameter_quadratic_thirteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:16:46.762837+00:00
-- url     : https://prove2.me/submissions/dae839e1-7f58-4c32-97e3-dd32d4a77f3c

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: checked algebraic coefficient identities for the reflection,
including its diamond orbit and its quadratic coefficient over the cubic field.
Named downstream consumer: the Galois orbit of the actual reflection, used
to identify the cyclotomic quotient kernel's arithmetic character.
-/

noncomputable section
universe u
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter
namespace MazurTransfer.ReflectionQuadraticThirteenProofHelpers20261018
variable {K : Type u} [Field K]

theorem quadratic_thirteen_certificate (t : K) :
    (3 * t ^ 2 + 8 * t + 1) ^ 2 - 13 * reflectionScalar t =
      3 * (3 * t + 4) * reflectionCubic t := by
  dsimp [reflectionScalar, reflectionCubic]
  ring

end MazurTransfer.ReflectionQuadraticThirteenProofHelpers20261018

theorem solution {K : Type u} [Field K] (a : ReflectionParameter K) :
    (3 * a.t ^ 2 + 8 * a.t + 1) ^ 2 = 13 * a.s ^ 2 := by
  have h := MazurTransfer.ReflectionQuadraticThirteenProofHelpers20261018.quadratic_thirteen_certificate a.t
  rw [a.cubic_eq_zero, mul_zero, ← a.square_eq_scalar] at h
  exact sub_eq_zero.mp h

#print axioms solution
