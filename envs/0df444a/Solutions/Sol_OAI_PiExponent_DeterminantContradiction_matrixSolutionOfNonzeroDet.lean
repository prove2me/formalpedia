-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.matrixSolutionOfNonzeroDet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:22:48.748009+00:00
-- url     : https://prove2.me/submissions/29546dba-45e3-4849-b52e-dbd0ff93f7fa

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (A : Matrix iota iota Complex) (hA : A.det ≠ 0) (y : iota → Complex) :
    ∃ x : iota → Complex, ∀ i : iota, ∑ j : iota, A i j * x j = y i := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hdet
  obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit).2 hunit y
  refine ⟨x, ?_⟩
  intro i
  simpa [Matrix.mulVec, dotProduct] using congrFun hx i