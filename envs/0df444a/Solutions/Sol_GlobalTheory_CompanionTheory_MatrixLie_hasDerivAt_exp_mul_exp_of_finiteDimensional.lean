-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixLie.hasDerivAt_exp_mul_exp_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:42.178328+00:00
-- url     : https://prove2.me/submissions/a3c1992d-0ed6-4d41-a875-cdb443739c8d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixLie
namespace GlobalTheory.CompanionTheory.MatrixLie
theorem _root_.solution {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y)) (X + Y) 0 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  have hX := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hY := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  have hXY := hX.mul hY
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hXY
  exact hXY
end GlobalTheory.CompanionTheory.MatrixLie
