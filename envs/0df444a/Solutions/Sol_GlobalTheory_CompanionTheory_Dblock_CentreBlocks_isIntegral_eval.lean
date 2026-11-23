-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.isIntegral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:55.54604+00:00
-- url     : https://prove2.me/submissions/ca5e9cee-ab2e-48d7-bbc0-e9fe86ebcfcd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
theorem _root_.solution {A : Type} [CommRing A] [Algebra ℂ A] (P : A[X])
    (h : ∀ k, IsIntegral ℂ (P.coeff k)) (x : A) (hx : IsIntegral ℂ x) :
    IsIntegral ℂ (P.eval x) := by
  rw [Polynomial.eval_eq_sum_range]
  exact (integralClosure ℂ A).sum_mem fun i _ =>
    (integralClosure ℂ A).mul_mem (h i) ((integralClosure ℂ A).pow_mem hx _)
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
