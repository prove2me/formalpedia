-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:25.425847+00:00
-- url     : https://prove2.me/submissions/4aa73ea8-2aec-4efd-84c0-a7a8a94e96ad

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntFac
namespace GlobalTheory.CompanionTheory.IntFac
theorem _root_.solution (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ k, IsIntegral ℂ (F.coeff k)) (u : ℂ) : IsIntegral ℂ (F.eval (algebraMap ℂ A u)) := by
  rw [eval_eq_sum_range]
  exact IsIntegral.sum _ fun i _ => (h i).mul (isIntegral_algebraMap.pow _)
end GlobalTheory.CompanionTheory.IntFac
