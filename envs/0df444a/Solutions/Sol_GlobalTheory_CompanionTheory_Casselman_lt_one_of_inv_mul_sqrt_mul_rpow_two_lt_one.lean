-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:57.644149+00:00
-- url     : https://prove2.me/submissions/fbe2fadc-5b93-4ce7-b473-403649c1f6bb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman
namespace GlobalTheory.CompanionTheory.Casselman
theorem _root_.solution :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith
end GlobalTheory.CompanionTheory.Casselman
