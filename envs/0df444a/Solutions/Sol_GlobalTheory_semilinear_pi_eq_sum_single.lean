-- Prove2me | solution 1 for GlobalTheory.semilinear_pi_eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:10.922803+00:00
-- url     : https://prove2.me/submissions/6f335f43-a3e5-4f79-add9-80d56c6b88d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanRangeInfKerEqSpanRationalKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]
end GlobalTheory
