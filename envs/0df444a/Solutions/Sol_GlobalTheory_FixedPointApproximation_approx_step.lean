-- Prove2me | solution 1 for GlobalTheory.FixedPointApproximation.approx_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:45.821676+00:00
-- url     : https://prove2.me/submissions/75c6f99e-2345-4abd-96d3-47811ab2d1e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ApproxStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FixedPointApproximation
namespace GlobalTheory.FixedPointApproximation
theorem _root_.solution {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring
end GlobalTheory.FixedPointApproximation
