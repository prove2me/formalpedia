-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.dvd_of_dvd_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:30.271576+00:00
-- url     : https://prove2.me/submissions/6dbd9bc3-e321-446b-8742-6d9d3e53a34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.PowerSeriesNormal
theorem _root_.solution {u a : R⟦X⟧} (hu : ¬ (X : R⟦X⟧) ∣ u) {c : ℕ}
    (h : u ∣ X ^ c * a) : u ∣ a := by
  induction c generalizing a with
  | zero => simpa using h
  | succ c ih =>
    apply ih
    obtain ⟨v, hv⟩ := h
    have hXv : (X : R⟦X⟧) ∣ u * v := ⟨X ^ c * a, by rw [← hv]; ring⟩
    rcases X_prime.dvd_or_dvd hXv with hu' | ⟨w, hw⟩
    · exact absurd hu' hu
    · refine ⟨w, mul_left_cancel₀ (X_ne_zero (R := R)) ?_⟩
      calc X * (X ^ c * a) = X ^ (c + 1) * a := by ring
        _ = u * v := hv
        _ = X * (u * w) := by rw [hw]; ring
end GlobalTheory.PowerSeriesNormal
