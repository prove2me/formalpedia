-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.exists_eq_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:13.182814+00:00
-- url     : https://prove2.me/submissions/a874523b-d761-40fc-9e78-695c2f894bdc

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
theorem _root_.solution {f : R⟦X⟧} (hf : f ≠ 0) :
    ∃ (a : ℕ) (f₁ : R⟦X⟧), ¬ (X : R⟦X⟧) ∣ f₁ ∧ f = X ^ a * f₁ := by
  obtain ⟨f₁, hf₁⟩ := X_pow_order_dvd (φ := f)
  refine ⟨f.order.toNat, f₁, ?_, hf₁⟩
  rintro ⟨e, he⟩
  have hd : (X : R⟦X⟧) ^ (f.order.toNat + 1) ∣ f := ⟨e, by rw [pow_succ, mul_assoc, ← he, ← hf₁]⟩
  rw [X_pow_dvd_iff] at hd
  exact coeff_order hf (hd _ (Nat.lt_succ_self _))
end GlobalTheory.PowerSeriesNormal
