-- Prove2me | solution 1 for GlobalTheory.PrimeElement.exists_eq_of_pow_mul_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:51.461933+00:00
-- url     : https://prove2.me/submissions/abf79362-6016-4270-9331-5352f1cc1af9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
namespace GlobalTheory.PrimeElement
theorem _root_.solution {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    [FaithfulSMul R K] (hπ : Prime π) {x : K} {n : ℕ} {a b c : R}
    (ha : algebraMap R K (π ^ n) * x = algebraMap R K a) (hb : ¬ π ∣ b)
    (hc : algebraMap R K b * x = algebraMap R K c) : ∃ r : R, algebraMap R K r = x := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have := hinj.isDomain
  have h : b * a = π ^ n * c := hinj <| by
    rw [map_mul, map_mul, ← ha, ← hc]; ring
  obtain ⟨r, rfl⟩ : π ^ n ∣ a := hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩
  refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩
  rw [ha, map_mul]
end GlobalTheory.PrimeElement
