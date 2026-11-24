-- Prove2me | solution 1 for GlobalTheory.wittVector_dvd_of_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:35.428434+00:00
-- url     : https://prove2.me/submissions/4b8e9483-f480-458f-925b-54ae84b8e40b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] [PerfectRing R l] (x : WittVector l R) (hx : x.coeff 0 = 0) :
    ∃ y, x = (l : WittVector l R) * y := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := exists_eq_pow_p_mul x h
  cases m with
  | zero => rw [pow_zero, one_mul] at hxb; exact absurd (hxb ▸ hx) hb
  | succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩
end GlobalTheory
