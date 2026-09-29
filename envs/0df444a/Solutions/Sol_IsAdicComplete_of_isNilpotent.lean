-- Prove2me | solution 1 for IsAdicComplete.of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/259c012e-c097-57fe-b026-6cd090320c82

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_of_isNilpotent

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  haveI : IsHausdorff I R := ⟨fun x hx => by
    have h := hx N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hN] at h
    exact h⟩
  haveI : IsPrecomplete I R := ⟨fun {f} hf => ⟨f N, fun n => by
    rcases le_or_gt n N with hn | hn
    · exact hf hn
    · have hzero : (I ^ n • ⊤ : Ideal R) = ⊥ := by
        rw [smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
        exact Ideal.pow_le_pow_right hn.le
      rw [SModEq.sub_mem, hzero, Ideal.mem_bot, sub_eq_zero]
      have h := hf hn.le
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hN, Ideal.zero_eq_bot, Ideal.mem_bot,
        sub_eq_zero] at h
      exact h.symm⟩⟩
  exact ⟨⟩

end S_IsAdicComplete_of_isNilpotent
end P2MW
export P2MW.S_IsAdicComplete_of_isNilpotent (solution)
