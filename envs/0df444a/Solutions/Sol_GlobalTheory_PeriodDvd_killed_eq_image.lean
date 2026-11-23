-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.killed_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:03.342853+00:00
-- url     : https://prove2.me/submissions/0d8a5a2e-e5fa-469e-9bfc-650ec523aa4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    killed d s = (Finset.range s).image fun j => ((e * j : ℕ) : ZMod d) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hs : 0 < s := Nat.pos_of_mul_pos_right (h ▸ hd)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  ext x
  rw [mem_killed, Finset.mem_image]
  constructor
  · intro hx
    have h1 : ((s * x.val : ℕ) : ZMod d) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hx]
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : s * e ∣ s * x.val := by rw [h]; exact h1
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left hs h2
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h3 := ZMod.val_lt x
      rw [hj] at h3
      by_contra hc
      have : e * s ≤ e * j := Nat.mul_le_mul_left _ (not_lt.mp hc)
      nlinarith
    · rw [← hj, ZMod.natCast_zmod_val]
  · rintro ⟨j, -, rfl⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← mul_assoc, h, Nat.cast_mul, ZMod.natCast_self, zero_mul]
end GlobalTheory.PeriodDvd
