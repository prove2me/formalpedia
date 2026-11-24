-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.exists_eq_mul_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:50.427833+00:00
-- url     : https://prove2.me/submissions/837f1b75-524e-4c97-998d-8316f9e83b7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard

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
theorem _root_.solution {q d s e l : ℕ} (hq : 2 ≤ q) (hd : 0 < d) (h : s * e = d)
    (hl : l * q ^ e ≡ l [MOD q ^ d - 1]) :
    ∃ k, l = k * ∑ j ∈ Finset.range s, (q ^ e) ^ j := by
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  have hqe : 2 ≤ q ^ e := le_trans hq (Nat.le_self_pow he.ne' q)
  obtain ⟨m, hm⟩ : ∃ m, q ^ e = m + 1 := ⟨q ^ e - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hg := geom_sum_mul_add m s
  have hN : q ^ d - 1 = (∑ j ∈ Finset.range s, (m + 1) ^ j) * m := by
    rw [← h, mul_comm s e, pow_mul, hm, ← hg]; simp
  rw [hN, hm] at hl
  have h2 := (Nat.modEq_iff_dvd' (by nlinarith)).mp hl.symm
  have h3 : l * (m + 1) - l = l * m := by rw [mul_add]; omega
  rw [h3] at h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 h2
  exact ⟨k, by rw [hm, hk, mul_comm]⟩
end GlobalTheory.PeriodDvd
