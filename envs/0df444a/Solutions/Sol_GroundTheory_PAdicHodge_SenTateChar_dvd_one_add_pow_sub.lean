-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.dvd_one_add_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:13.826441+00:00
-- url     : https://prove2.me/submissions/604517de-7060-4264-8ad1-8c5e0b229242

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) {x : ℤ_[p]} (hx : (p : ℤ_[p]) ^ k ∣ x) :
    (p : ℤ_[p]) ^ (k + 2) ∣ (1 + x) ^ p - 1 - p * x := by
  obtain ⟨c, rfl⟩ := hx
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [add_comm (1 : ℤ_[p]), add_pow]
  have hsplit : ∑ m ∈ Finset.range (p + 1),
      ((p : ℤ_[p]) ^ k * c) ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) =
      1 + p * ((p : ℤ_[p]) ^ k * c) +
        ∑ m ∈ Finset.Ico 2 (p + 1), ((p : ℤ_[p]) ^ k * c) ^ m * (p.choose m : ℤ_[p]) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by omega)
      (by omega : 2 ≤ p + 1)]
    simp only [one_pow, mul_one]
    rw [show Finset.Ico 0 2 = {0, 1} by decide, Finset.sum_pair (by norm_num)]
    simp [Nat.choose_one_right]
    ring
  rw [hsplit]
  have e : 1 + ↑p * (↑p ^ k * c) +
      ∑ m ∈ Finset.Ico 2 (p + 1), (↑p ^ k * c) ^ m * (p.choose m : ℤ_[p]) - 1 - ↑p * (↑p ^ k * c) =
      ∑ m ∈ Finset.Ico 2 (p + 1), ((p : ℤ_[p]) ^ k * c) ^ m * (p.choose m : ℤ_[p]) := by
    ring
  rw [e]
  refine Finset.dvd_sum fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  rw [mul_pow, ← pow_mul]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hm.2) with hmp | hmp
  ·
    have hch : (p : ℤ_[p]) ∣ (p.choose m : ℤ_[p]) := by
      exact Nat.cast_dvd_cast (hp.out.dvd_choose_self (by omega : m ≠ 0) hmp)
    have h1 : (p : ℤ_[p]) ^ (k + 1) ∣ (p : ℤ_[p]) ^ (k * m) :=
      pow_dvd_pow _ (by nlinarith)
    calc (p : ℤ_[p]) ^ (k + 2) = (p : ℤ_[p]) ^ (k + 1) * p := by ring
      _ ∣ (p : ℤ_[p]) ^ (k * m) * c ^ m * (p.choose m : ℤ_[p]) :=
        mul_dvd_mul (h1.mul_right _) hch
  ·
    rw [hmp]
    have h1 : (p : ℤ_[p]) ^ (k + 2) ∣ (p : ℤ_[p]) ^ (k * p) := pow_dvd_pow _ (by nlinarith)
    exact (h1.mul_right _).mul_right _
end GroundTheory.PAdicHodge.SenTateChar
