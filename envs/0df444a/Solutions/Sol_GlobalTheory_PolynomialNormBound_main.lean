-- Prove2me | solution 1 for GlobalTheory.PolynomialNormBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:28:16.481781+00:00
-- url     : https://prove2.me/submissions/eb2c4ddc-328a-4bac-aad8-fd036c6d49bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialNormBound
namespace GlobalTheory.PolynomialNormBound
theorem _root_.solution : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by
  intro l inst j m hj hdvd
  have hl : l.Prime := inst.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one
  have hvm : v < m := by
    by_contra h
    exact hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)
  have hunit : IsUnit (u : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).mpr hu
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩
  have hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  rw [← hw]
  calc (l : ℤ_[l]) ^ v * ↑w * (↑w⁻¹ * (l : ℤ_[l]) ^ (m - 1 - v))
      = (l : ℤ_[l]) ^ v * ((↑w * ↑w⁻¹) * (l : ℤ_[l]) ^ (m - 1 - v)) := by ring
    _ = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by rw [Units.mul_inv, one_mul]
end GlobalTheory.PolynomialNormBound
