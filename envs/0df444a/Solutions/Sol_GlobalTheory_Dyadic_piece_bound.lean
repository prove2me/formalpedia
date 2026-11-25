-- Prove2me | solution 1 for GlobalTheory.Dyadic.piece_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:39.621004+00:00
-- url     : https://prove2.me/submissions/03839056-f3e3-4eda-a4c8-28753f8bdce3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution (r kk : ℕ) (H De D l l' u v : ℝ) (hr : 1 ≤ r) (hkk : 1 ≤ kk) (hH : 1 ≤ H)
    (hDe : 1 ≤ De) (hD : 0 < D) (hl : 1 ≤ l) (hl' : 1 ≤ l') (hu : 0 < u) (hv : 0 < v)
    (h1 : (r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u *
      ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) * D ≤ 2 ^ r)
    (h2 : D ≤ (l * l' * H) ^ (2 * r)) :
    ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / u) ^ kk *
        (l ^ (24 * r ^ 3 + 1))⁻¹) *
      ((l * l' * H) ^ (10 * r ^ 3) * ((r * (l * l' * H) ^ (2 * r - 1) * De) ^ r / v) ^ kk *
        (l' ^ (24 * r ^ 3 + 1))⁻¹) ≤
      (r : ℝ) ^ (2 * r) * H ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk *
        (l⁻¹ * l'⁻¹ * u⁻¹ * v⁻¹) := by
  have hR : 1 ≤ l * l' * H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hl hl') hH
  have hRe : (l * l' * H) ^ (24 * r ^ 3) = l ^ (24 * r ^ 3) * l' ^ (24 * r ^ 3) * H ^ (24 * r ^ 3) := by
    rw [mul_pow, mul_pow]
  generalize l * l' * H = R at *
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hT2 : (r * R ^ (2 * r - 1) * De) ^ r * (r * R ^ (2 * r - 1) * De) ^ r * R ^ (2 * r)
      = (r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    generalize ((m + 1 : ℕ) : ℝ) = c
    ring
  have hTpos : 0 < (r * R ^ (2 * r - 1) * De) ^ r := by positivity
  generalize (r * R ^ (2 * r - 1) * De) ^ r = T at *
  set P : ℝ := 2 ^ r / D with hP
  have hPpos : 0 < P := by positivity
  set w : ℝ := T / u * (T / v) with hw
  have hwpos : 0 < w := by positivity
  have hwP : w ≤ P := by rw [hP, le_div_iff₀ hD]; exact h1
  have h3 : w ^ kk ≤ P ^ kk * (T * T * R ^ (2 * r) * (u⁻¹ * v⁻¹)) := by
    obtain ⟨m, rfl⟩ : ∃ m, kk = m + 1 := ⟨kk - 1, by omega⟩
    have h4 : w ^ m ≤ P ^ m := pow_le_pow_left₀ hwpos.le hwP m
    have h5 : 1 ≤ P * R ^ (2 * r) := by
      have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
      calc (1 : ℝ) ≤ 2 ^ r := this
        _ = P * D := by rw [hP]; field_simp
        _ ≤ P * R ^ (2 * r) := by gcongr
    calc w ^ (m + 1) = w ^ m * w * 1 := by ring
      _ ≤ P ^ m * w * (P * R ^ (2 * r)) := by gcongr
      _ = _ := by rw [hw]; ring
  rw [hT2] at h3
  have h6 : R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2) ≤ R ^ (24 * r ^ 3) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hR ?_
    have : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    omega
  have hl0 : 0 < l := by linarith
  have hl0' : 0 < l' := by linarith
  have hR0 : 0 < R := by linarith
  have hDe0 : 0 < De := by linarith
  calc _ = R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * w ^ kk *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by
          rw [hw, mul_pow]; ring
    _ ≤ R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * R ^ (4 * r ^ 2) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = (R ^ (10 * r ^ 3) * R ^ (10 * r ^ 3) * R ^ (4 * r ^ 2)) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by ac_rfl
    _ ≤ R ^ (24 * r ^ 3) * (P ^ kk * ((r : ℝ) ^ (2 * r) * De ^ (2 * r) * (u⁻¹ * v⁻¹))) *
        ((l ^ (24 * r ^ 3 + 1))⁻¹ * (l' ^ (24 * r ^ 3 + 1))⁻¹) := by gcongr
    _ = _ := by
      rw [hRe, pow_succ l, pow_succ l']
      have e1 : 0 < l ^ (24 * r ^ 3) := by positivity
      have e2 : 0 < l' ^ (24 * r ^ 3) := by positivity
      generalize l ^ (24 * r ^ 3) = a at *
      generalize l' ^ (24 * r ^ 3) = b at *
      generalize H ^ (24 * r ^ 3) = c
      generalize P ^ kk = d
      generalize (r : ℝ) ^ (2 * r) = e
      generalize De ^ (2 * r) = f
      field_simp
end GlobalTheory.Dyadic
