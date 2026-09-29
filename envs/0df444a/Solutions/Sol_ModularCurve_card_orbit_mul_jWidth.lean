-- Prove2me | solution 1 for ModularCurve.card_orbit_mul_jWidth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f5c510ea-2216-5922-af65-55ede661d378

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_legendreJ_eq_zero_iff
import Theorems.Thm_ModularCurve_legendreJ_eq_ofNat_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_orbit_mul_jWidth

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ jWidth legendreJ_eq_zero_iff legendreJ_eq_ofNat_iff"
p2m_open "ModularCurve"

theorem card_orbit_eq_six' {K : Type*} [Field K] [DecidableEq K] {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (hA : t ≠ -1) (hB : t ≠ 2) (hC : t ≠ 2⁻¹) (hD : t ^ 2 - t + 1 ≠ 0) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card = 6 := by
  have h1t : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  have hw : (1 - t) * (1 - t)⁻¹ = 1 := mul_inv_cancel₀ h1t
  have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hA' : t + 1 ≠ 0 := fun h => hA (add_eq_zero_iff_eq_neg.mp h)
  have hB' : t - 2 ≠ 0 := fun h => hB (sub_eq_zero.mp h)
  have hC' : 2 * t - 1 ≠ 0 := fun h => hC (eq_inv_of_mul_eq_one_right (by linear_combination h))
  have hAA : (t - 1) * (t + 1) ≠ 0 := mul_ne_zero ht1' hA'
  have hBB : t * (t - 2) ≠ 0 := mul_ne_zero ht0 hB'
  have d12 : (t : K) ≠ 1 - t := fun h => hC' (by linear_combination (1) * h)
  have d13 : (t : K) ≠ t⁻¹ := fun h => hAA (by linear_combination (t) * h + (1) * hi)
  have d14 : (t : K) ≠ 1 - t⁻¹ := fun h => hD (by linear_combination (t) * h + (-1) * hi)
  have d15 : (t : K) ≠ (1 - t)⁻¹ := fun h => hD (by linear_combination (t - 1) * h + (-1) * hw)
  have d16 : (t : K) ≠ 1 - (1 - t)⁻¹ := fun h => hBB (by linear_combination (t - 1) * h + (1) * hw)
  have d23 : (1 - t : K) ≠ t⁻¹ := fun h => hD (by linear_combination (-t) * h + (-1) * hi)
  have d24 : (1 - t : K) ≠ 1 - t⁻¹ := fun h => hAA (by linear_combination (-t) * h + (1) * hi)
  have d25 : (1 - t : K) ≠ (1 - t)⁻¹ := fun h => hBB (by linear_combination (1 - t) * h + (1) * hw)
  have d26 : (1 - t : K) ≠ 1 - (1 - t)⁻¹ := fun h => hD (by linear_combination (1 - t) * h + (-1) * hw)
  have d34 : (t⁻¹ : K) ≠ 1 - t⁻¹ := fun h => hB' (by linear_combination (-t) * h + (2) * hi)
  have d35 : (t⁻¹ : K) ≠ (1 - t)⁻¹ := fun h => hC' (by linear_combination (t^2 - t) * h + (1 - t) * hi + (-t) * hw)
  have d36 : (t⁻¹ : K) ≠ 1 - (1 - t)⁻¹ := fun h => hD (by linear_combination (-t^2 + t) * h + (t - 1) * hi + (-t) * hw)
  have d45 : (1 - t⁻¹ : K) ≠ (1 - t)⁻¹ := fun h => hD (by linear_combination (t^2 - t) * h + (t - 1) * hi + (-t) * hw)
  have d46 : (1 - t⁻¹ : K) ≠ 1 - (1 - t)⁻¹ := fun h => hC' (by linear_combination (-t^2 + t) * h + (1 - t) * hi + (-t) * hw)
  have d56 : ((1 - t)⁻¹ : K) ≠ 1 - (1 - t)⁻¹ := fun h => hA' (by linear_combination (1 - t) * h + (-2) * hw)
  have n1 : t ∉ ({1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d12, d13, d14, d15, d16⟩
  have n2 : 1 - t ∉ ({t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d23, d24, d25, d26⟩
  have n3 : t⁻¹ ∉ ({1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d34, d35, d36⟩
  have n4 : 1 - t⁻¹ ∉ ({(1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d45, d46⟩
  rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
    Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_pair d56]

theorem card_orbit_eq_two' {K : Type*} [Field K] [DecidableEq K] (h3 : (3 : K) ≠ 0) {t : K}
    (hD : t ^ 2 - t + 1 = 0) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card = 2 := by
  have e3 : t⁻¹ = 1 - t := inv_eq_of_mul_eq_one_right (by linear_combination -hD)
  have e5 : (1 - t)⁻¹ = t := inv_eq_of_mul_eq_one_right (by linear_combination -hD)
  have d12 : t ≠ 1 - t := fun h => h3 (by linear_combination 4 * hD - (2 * t - 1) * h)
  have : ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) = {t, 1 - t} := by
    ext x
    rw [e3, e5, sub_sub_cancel]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [this, Finset.card_pair d12]

theorem card_eq_three_of_forall_mem_iff' {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (l : Finset K) (hl : ∀ x, x ∈ l ↔ x = -1 ∨ x = 2 ∨ x = 2⁻¹) :
    l.card = 3 := by
  have n12 : (-1 : K) ≠ 2 := fun h => h3 (by linear_combination -h)
  have n13 : (-1 : K) ≠ 2⁻¹ := fun h => by
    have : (-1 : K) * 2 = 1 := by rw [h, inv_mul_cancel₀ h2]
    exact h3 (by linear_combination -this)
  have n23 : (2 : K) ≠ 2⁻¹ := fun h => by
    have : (2 : K) * 2 = 1 := by rw [← inv_mul_cancel₀ h2, ← h]
    exact h3 (by linear_combination this)
  have : l = {-1, 2, 2⁻¹} := by
    ext x; rw [hl]; simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [this, Finset.card_insert_of_notMem, Finset.card_pair n23]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨n12, n13⟩

theorem card_orbit_eq_three' {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {t : K} (hT : t = -1 ∨ t = 2 ∨ t = 2⁻¹) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card = 3 := by
  have eh : (1 : K) - 2⁻¹ = 2⁻¹ := by
    rw [sub_eq_iff_eq_add, ← two_mul, mul_inv_cancel₀ h2]
  have f1 : (1 : K) - -1 = 2 := by norm_num
  have f2 : (-1 : K)⁻¹ = -1 := by norm_num
  have g1 : (1 : K) - 2 = -1 := by norm_num
  apply card_eq_three_of_forall_mem_iff' h2 h3
  intro x
  rcases hT with rfl | rfl | rfl
  · rw [f2, f1, eh]
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [g1, f2, f1, eh]
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [eh, inv_inv, g1]
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem card_orbit_mul_jWidth' {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card * jWidth (legendreJ t)
      = 6 := by
  by_cases hD : t ^ 2 - t + 1 = 0
  · rw [card_orbit_eq_two' h3 hD, (legendreJ_eq_zero_iff h2 ht0 ht1).mpr hD, jWidth, if_pos rfl]
  by_cases hT : t = -1 ∨ t = 2 ∨ t = 2⁻¹
  · have hj : legendreJ t = 1728 := (legendreJ_eq_ofNat_iff h2 ht0 ht1).mpr hT
    have h1728 : (1728 : K) ≠ 0 := by
      rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    rw [card_orbit_eq_three' h2 h3 hT, hj, jWidth, if_neg h1728, if_pos rfl]
  have hj0 : legendreJ t ≠ 0 := fun h => hD ((legendreJ_eq_zero_iff h2 ht0 ht1).mp h)
  have hj1 : legendreJ t ≠ 1728 := fun h => hT ((legendreJ_eq_ofNat_iff h2 ht0 ht1).mp h)
  simp only [not_or] at hT
  rw [card_orbit_eq_six' ht0 ht1 hT.1 hT.2.1 hT.2.2 hD, jWidth, if_neg hj0, if_neg hj1]

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_card_orbit_mul_jWidth.ModularCurve"

theorem solution {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card * jWidth (legendreJ t)
      = 6 :=
  ModularCurve.card_orbit_mul_jWidth' h2 h3 ht0 ht1

end S_ModularCurve_card_orbit_mul_jWidth
end P2MW
export P2MW.S_ModularCurve_card_orbit_mul_jWidth (solution)
