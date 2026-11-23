-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:21.298891+00:00
-- url     : https://prove2.me/submissions/6244c334-5f75-465f-b06c-06cee63e30f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (δ π : K) (k : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) → w δ = 1 → w 4 < w (δ - 1) → w (δ - 1) = WithZero.exp (-(2 * (k : ℤ))) → ∃ c : K, w c = 1 ∧ w (δ * c ^ 2 - 1) < w (δ - 1) := by
  intro K _ w δ π k hπ hres hδ h4 hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have hδ0 : δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hδ
      exact zero_ne_one hδ
    have hinv : w δ⁻¹ = 1 := by rw [map_inv₀, hδ, inv_one]
    obtain ⟨y, hy1, hy⟩ := hres δ⁻¹ hinv.le
    have hy2 : w (y ^ 2) = 1 := by
      have e : y ^ 2 = δ⁻¹ - (δ⁻¹ - y ^ 2) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rwa [hinv]), hinv]
    refine ⟨y, le_antisymm hy1 (not_lt.mp fun hlt => ?_), ?_⟩
    · rw [map_pow] at hy2
      exact (pow_lt_one₀ zero_le' hlt two_ne_zero).ne hy2
    · have e : δ * y ^ 2 - 1 = -(δ * (δ⁻¹ - y ^ 2)) := by
        rw [mul_sub, mul_inv_cancel₀ hδ0]
        ring
      rw [e, Valuation.map_neg, map_mul, hδ, one_mul, hk]
      simpa using hy
  ·

    set t := π ^ k with ht
    set g := w (δ - 1) with hg
    have hgpos : 0 < g := lt_of_le_of_lt zero_le' h4
    have htt : w t * w t = g := by
      show w t * w t = g
      rw [hk, ht, map_pow, hπ, ← pow_add, ← WithZero.exp_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      ring
    have hwt0 : w t ≠ 0 := fun h => hgpos.ne (by simpa [h] using htt)
    have hwtpos : 0 < w t := zero_lt_iff.mpr hwt0
    have ht0 : t ≠ 0 := fun h => hwt0 (by rw [h, map_zero])
    have ht1 : w t < 1 := by
      rw [ht, map_pow, hπ]
      refine pow_lt_one₀ zero_le' ?_ hkpos.ne'
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hg1 : g < 1 := by
      rw [← htt]
      calc w t * w t ≤ w t * 1 := mul_le_mul' le_rfl ht1.le
        _ = w t := mul_one _
        _ < 1 := ht1
    have h2t : w 2 < w t := by
      refine lt_of_not_ge fun h => ?_
      have hle : g ≤ w 4 := by
        rw [← htt, show (4 : K) = 2 * 2 by norm_num, map_mul]
        exact mul_le_mul' h h
      exact absurd h4 (not_lt.mpr hle)
    set x := (δ - 1) * (t ^ 2)⁻¹ with hxdef
    have hx : t ^ 2 * x = δ - 1 := by
      rw [hxdef, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ht0), mul_one]
    have hwx : w (-x) = 1 := by
      rw [Valuation.map_neg, hxdef, map_mul, map_inv₀, map_pow, ← hg, ← htt, sq,
        mul_inv_cancel₀ (mul_ne_zero hwt0 hwt0)]
    obtain ⟨y, hy1, hy⟩ := hres (-x) hwx.le
    refine ⟨1 + t * y, ?_, ?_⟩
    · apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc w t * w y ≤ w t * 1 := mul_le_mul' le_rfl hy1
        _ = w t := mul_one _
        _ < 1 := ht1
    · have e : δ * (1 + t * y) ^ 2 - 1
          = -(t ^ 2 * (-x - y ^ 2)) + 2 * t * y + (δ - 1) * (2 * t * y + t ^ 2 * y ^ 2) := by
        linear_combination (-1 : K) * hx
      rw [e]
      have hA : w (-(t ^ 2 * (-x - y ^ 2))) < g := by
        rw [Valuation.map_neg, map_mul, map_pow, sq, htt]
        calc g * w (-x - y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hy hgpos
          _ = g := mul_one g
      have hB : w (2 * t * y) < g := by
        rw [map_mul, map_mul, ← htt]
        calc w 2 * w t * w y ≤ w 2 * w t * 1 := mul_le_mul' le_rfl hy1
          _ = w 2 * w t := mul_one _
          _ < w t * w t := mul_lt_mul_of_pos_right h2t hwtpos
      have hC : w ((δ - 1) * (2 * t * y + t ^ 2 * y ^ 2)) < g := by
        have hD : w (2 * t * y + t ^ 2 * y ^ 2) < 1 := by
          apply Valuation.map_add_lt
          · exact hB.trans hg1
          · rw [map_mul, map_pow w t, map_pow w y, sq (w t), htt]
            calc g * w y ^ 2 ≤ g * 1 := mul_le_mul' le_rfl (pow_le_one₀ zero_le' hy1)
              _ = g := mul_one g
              _ < 1 := hg1
        rw [map_mul, ← hg]
        calc g * w (2 * t * y + t ^ 2 * y ^ 2) < g * 1 := mul_lt_mul_of_pos_left hD hgpos
          _ = g := mul_one g
      exact Valuation.map_add_lt _ (Valuation.map_add_lt _ hA hB) hC
end GlobalTheory.QNorm
