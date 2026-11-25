-- Prove2me | solution 1 for GlobalTheory.Nef.PlaceResiduePowerBound.pow_of_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:11.014226+00:00
-- url     : https://prove2.me/submissions/39e187e5-b8d8-45a8-a3ce-fb41a2d7d074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.PlaceResiduePowerBound
theorem _root_.solution (v q : Valuation F ℤᵐ⁰) (hq : Function.Surjective q)
    (h : ∀ x, v x ≤ 1 ↔ q x ≤ 1) : ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  obtain ⟨π, hπ⟩ := hq (exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).2 hπ0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, v π = exp b := ⟨log (v π), (exp_log hvπ0).symm⟩
  have hb0 : b < 0 := by
    have h1 : v π ≤ 1 := (h π).2 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
    have h2 : v π ≠ 1 := by
      intro h1'
      have : q π⁻¹ ≤ 1 := (h _).1 (by rw [map_inv₀, h1', inv_one])
      rw [map_inv₀, hπ, ← exp_neg, ← exp_zero, exp_le_exp] at this
      norm_num at this
    rw [hb, ← exp_zero, exp_le_exp] at h1
    rw [hb, ne_eq, exp_eq_one] at h2
    omega
  have hbe : (((-b).toNat : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  refine ⟨(-b).toNat, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, zero_pow (by omega)]
  have hqx : q x ≠ 0 := (Valuation.ne_zero_iff q).2 hx
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
  obtain ⟨c, hc⟩ : ∃ c : ℤ, q x = exp c := ⟨log (q x), (exp_log hqx).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a := ⟨log (v x), (exp_log hvx).symm⟩
  have hqu : q (x * π ^ c) = 1 := by
    rw [map_mul, map_zpow₀, hc, hπ, ← exp_zsmul, ← exp_add, exp_eq_one, smul_eq_mul]; ring
  have hvu : v (x * π ^ c) = exp (a + c * b) := by
    rw [map_mul, map_zpow₀, ha, hb, ← exp_zsmul, ← exp_add, smul_eq_mul]
  have h1 : v (x * π ^ c) ≤ 1 := (h _).2 hqu.le
  have h2 : v (x * π ^ c)⁻¹ ≤ 1 := (h _).2 (by rw [map_inv₀, hqu, inv_one])
  rw [hvu, ← exp_zero, exp_le_exp] at h1
  rw [map_inv₀, hvu, ← exp_neg, ← exp_zero, exp_le_exp] at h2
  have h3 : a + c * b = 0 := by omega
  rw [ha, hc, ← exp_nsmul, exp_inj, nsmul_eq_mul, hbe]
  linear_combination h3
end GlobalTheory.Nef.PlaceResiduePowerBound
