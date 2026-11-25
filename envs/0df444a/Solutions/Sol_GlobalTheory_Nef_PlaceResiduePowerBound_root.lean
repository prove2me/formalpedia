-- Prove2me | solution 1 for GlobalTheory.Nef.PlaceResiduePowerBound.root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:47.583246+00:00
-- url     : https://prove2.me/submissions/3b145582-fd83-4545-affd-2967ac4abe00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
import Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_pow_inj

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
theorem _root_.solution (v : Valuation F ℤᵐ⁰) (hv : ∃ a, 1 < v a) :
    ∃ q : Valuation F ℤᵐ⁰, Function.Surjective q ∧ ∃ e : ℕ, 0 < e ∧ ∀ x, v x = q x ^ e := by
  classical
  have hS : ∃ n : ℕ, 0 < n ∧ ∃ x, v x = exp (n : ℤ) := by
    obtain ⟨a, ha⟩ := hv
    have ha0 : v a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
    obtain ⟨b, hb⟩ : ∃ b : ℤ, v a = exp b := ⟨_, (exp_log ha0).symm⟩
    rw [hb, ← exp_zero, exp_lt_exp] at ha
    exact ⟨b.toNat, by omega, a, by rw [hb, Int.toNat_of_nonneg ha.le]⟩
  have he0 : 0 < Nat.find hS := (Nat.find_spec hS).1
  obtain ⟨π, hπ⟩ := (Nat.find_spec hS).2
  have hdvd : ∀ x, x ≠ 0 → ∃ m : ℤ, v x = exp ((Nat.find hS : ℤ) * m) := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : ℤ, v x = exp a :=
      ⟨_, (exp_log ((Valuation.ne_zero_iff v).2 hx)).symm⟩
    refine ⟨a / (Nat.find hS : ℤ), ?_⟩
    have hr0 : 0 ≤ a % (Nat.find hS : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : a % (Nat.find hS : ℤ) < Nat.find hS := Int.emod_lt_of_pos _ (by omega)
    have hdec := Int.mul_ediv_add_emod a (Nat.find hS : ℤ)
    by_contra hne
    have hr : 0 < a % (Nat.find hS : ℤ) := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; rw [ha, exp_inj]; linear_combination -hdec - h
    have hval : v (x * π ^ (-(a / (Nat.find hS : ℤ)))) = exp (((a % (Nat.find hS : ℤ)).toNat : ℕ) : ℤ) := by
      rw [map_mul, map_zpow₀, ha, hπ, ← exp_zsmul, ← exp_add, Int.toNat_of_nonneg hr0, exp_inj,
        smul_eq_mul]
      linear_combination -hdec
    exact Nat.find_min hS (show (a % (Nat.find hS : ℤ)).toNat < Nat.find hS by omega)
      ⟨by omega, _, hval⟩
  have hroot : ∀ x, ∃ c : ℤᵐ⁰, c ^ Nat.find hS = v x := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by rw [hx, map_zero, zero_pow he0.ne']⟩
    · obtain ⟨m, hm⟩ := hdvd x hx
      exact ⟨exp m, by rw [hm, ← exp_nsmul, nsmul_eq_mul]⟩
  choose qf hqf using hroot
  have hle : ∀ {a b : ℤᵐ⁰}, a ^ Nat.find hS ≤ b ^ Nat.find hS → a ≤ b :=
    fun h => (pow_le_pow_iff_left₀ zero_le' zero_le' he0.ne').1 h
  let q : Valuation F ℤᵐ⁰ :=
    { toFun := qf
      map_zero' := pow_inj he0.ne' (by rw [hqf, map_zero, zero_pow he0.ne'])
      map_one' := pow_inj he0.ne' (by rw [hqf, map_one, one_pow])
      map_mul' := fun x y => pow_inj he0.ne' (by rw [hqf, mul_pow, hqf, hqf, map_mul])
      map_add_le_max' := fun x y => by
        have h := v.map_add x y
        rw [← hqf x, ← hqf y, ← hqf (x + y)] at h
        rcases le_max_iff.1 h with h | h
        · exact le_max_of_le_left (hle h)
        · exact le_max_of_le_right (hle h) }
  have hqq : ∀ x, q x = qf x := fun _ => rfl
  refine ⟨q, ?_, Nat.find hS, he0, fun x => by rw [hqq, hqf]⟩
  have hqπ : q π = exp 1 :=
    pow_inj he0.ne' (by rw [hqq, hqf, hπ, ← exp_nsmul, nsmul_eq_mul, mul_one])
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, map_zero q⟩
  · refine ⟨π ^ log t, ?_⟩
    rw [map_zpow₀, hqπ, ← exp_zsmul, smul_eq_mul, mul_one, exp_log ht]
end GlobalTheory.Nef.PlaceResiduePowerBound
