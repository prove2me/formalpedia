-- Prove2me | solution 1 for GlobalTheory.QNorm.relIndex_hiUnits_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:41.070805+00:00
-- url     : https://prove2.me/submissions/b9e70966-472a-4d6d-aa6b-aed8fc25157d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < WithZero.exp m) :
    a ≤ WithZero.exp (m - 1) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  intro K _ w π R n hπ hR
  have hπn : w (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hπn0 : w (π ^ n) ≠ 0 := by rw [hπn]; exact WithZero.exp_ne_zero
  have hπn0' : π ^ n ≠ 0 := by
    intro h; rw [h] at hπn0; simp at hπn0
  have hex : ∀ x : hiUnits w n, ∃ r : R, w ((((x : Kˣ) : K) - 1) / π ^ n - r) < 1 := by
    intro x
    have hx : w (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := x.2.2
    obtain ⟨r, hr, h⟩ := hR ((((x : Kˣ) : K) - 1) / π ^ n) (by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hπn0), hπn]; exact hx)
    exact ⟨⟨r, hr⟩, h⟩
  choose f hf using hex
  have key : ∀ x y : hiUnits w n, f x = f y →
      x⁻¹ * y ∈ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) := by
    intro x y hxy
    have hx1 : w ((x : Kˣ) : K) = 1 := x.2.1
    have hy1 : w ((y : Kˣ) : K) = 1 := y.2.1
    have h1 := hf x
    have h2 := hf y
    rw [← hxy] at h2
    have h3 := w.map_sub_lt h2 h1
    have h4 : (((y : Kˣ) : K) - 1) / π ^ n - (f x : K) -
        ((((x : Kˣ) : K) - 1) / π ^ n - (f x : K)) =
        (((y : Kˣ) : K) - ((x : Kˣ) : K)) / π ^ n := by ring
    rw [h4, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hπn0), hπn] at h3
    have h5 := le_exp_sub_one_of_lt_exp h3
    rw [Subgroup.mem_subgroupOf]
    have hv : ((((x⁻¹ * y : hiUnits w n) : Kˣ)) : K) =
        ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) := by simp
    refine ⟨by rw [hv, map_mul, map_inv₀, hx1, hy1]; simp, ?_⟩
    have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h6 : ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) - 1 =
        ((x : Kˣ) : K)⁻¹ * (((y : Kˣ) : K) - ((x : Kˣ) : K)) := by
      field_simp
    rw [hv, h6, map_mul, map_inv₀, hx1, inv_one, one_mul]
    refine h5.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hinj : Function.Injective
      (fun q : hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) => f q.out) := by
    intro p q hpq
    have := key _ _ hpq
    rw [← QuotientGroup.eq] at this
    simpa using this
  have hfin : Finite (hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n)) :=
    Finite.of_injective _ hinj
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := R), Fintype.card_coe] at this
    exact this
end GlobalTheory.QNorm
