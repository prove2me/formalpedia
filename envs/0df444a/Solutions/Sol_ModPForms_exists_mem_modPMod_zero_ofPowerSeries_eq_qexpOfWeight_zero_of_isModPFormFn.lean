-- Prove2me | solution 1 for ModPForms.exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e57320d8-bd49-5a02-8a08-f833a3f3f4cd

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn

set_option autoImplicit false

open ModularCurve Polynomial

namespace FltWs24
namespace LiftZero

section Val
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_valuationSubring_of_isIntegral_subalgebra (V : ValuationSubring F) (A : Subalgebra K F)
    (hA : ∀ a ∈ A, a ∈ V) {z : F} (hz : IsIntegral A z) : z ∈ V := by

  let φ : A →+* V.toSubring :=
    { toFun := fun a => ⟨a, hA a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hp, hpz⟩ := hz
  have hz' : IsIntegral V.toSubring z := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpz
  haveI : IsIntegrallyClosedIn V.toSubring F := inferInstanceAs (IsIntegrallyClosedIn V F)
  obtain ⟨w, hw⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hz'
  rw [← hw]
  exact w.2

theorem mem_valuationSubring_of_pow_mem (V : ValuationSubring F) {y : F} {a : ℕ} (ha : a ≠ 0)
    (h : y ^ a ∈ V) : y ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' ha).mp h

theorem isIntegral_of_isIntegral_pow_adjoin_of_isIntegral_pow_adjoin_inv (x y : F) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : IsIntegral (Algebra.adjoin K ({x} : Set F)) (y ^ a))
    (h₂ : IsIntegral (Algebra.adjoin K ({x⁻¹} : Set F)) (y ^ b)) :
    IsIntegral K y := by
  by_contra hy
  have hyR : y ∉ (integralClosure K F).toSubring := fun h => hy ((mem_integralClosure_iff K F).mp h)
  haveI : IsIntegrallyClosedIn (integralClosure K F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure K F) F)
  obtain ⟨V, hRV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hyR
  have hKV : ∀ c : K, algebraMap K F c ∈ V := fun c =>
    hRV (show algebraMap K F c ∈ (integralClosure K F).toSubring from (integralClosure K F).algebraMap_mem c)

  let V' : Subalgebra K F :=
    { carrier := V
      mul_mem' := fun ha hb => V.mul_mem _ _ ha hb
      one_mem' := V.one_mem
      add_mem' := fun ha hb => V.add_mem _ _ ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := hKV }
  have hV' : ∀ s : F, s ∈ V → ∀ z ∈ Algebra.adjoin K ({s} : Set F), z ∈ V := by
    intro s hs z hz
    have hle : Algebra.adjoin K ({s} : Set F) ≤ V' :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
    exact hle hz
  apply hyV
  rcases V.mem_or_inv_mem x with hx | hx
  · exact mem_valuationSubring_of_pow_mem V ha
      (mem_valuationSubring_of_isIntegral_subalgebra V _ (hV' x hx) h₁)
  · exact mem_valuationSubring_of_pow_mem V hb
      (mem_valuationSubring_of_isIntegral_subalgebra V _ (hV' x⁻¹ hx) h₂)

end Val

section LS
variable {K : Type} [Field K]

theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem coeff_aeval (p : K[X]) (x : LaurentSeries K) (g : ℤ) :
    (aeval x p).coeff g = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i).coeff g := by
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_eq_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem order_eq_zero_of_isIntegral {x : LaurentSeries K} (hx : IsIntegral K x) (h0 : x ≠ 0) :
    x.order = 0 := by
  set p := minpoly K x with hp
  have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hx h0
  have hpx : aeval x p = 0 := minpoly.aeval K x
  have hmon : p.coeff p.natDegree = 1 := (minpoly.monic hx).coeff_natDegree
  rcases lt_trichotomy x.order 0 with hneg | h | hpos
  ·
    exfalso
    have key := congrArg (fun y : LaurentSeries K => y.coeff ((p.natDegree : ℤ) * x.order)) hpx
    beta_reduce at key
    rw [coeff_aeval, HahnSeries.coeff_zero, Finset.sum_eq_single p.natDegree] at key
    · rw [hmon, one_mul] at key
      have h2 : (x ^ p.natDegree).order = (p.natDegree : ℤ) * x.order := by
        rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact (HahnSeries.coeff_order_eq_zero.not.mpr) (pow_ne_zero _ h0) (h2 ▸ key)
    · intro i hi hne
      have hi' : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast hi') hneg
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · exact h
  ·
    exfalso
    have key := congrArg (fun y : LaurentSeries K => y.coeff 0) hpx
    beta_reduce at key
    rw [coeff_aeval, HahnSeries.coeff_zero, Finset.sum_eq_single 0] at key
    · rw [pow_zero, HahnSeries.coeff_one, if_pos rfl, mul_one] at key
      exact hp0 key
    · intro i _ hne
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [HahnSeries.order_pow, nsmul_eq_mul]
      exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hne) hpos
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem eq_C_of_isIntegral {x : LaurentSeries K} (hx : IsIntegral K x) : x = HahnSeries.C (x.coeff 0) := by
  set z := x - HahnSeries.C (x.coeff 0) with hz
  have hzint : IsIntegral K z := hx.sub (by rw [← algebraMap_eq_C]; exact isIntegral_algebraMap)
  have hz0 : z.coeff 0 = 0 := by
    rw [hz, HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]
  by_contra hne
  have hzne : z ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hord := order_eq_zero_of_isIntegral hzint hzne
  exact (HahnSeries.coeff_order_eq_zero.not.mpr) hzne (hord ▸ hz0)

end LS

end FltWs24.LiftZero

open FltWs24.LiftZero in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p]
    (G : ↥(modularFunctionFieldC K N)) (hG : IsModPFormFn K 0 (G : LaurentSeries K)) :
    ∃ φ : PowerSeries K, φ ∈ ModPForms.modPMod N (2 * ((0 : ℕ) : ℤ)) K ∧
      HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K ((0 : ℕ) : ℤ) (G : LaurentSeries K) := by

  obtain ⟨h₁, h₂⟩ := hG
  simp only [mul_zero, pow_zero, mul_one] at h₁ h₂

  have hint : IsIntegral K (G : LaurentSeries K) :=
    isIntegral_of_isIntegral_pow_adjoin_of_isIntegral_pow_adjoin_inv (jqModC K) _ (by norm_num)
      (by norm_num) h₁ h₂
  set c := (G : LaurentSeries K).coeff 0 with hc
  have hGc : (G : LaurentSeries K) = HahnSeries.C c := eq_C_of_isIntegral hint

  refine ⟨c • 1, ?_, ?_⟩
  · rw [show (2 * ((0 : ℕ) : ℤ) : ℤ) = 0 by norm_num]
    refine Submodule.smul_mem _ c ?_

    unfold ModPForms.modPMod
    refine Submodule.subset_span ⟨(1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0),
      fun n => if n = 0 then 1 else 0, fun n => ?_, ?_⟩
    · unfold ModularFormClass.qCoeff
      rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
      by_cases hn : n = 0 <;> simp [hn]
    · ext n
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
      by_cases hn : n = 0 <;> simp [hn]
  · unfold qexpOfWeight
    rw [Nat.cast_zero, zpow_zero, mul_one, hGc, Algebra.smul_def, mul_one]
    simp

end S_ModPForms_exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn
end P2MW
export P2MW.S_ModPForms_exists_mem_modPMod_zero_ofPowerSeries_eq_qexpOfWeight_zero_of_isModPFormFn (solution)
