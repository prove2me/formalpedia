-- Prove2me | solution 1 for LaurentSeries.exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/83149030-c59c-5623-9b92-5bec4c4b73c0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries

set_option autoImplicit false

open PowerSeries

namespace IntCoeffAux

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] (i : R →+* K) (hi : Function.Injective i)

noncomputable def φ : PowerSeries R →+* LaurentSeries K := (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)

theorem φ_apply (f : PowerSeries R) : φ i f = HahnSeries.ofPowerSeries ℤ K (f.map i) := rfl

include hi in
theorem φ_injective : Function.Injective (φ i) := by
  intro a b h
  rw [φ_apply, φ_apply] at h
  have h' : a.map i = b.map i := HahnSeries.ofPowerSeries_injective h
  ext n
  apply hi
  have := congrArg (PowerSeries.coeff n) h'
  rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at this

theorem coeff_φ (f : PowerSeries R) (n : ℕ) : (φ i f).coeff (n : ℤ) = i (PowerSeries.coeff n f) := by
  rw [φ_apply, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem coeff_φ_of_neg (f : PowerSeries R) {n : ℤ} (hn : n < 0) : (φ i f).coeff n = 0 := by
  rw [φ_apply, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  simp only [Set.mem_range, not_exists]
  intro m hm
  have : ((m : ℕ) : ℤ) = n := hm
  omega

noncomputable def Φ : FractionRing (PowerSeries R) →+* LaurentSeries K :=
  IsFractionRing.lift (φ_injective i hi)

theorem Φ_algebraMap (f : PowerSeries R) : Φ i hi (algebraMap _ _ f) = φ i f :=
  IsFractionRing.lift_algebraMap (φ_injective i hi) f

theorem closure_le_fieldRange : Subfield.closure (Set.range (φ i)) ≤ (Φ i hi).fieldRange := by
  rw [Subfield.closure_le]
  rintro _ ⟨f, rfl⟩
  exact ⟨algebraMap _ _ f, Φ_algebraMap i hi f⟩

theorem coeff_φ_eq (f : PowerSeries R) (n : ℤ) : (φ i f).coeff n = i ((HahnSeries.ofPowerSeries ℤ R f).coeff n) := by
  rw [φ_apply, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

theorem exists_map_eq (g : PowerSeries K) (hg : ∀ n : ℕ, PowerSeries.coeff n g ∈ Set.range i) :
    ∃ f : PowerSeries R, f.map i = g := by
  classical
  refine ⟨PowerSeries.mk fun n => (hg n).choose, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact (hg n).choose_spec

theorem exists_single_mul_φ_eq (z : LaurentSeries K) (hz : ∀ n : ℤ, z.coeff n ∈ Set.range i) :
    ∃ (e : ℤ) (f : PowerSeries R), HahnSeries.single e (1 : K) * φ i f = z := by
  obtain ⟨f, hf⟩ := exists_map_eq i z.powerSeriesPart (fun n => by rw [LaurentSeries.powerSeriesPart_coeff]; exact hz _)
  refine ⟨z.order, f, ?_⟩
  rw [φ_apply, hf]
  exact z.single_order_mul_powerSeriesPart

theorem single_one_zpow (k : ℤ) : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ^ k = HahnSeries.single k 1 := by
  have hpow : ∀ n : ℕ, (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ^ n = HahnSeries.single (n : ℤ) 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ih, HahnSeries.single_mul_single, one_mul]; push_cast; rfl
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, hpow]
  · rw [zpow_neg, zpow_natCast, hpow]
    apply inv_eq_of_mul_eq_one_right
    rw [HahnSeries.single_mul_single, one_mul, add_neg_cancel]
    rfl

theorem φ_X : φ i PowerSeries.X = HahnSeries.single 1 1 := by
  rw [φ_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

end IntCoeffAux

theorem solution
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K]
    (i : R →+* K) (hi : Function.Injective i)
    (x : LaurentSeries K)
    (hx : x ∈ Subfield.closure (Set.range ((HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i))))
    (S : Subring (LaurentSeries K)) (hS : ∀ z ∈ S, ∀ n : ℤ, z.coeff n ∈ Set.range i)
    (hint : IsIntegral ↥S x) :
    ∃ y : LaurentSeries R, ∀ n : ℤ, i (y.coeff n) = x.coeff n := by
  classical

  haveI : IsIntegrallyClosed (PowerSeries R) := inferInstance
  let F := FractionRing (PowerSeries R)
  let ψ : F →+* LaurentSeries K := IntCoeffAux.Φ i hi
  have hψinj : Function.Injective ψ := ψ.injective

  obtain ⟨z₀, hz₀⟩ : x ∈ ψ.fieldRange := IntCoeffAux.closure_le_fieldRange i hi hx

  let L := Localization.Away (PowerSeries.X : PowerSeries R)
  have hXne : ∀ y : Submonoid.powers (PowerSeries.X : PowerSeries R), (y : PowerSeries R) ≠ 0 := by
    rintro ⟨_, k, rfl⟩; exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hXunit : ∀ y : Submonoid.powers (PowerSeries.X : PowerSeries R), IsUnit (algebraMap (PowerSeries R) F y) :=
    fun y => isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries R) F)).mpr (hXne y))
  letI : Algebra L F := (IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : PowerSeries R)) hXunit).toAlgebra
  haveI : IsScalarTower (PowerSeries R) L F :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq (M := Submonoid.powers (PowerSeries.X : PowerSeries R)) hXunit b).symm
  let χ : L →+* LaurentSeries K := ψ.comp (algebraMap L F)
  have hψX : ψ (algebraMap (PowerSeries R) F PowerSeries.X) = HahnSeries.single 1 1 := by
    show IntCoeffAux.Φ i hi _ = _
    rw [IntCoeffAux.Φ_algebraMap, IntCoeffAux.φ_X]
  have hψB : ∀ b : PowerSeries R, ψ (algebraMap (PowerSeries R) F b) = IntCoeffAux.φ i b := fun b => IntCoeffAux.Φ_algebraMap i hi b

  have hSχ : ∀ s ∈ S, s ∈ Set.range χ := by
    intro s hs
    obtain ⟨e, f, hef⟩ := IntCoeffAux.exists_single_mul_φ_eq i s (hS s hs)
    have hu := IsLocalization.Away.algebraMap_isUnit (S := L) (PowerSeries.X : PowerSeries R)
    refine ⟨((hu.unit ^ e : Lˣ) : L) * algebraMap (PowerSeries R) L f, ?_⟩
    have h1 : χ (algebraMap (PowerSeries R) L f) = IntCoeffAux.φ i f := by
      show ψ (algebraMap L F (algebraMap (PowerSeries R) L f)) = _
      rw [← IsScalarTower.algebraMap_apply, hψB]
    have h2 : χ ((hu.unit ^ e : Lˣ) : L) = HahnSeries.single e 1 := by
      have hX : χ (algebraMap (PowerSeries R) L PowerSeries.X) = HahnSeries.single 1 1 := by
        show ψ (algebraMap L F (algebraMap (PowerSeries R) L PowerSeries.X)) = _
        rw [← IsScalarTower.algebraMap_apply, hψX]
      calc χ ((hu.unit ^ e : Lˣ) : L) = ((Units.map (χ : L →* LaurentSeries K) (hu.unit ^ e) : (LaurentSeries K)ˣ) : LaurentSeries K) := by
            rw [Units.coe_map]; rfl
        _ = ((Units.map (χ : L →* LaurentSeries K) hu.unit : (LaurentSeries K)ˣ) : LaurentSeries K) ^ e := by
            rw [map_zpow, Units.val_zpow_eq_zpow_val]
        _ = (χ (algebraMap (PowerSeries R) L PowerSeries.X)) ^ e := by
            rw [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec]
        _ = HahnSeries.single e 1 := by rw [hX, IntCoeffAux.single_one_zpow]
    rw [map_mul, h1, h2, hef]

  obtain ⟨P, hPm, hPx⟩ := hint
  set Q : Polynomial (LaurentSeries K) := P.map S.subtype with hQ
  have hQm : Q.Monic := hPm.map _
  have hQx : Q.eval x = 0 := by rw [hQ, Polynomial.eval_map]; exact hPx
  have hQl : Q ∈ Polynomial.lifts χ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQ, Polynomial.coeff_map]
    exact hSχ _ (P.coeff n).2
  obtain ⟨P', hP'Q, -, hP'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQl hQm
  have hz₀int : IsIntegral L z₀ := by
    refine ⟨P', hP'm, ?_⟩
    apply hψinj
    rw [map_zero, Polynomial.hom_eval₂, hz₀]
    show Polynomial.eval₂ χ x P' = 0
    rw [← Polynomial.eval_map, hP'Q, hQx]

  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) z₀ hz₀int
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk

  have hxb : HahnSeries.single (k : ℤ) (1 : K) * x = IntCoeffAux.φ i b := by
    have := congrArg ψ hb
    rw [hψB, Submonoid.smul_def, Algebra.smul_def, map_mul, map_pow, map_pow, hψX, hz₀] at this
    rw [this, ← zpow_natCast, IntCoeffAux.single_one_zpow]
  refine ⟨HahnSeries.single (-(k : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ R b, fun n => ?_⟩
  have hx' : x = HahnSeries.single (-(k : ℤ)) 1 * IntCoeffAux.φ i b := by
    rw [← hxb, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, one_mul]
    exact (one_mul x).symm
  rw [hx', HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul, one_mul, IntCoeffAux.coeff_φ_eq]

end S_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries
end P2MW
export P2MW.S_LaurentSeries_exists_forall_coeff_eq_of_isIntegral_of_mem_closure_range_ofPowerSeries (solution)
