-- Prove2me | solution 1 for ModularCurve.StarBank.starK
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/341ef078-c553-5118-a420-e3b8d38b820d

import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.CharP.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_StarBank_starK

set_option autoImplicit false

open HahnSeries PowerSeries

namespace ModularCurve
p2m_export "ModularCurve" "jqModC map_jqModC eisenstein4 etaProd dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum ofPowerSeries_coeff_of_neg"
namespace W1
p2m_open "ModularCurve"

noncomputable abbrev Dseries (K : Type*) [CommRing K] : LaurentSeries K :=
  HahnSeries.single (1 : ℤ) (1 : K)
    * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24

private def hahnMapRingHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

private theorem hahnMapRingHom_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : LaurentSeries R) : hahnMapRingHom f x = x.map f := rfl

theorem ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u).map f = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext k
  rw [HahnSeries.map_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk,
      ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem hahnMapRingHom_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    hahnMapRingHom f (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) :=
  ofPowerSeries_map f u

private theorem hahnMapRingHom_single {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : ℤ) (r : R) :
    hahnMapRingHom f (HahnSeries.single g r) = HahnSeries.single g (f r) :=
  HahnSeries.map_single (f := f.toZeroHom)

private theorem hahnMapRingHom_etaBlock (K : Type*) [CommRing K] :
    hahnMapRingHom (Int.castRingHom K)
        (HahnSeries.single (1 : ℤ) (1 : ℤ)
          * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24)
      = HahnSeries.single (1 : ℤ) (1 : K)
          * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24 := by
  rw [map_mul, map_pow, hahnMapRingHom_single, hahnMapRingHom_ofPowerSeries, map_one]

private theorem hahnMapRingHom_aeval_jqModC (K : Type*) [CommRing K] (G : Polynomial ℤ) :
    hahnMapRingHom (Int.castRingHom K) (Polynomial.aeval (ModularCurve.jqModC ℤ) G)
      = Polynomial.aeval (ModularCurve.jqModC K) (G.map (Int.castRingHom K)) := by
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := ℤ) (S := LaurentSeries ℤ) (T := K) (U := LaurentSeries K)
    (φ := Int.castRingHom K) (ψ := hahnMapRingHom (Int.castRingHom K))
    (RingHom.ext_int _ _) G (ModularCurve.jqModC ℤ)
  rw [h, hahnMapRingHom_apply, ModularCurve.map_jqModC]

private theorem powerSeries_map_eq_C_of_dvd {K : Type*} [CommRing K] {ℓ : ℕ} [CharP K ℓ]
    {T : PowerSeries ℤ} (hT : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) :
    T.map (Int.castRingHom K) = PowerSeries.C ((PowerSeries.constantCoeff T : ℤ) : K) := by
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_pos rfl, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast]
  · rw [if_neg hm.ne']
    exact_mod_cast (CharP.intCast_eq_zero_iff K ℓ _).mpr (hT m hm)

private theorem eisenstein4_map_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    PowerSeries.map (Int.castRingHom K) ModularCurve.eisenstein4 = 1 := by
  ext n
  rw [PowerSeries.coeff_map, ModularCurve.eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', if_neg hn.ne']
    have h240Z : (Int.castRingHom K) (240 : ℤ) = 0 := by
      simp only [eq_intCast]; exact_mod_cast h240
    rw [map_mul, h240Z, zero_mul]

theorem jqModC_mul_Dseries_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    ModularCurve.jqModC K * Dseries K = 1 := by
  have heis := eisenstein4_map_of_240 h240
  have hjnum : PowerSeries.map (Int.castRingHom K) ModularCurve.jNum
      = PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnitInv := by
    rw [ModularCurve.jNum, map_mul, map_pow, heis, one_pow, one_mul]
  have heta : HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24
      = HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnit) := by
    rw [ModularCurve.dedekindEtaUnit, map_pow, map_pow]
  rw [ModularCurve.jqModC, Dseries, hjnum, heta]
  have hinv : PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnitInv
      * PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnit = 1 := by
    rw [← map_mul, mul_comm, ModularCurve.dedekindEtaUnit_mul_inv, map_one]
  calc HahnSeries.single (-1 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnitInv)
        * (HahnSeries.single (1 : ℤ) (1 : K)
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnit))
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K))
        * (HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnitInv)
            * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) ModularCurve.dedekindEtaUnit)) := by ring
    _ = HahnSeries.single (0 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K (1 : PowerSeries K) := by
        rw [HahnSeries.single_mul_single, ← map_mul, hinv]; ring_nf
    _ = 1 := by rw [HahnSeries.single_zero_one, map_one, one_mul]

end ModularCurve.W1

p2m_open "P2MW.S_ModularCurve_StarBank_starK.ModularCurve.W1 ModularCurve P2MW.S_ModularCurve_StarBank_starK.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "jqModC map_jqModC eisenstein4 etaProd dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum ofPowerSeries_coeff_of_neg" namespace StarBank end ModularCurve.StarBank
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.StarBank.starK_of_240 (K : Type*) [Field K] (h240 : (240 : K) = 0) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  refine ⟨1, le_refl 1, ?_, Polynomial.X, Polynomial.natDegree_X, ?_⟩
  · exact_mod_cast one_ne_zero (α := K)
  · rw [Polynomial.aeval_X, pow_one]
    exact ModularCurve.W1.jqModC_mul_Dseries_of_240 h240

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.StarBank.starK (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hHasse : 5 ≤ ℓ → ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
        (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
        ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
        ∧ HahnSeries.ofPowerSeries ℤ ℤ T
            = Polynomial.aeval (jqModC ℤ) G
              * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                  * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1)) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  have hℓp : ℓ.Prime := Fact.out
  rcases lt_or_ge ℓ 5 with hℓ5 | hℓ5
  ·
    have hℓdvd : ℓ ∣ 240 := by
      interval_cases ℓ <;> first | decide | exact absurd hℓp (by decide)
    exact ModularCurve.StarBank.starK_of_240 K ((CharP.cast_eq_zero_iff K ℓ 240).mpr hℓdvd)
  ·
    obtain ⟨T, G₀, hTdvd, hTconst, hGdeg, hGcoeff, hId⟩ := hHasse hℓ5
    set cT := PowerSeries.constantCoeff T with hcTdef
    have hcTK : ((cT : ℤ) : K) ≠ 0 := fun h =>
      hTconst ((CharP.intCast_eq_zero_iff K ℓ cT).mp h)

    have hmap := congrArg (hahnMapRingHom (Int.castRingHom K)) hId
    rw [map_mul, map_pow, hahnMapRingHom_aeval_jqModC, hahnMapRingHom_etaBlock,
      hahnMapRingHom_apply, ofPowerSeries_map, powerSeries_map_eq_C_of_dvd hTdvd,
      HahnSeries.ofPowerSeries_C] at hmap

    refine ⟨ℓ - 1, by omega, ?_,
      Polynomial.C (((cT : ℤ) : K)⁻¹) * G₀.map (Int.castRingHom K), ?_, ?_⟩
    ·
      have h1 : (1 : ℕ) ≤ ℓ := hℓp.one_lt.le
      have : ((ℓ - 1 : ℕ) : K) = (ℓ : K) - 1 := by exact_mod_cast Nat.cast_sub h1
      rw [this, CharP.cast_eq_zero K ℓ, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    ·
      have hdegK : (G₀.map (Int.castRingHom K)).natDegree = ℓ - 1 := by
        refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_ |>.trans hGdeg
        rw [Polynomial.leadingCoeff, hGdeg, hGcoeff]; simpa using hcTK
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hcTK), hdegK]
    ·
      rw [map_mul (Polynomial.aeval (jqModC K)), Polynomial.aeval_C, mul_assoc, ← hmap,
        ← hcTdef, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
        HahnSeries.ofPowerSeries_C, ← map_mul, inv_mul_cancel₀ hcTK, map_one]

example : ((720 : ℤ) : ℚ) ≠ 0 := by decide

open HahnSeries PowerSeries _root_.ModularCurve _root_.P2MW.S_ModularCurve_StarBank_starK.ModularCurve in

theorem solution (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hHasse : 5 ≤ ℓ → ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
        (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
        ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
        ∧ HahnSeries.ofPowerSeries ℤ ℤ T
            = Polynomial.aeval (jqModC ℤ) G
              * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                  * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1)) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 :=
  ModularCurve.StarBank.starK K hHasse

#print axioms solution

end S_ModularCurve_StarBank_starK
end P2MW
export P2MW.S_ModularCurve_StarBank_starK (solution)
