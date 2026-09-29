-- Prove2me | solution 1 for ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0842af33-8c00-5f08-af30-3849c027b516

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
import Theorems.Thm_ModularCurve_StarBank_hassePolyDescent
import Theorems.Thm_ModularCurve_StarBank_eisInt_series
import Theorems.Thm_ModularCurve_StarBank_eisInt_not_dvd_num
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

noncomputable section

section DescFrobenius

variable (k : Type*) [Field k]

private def descDelta : LaurentSeries k :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
    (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))

private theorem descDelta_def :
    descDelta k = HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
      (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) := rfl

private theorem descDelta_eq_map :
    (HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit).map
        (Int.castRingHom k) = descDelta k := by
  have hmul : ∀ x y : LaurentSeries ℤ, (x * y).map (Int.castRingHom k)
      = x.map (Int.castRingHom k) * y.map (Int.castRingHom k) :=
    fun x y => HahnSeries.map_mul (Int.castRingHom k).toNonUnitalRingHom
  have hsingle : (HahnSeries.single (1 : ℤ) (1 : ℤ)).map (Int.castRingHom k)
      = HahnSeries.single (1 : ℤ) (1 : k) := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single,
      apply_ite (Int.castRingHom k), map_one, map_zero]
  have hseries : ∀ u : PowerSeries ℤ, (HahnSeries.ofPowerSeries ℤ ℤ u).map (Int.castRingHom k)
      = HahnSeries.ofPowerSeries ℤ k (u.map (Int.castRingHom k)) := by
    intro u
    ext n
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn, ModularCurve.ofPowerSeries_coeff_of_neg _ hn,
        map_zero]
  rw [hmul, hsingle, hseries, descDelta]

private theorem desc_intCast_pow_char (q : ℕ) [Fact q.Prime] [CharP k q] (n : ℤ) :
    Int.castRingHom k n ^ q = Int.castRingHom k n := by
  have h : Int.castRingHom k = (ZMod.castHom (dvd_refl q) k).comp (Int.castRingHom (ZMod q)) :=
    RingHom.ext_int _ _
  rw [h, RingHom.comp_apply, ← map_pow, ZMod.pow_card]

private theorem descDelta_coeff_fixed (q : ℕ) [Fact q.Prime] [CharP k q] (n : ℤ) :
    (descDelta k).coeff n ^ q = (descDelta k).coeff n := by
  rw [← descDelta_eq_map, HahnSeries.map_coeff]
  exact desc_intCast_pow_char k q _

private theorem desc_qExpand_descDelta (q : ℕ) [Fact q.Prime] [CharP k q] :
    ModularCurve.qExpand k q (descDelta k) = descDelta k ^ q :=
  (ModularCurve.pow_char_eq_qExpand_of_coeff_fixed q (descDelta k) (descDelta_coeff_fixed k q)).symm

private theorem desc_lhs (q : ℕ) [Fact q.Prime] [CharP k q] :
    descDelta k * (ModularCurve.qExpand k q (descDelta k))⁻¹ = (descDelta k ^ (q - 1))⁻¹ := by
  rw [desc_qExpand_descDelta k q]
  obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by have := (Fact.out : q.Prime).two_le; omega⟩
  have hm0 : m ≠ 0 := by have := (Fact.out : q.Prime).two_le; omega
  rw [show q - 1 = m by omega, hm, pow_succ]
  by_cases h : descDelta k = 0
  · rw [h, zero_pow hm0, zero_mul, inv_zero]
  · rw [mul_inv, mul_left_comm, mul_inv_cancel₀ h, mul_one]

private theorem desc_eisenstein4_map (q : ℕ) [Fact q.Prime] [CharP k q] (h : q ∣ 240) :
    ModularCurve.eisenstein4.map (Int.castRingHom k) = 1 := by
  have h240 : (240 : k) = 0 := by
    have := (CharP.cast_eq_zero_iff k q 240).2 h
    simpa using this
  ext n
  rw [PowerSeries.coeff_map]
  simp only [ModularCurve.eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs
  · simp
  · simp [h240]

private theorem desc_jqModC_mul_descDelta (q : ℕ) [Fact q.Prime] [CharP k q] (h : q ∣ 240) :
    ModularCurve.jqModC k * descDelta k = 1 := by
  have hU : ModularCurve.dedekindEtaUnitInv.map (Int.castRingHom k)
      * ModularCurve.dedekindEtaUnit.map (Int.castRingHom k) = 1 := by
    rw [← map_mul, mul_comm, ModularCurve.dedekindEtaUnit_mul_inv, map_one]
  rw [ModularCurve.jqModC, descDelta, ModularCurve.jNum, map_mul, map_pow,
    desc_eisenstein4_map k q h, one_pow, one_mul]
  calc HahnSeries.single (-1 : ℤ) (1 : k)
          * HahnSeries.ofPowerSeries ℤ k (ModularCurve.dedekindEtaUnitInv.map (Int.castRingHom k))
        * (HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ k (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)))
      = (HahnSeries.single (-1 : ℤ) (1 : k) * HahnSeries.single (1 : ℤ) 1)
          * HahnSeries.ofPowerSeries ℤ k (ModularCurve.dedekindEtaUnitInv.map (Int.castRingHom k)
              * ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) := by
        rw [map_mul]; ring
    _ = 1 := by
        rw [hU, (HahnSeries.ofPowerSeries ℤ k).map_one, HahnSeries.single_mul_single]
        simp

private theorem desc_small (q : ℕ) [Fact q.Prime] [CharP k q] (h : q ∣ 240) :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      Polynomial.aeval (ModularCurve.jqModC k) G * descDelta k ^ (q - 1) = 1 :=
  ⟨Polynomial.X ^ (q - 1), Polynomial.natDegree_X_pow _, by
    rw [map_pow, Polynomial.aeval_X, ← mul_pow, desc_jqModC_mul_descDelta k q h, one_pow]⟩

end DescFrobenius

end

open HahnSeries PowerSeries

namespace DescUnitPoly

section Transport

private def seriesMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

private theorem seriesMap_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : LaurentSeries R) : seriesMap f x = x.map f := rfl

private theorem ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
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

private theorem seriesMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    seriesMap f (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) :=
  ofPowerSeries_map f u

private theorem seriesMap_single {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : ℤ) (r : R) :
    seriesMap f (HahnSeries.single g r) = HahnSeries.single g (f r) :=
  HahnSeries.map_single (f := f.toZeroHom)

private theorem seriesMap_discriminant (K : Type*) [CommRing K] :
    seriesMap (Int.castRingHom K)
        (HahnSeries.single (1 : ℤ) (1 : ℤ)
          * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24)
      = HahnSeries.single (1 : ℤ) (1 : K)
          * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24 := by
  rw [map_mul, map_pow, seriesMap_single, seriesMap_ofPowerSeries, map_one]

private theorem seriesMap_aeval_jqModC (K : Type*) [CommRing K] (G : Polynomial ℤ) :
    seriesMap (Int.castRingHom K) (Polynomial.aeval (ModularCurve.jqModC ℤ) G)
      = Polynomial.aeval (ModularCurve.jqModC K) (G.map (Int.castRingHom K)) := by
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := ℤ) (S := LaurentSeries ℤ) (T := K) (U := LaurentSeries K)
    (φ := Int.castRingHom K) (ψ := seriesMap (Int.castRingHom K))
    (RingHom.ext_int _ _) G (ModularCurve.jqModC ℤ)
  rw [h, seriesMap_apply, ModularCurve.map_jqModC]

private theorem map_eq_C_of_dvd {K : Type*} [CommRing K] {ℓ : ℕ} [CharP K ℓ]
    {T : PowerSeries ℤ} (hT : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) :
    T.map (Int.castRingHom K) = PowerSeries.C ((PowerSeries.constantCoeff T : ℤ) : K) := by
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_pos rfl, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast]
  · rw [if_neg hm.ne']
    exact_mod_cast (CharP.intCast_eq_zero_iff K ℓ _).mpr (hT m hm)

end Transport

section HasseInput

open UpperHalfPlane
open scoped MatrixGroups

private theorem hasse_input {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
      (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
      ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
      ∧ HahnSeries.ofPowerSeries ℤ ℤ T
          = Polynomial.aeval (ModularCurve.jqModC ℤ) G
            * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ (ℓ - 1) := by
  have hk : 3 ≤ ℓ - 1 := by omega
  obtain ⟨T, hTmap, hTconst, hTdvd⟩ := ModularCurve.StarBank.eisInt_series hℓ5 hk
  have hnum0 : ¬ (ℓ : ℤ) ∣ (_root_.bernoulli (ℓ - 1)).num :=
    ModularCurve.StarBank.eisInt_not_dvd_num hℓ5

  have hmapZ : T.map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_C]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff_apply, hTconst]
      rfl
    · rw [if_neg (by omega)]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hTdvd n hn)
  have hmapZ12 : (T ^ 12).map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C ((((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ^ 12) := by
    rw [map_pow, hmapZ, ← map_pow]
  have hnumZ : (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ≠ 0 :=
    fun h => hnum0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

  have hdvd12 : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ (T ^ 12).coeff m := by
    intro m hm
    have h1 := congrArg (fun u : PowerSeries (ZMod ℓ) => PowerSeries.coeff m u) hmapZ12
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_C] at h1
    rw [if_neg (by omega : ¬ m = 0)] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1

  have hconst12 : PowerSeries.constantCoeff (T ^ 12) = (_root_.bernoulli (ℓ - 1)).num ^ 12 := by
    rw [map_pow, hTconst]
  have hnot12 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff (T ^ 12) := by
    rw [hconst12, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact pow_ne_zero 12 hnumZ

  have hw : ((12 : ℕ) : ℤ) * ((ℓ - 1 : ℕ) : ℤ) = 12 * ((ℓ - 1 : ℕ) : ℤ) := by norm_num
  have hT12 : (T ^ 12).map (Int.castRingHom ℂ)
      = UpperHalfPlane.qExpansion 1
          ⇑(ModularForm.mcast hw
              ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12)) := by
    have h1 : UpperHalfPlane.qExpansion 1
        ⇑(ModularForm.mcast hw
            ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
        = UpperHalfPlane.qExpansion 1
            ⇑((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12) := rfl
    rw [h1, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_pow, hTmap]
  have h0 : PowerSeries.constantCoeff (T ^ 12) ≠ 0 := by
    rw [hconst12]
    intro h
    exact hnum0 ((pow_eq_zero_iff (by norm_num : (12 : ℕ) ≠ 0)).mp h ▸ dvd_zero _)
  obtain ⟨G, hGdeg, hGcoeff, hGid⟩ := ModularCurve.StarBank.hassePolyDescent
    (ModularForm.mcast hw ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
    hT12 h0
  exact ⟨T ^ 12, G, hdvd12, hnot12, hGdeg, hGcoeff, hGid⟩

end HasseInput

private theorem desc_engine (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (hq : 5 ≤ q) :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      Polynomial.aeval (ModularCurve.jqModC k) G *
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))) ^ (q - 1) = 1 := by
  obtain ⟨T, G₀, hTdvd, hTconst, hGdeg, hGcoeff, hId⟩ := hasse_input hq
  set cT := PowerSeries.constantCoeff T with hcTdef
  have hcTK : ((cT : ℤ) : k) ≠ 0 := fun h =>
    hTconst ((CharP.intCast_eq_zero_iff k q cT).mp h)

  have hmap := congrArg (seriesMap (Int.castRingHom k)) hId
  rw [map_mul, map_pow, seriesMap_aeval_jqModC, seriesMap_discriminant,
    seriesMap_apply, ofPowerSeries_map, map_eq_C_of_dvd hTdvd,
    HahnSeries.ofPowerSeries_C] at hmap

  have heta : HahnSeries.ofPowerSeries ℤ k
        (PowerSeries.map (Int.castRingHom k) ModularCurve.etaProd) ^ 24
      = HahnSeries.ofPowerSeries ℤ k
        (PowerSeries.map (Int.castRingHom k) ModularCurve.dedekindEtaUnit) := by
    rw [ModularCurve.dedekindEtaUnit, map_pow, map_pow]
  rw [heta] at hmap
  refine ⟨Polynomial.C (((cT : ℤ) : k)⁻¹) * G₀.map (Int.castRingHom k), ?_, ?_⟩
  · have hdegK : (G₀.map (Int.castRingHom k)).natDegree = q - 1 := by
      refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_ |>.trans hGdeg
      rw [Polynomial.leadingCoeff, hGdeg, hGcoeff]; simpa using hcTK
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hcTK), hdegK]
  · rw [map_mul (Polynomial.aeval (ModularCurve.jqModC k)), Polynomial.aeval_C, mul_assoc,
      ← hmap, ← hcTdef, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C, ← map_mul, inv_mul_cancel₀ hcTK, map_one]

end DescUnitPoly

theorem solution
    (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) *
        (ModularCurve.qExpand k q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))))⁻¹
        = Polynomial.aeval (ModularCurve.jqModC k) G := by
  have hqp : q.Prime := Fact.out
  obtain ⟨G, hdeg, hG⟩ : ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      Polynomial.aeval (ModularCurve.jqModC k) G * descDelta k ^ (q - 1) = 1 := by
    rcases lt_or_ge q 5 with hq | hq
    · refine desc_small k q ?_
      interval_cases q <;> first | decide | exact absurd hqp (by decide)
    · exact DescUnitPoly.desc_engine k q hq
  refine ⟨G, hdeg, ?_⟩
  show descDelta k * (ModularCurve.qExpand k q (descDelta k))⁻¹ = _
  rw [desc_lhs k q]
  exact (eq_inv_of_mul_eq_one_left hG).symm

end S_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
end P2MW
export P2MW.S_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP (solution)
