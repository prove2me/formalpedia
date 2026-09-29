-- Prove2me | solution 1 for NumberField.LevelArith.finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7f44951c-a11a-5a06-90f3-0a0f5e9b4efe

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_IsDedekindDomain_SelmerConnectingHom
import Theorems.Thm_NumberField_LevelArith_sPrimeClasses_eq_closure
import Theorems.Thm_NumberField_LevelArith_selmerStable_eq_selmer
import Theorems.Thm_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime
import Theorems.Thm_NumberField_LevelArith_finiteDimensional_unitsModP_sClass_selmerRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def comapPrime (σ : R ≃+* R) (v : HeightOneSpectrum R) : HeightOneSpectrum R where
  asIdeal := v.asIdeal.comap (σ : R →+* R)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h => by
    have e : Ideal.map (σ : R →+* R) (v.asIdeal.comap (σ : R →+* R)) = v.asIdeal := Ideal.map_comap_of_surjective _ σ.surjective _
    rw [h, Ideal.map_bot] at e
    exact v.ne_bot e.symm

omit [IsDedekindDomain R] in
theorem map_comapPrime (σ : R ≃+* R) (v : HeightOneSpectrum R) :
    (comapPrime σ v).asIdeal.map (σ : R →+* R) = v.asIdeal :=
  Ideal.map_comap_of_surjective _ σ.surjective _

theorem map_dvd_map_iff (σ : R ≃+* R) (I J : Ideal R) : I.map (σ : R →+* R) ∣ J.map (σ : R →+* R) ↔ I ∣ J := by
  constructor
  · intro h
    have := Ideal.map_mono (f := (σ.symm : R →+* R)) (Ideal.le_of_dvd h)
    rw [Ideal.map_of_equiv, Ideal.map_of_equiv] at this
    exact Ideal.dvd_iff_le.2 this
  · intro h
    exact Ideal.dvd_iff_le.2 (Ideal.map_mono (Ideal.le_of_dvd h))

omit [IsDedekindDomain R] in
theorem map_ne_bot (σ : R ≃+* R) {I : Ideal R} (hI : I ≠ ⊥) : I.map (σ : R →+* R) ≠ ⊥ := fun h =>
  hI ((Ideal.map_eq_bot_iff_of_injective σ.injective).1 h)

theorem count_map (σ : R ≃+* R) (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk v.asIdeal).count (Associates.mk (I.map (σ : R →+* R))).factors =
      (Associates.mk (comapPrime σ v).asIdeal).count (Associates.mk I).factors := by
  have hI' : Associates.mk (I.map (σ : R →+* R)) ≠ 0 := by rw [Ne, Associates.mk_eq_zero]; exact map_ne_bot σ hI
  have hI0 : Associates.mk I ≠ 0 := by rw [Ne, Associates.mk_eq_zero]; exact hI
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le hI' v.associates_irreducible, ← Associates.prime_pow_dvd_iff_le hI0 (comapPrime σ v).associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd, ← map_comapPrime σ v, ← Ideal.map_pow,
    map_dvd_map_iff]

end IsDedekindDomain.selmerGroup.K3aPf

end

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
namespace CGF
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

open scoped nonZeroDivisors

section Fidl'
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (L : Type*) [Field L] [Algebra R' L] [IsFractionRing R' L]

theorem FractionalIdeal.ringEquivOfRingEquiv_coeIdeal (g : R ≃+* R') (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L g (I : FractionalIdeal R⁰ K) =
      ((I.map (g : R →+* R') : Ideal R') : FractionalIdeal R'⁰ L) := by
  ext x
  rw [← FractionalIdeal.mem_coe, ← FractionalIdeal.mem_coe,
    FractionalIdeal.ringEquivOfRingEquiv_apply, FractionalIdeal.coe_mk,
    FractionalIdeal.val_eq_coe]
  simp only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨-, ⟨a, haI, rfl⟩, rfl⟩
    exact ⟨g a, Ideal.mem_map_of_mem _ haI,
      by rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨b, hbI, rfl⟩
    obtain ⟨a, haI, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ g.surjective).mp hbI
    exact ⟨algebraMap R K a, ⟨a, haI, rfl⟩,
      by rw [LinearEquiv.coe_coe, IsFractionRing.semilinearEquivOfRingEquiv_apply,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]⟩

end Fidl'

section ClassGroupFunctoriality'
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']

theorem ClassGroup.mulEquiv_mk_eq_mk (g : R ≃+* R')
    {I : (FractionalIdeal R⁰ (FractionRing R))ˣ}
    {J : (FractionalIdeal R'⁰ (FractionRing R'))ˣ}
    (hIJ : FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing R') g
        (I : FractionalIdeal R⁰ (FractionRing R)) = (J : FractionalIdeal R'⁰ (FractionRing R'))) :
    ClassGroup.mulEquiv g (ClassGroup.mk _ I) = ClassGroup.mk _ J := by
  have hself : ∀ (J' : (FractionalIdeal R'⁰ (FractionRing R'))ˣ),
      ClassGroup.equiv (R := R') (FractionRing R') (ClassGroup.mk _ J') =
        QuotientGroup.mk' _ J' := by
    intro J'
    rw [ClassGroup.equiv_mk]
    congr 1
    rw [← Units.val_inj, Units.coe_mapEquiv]
    simp [FractionalIdeal.canonicalEquiv_self]
  rw [ClassGroup.mulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, ClassGroup.equiv_mk,
    show Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) (FractionRing R)))
        I = I by
      rw [← Units.val_inj, Units.coe_mapEquiv]
      simp [FractionalIdeal.canonicalEquiv_self],
    QuotientGroup.congr_mk']
  rw [MulEquiv.symm_apply_eq, hself]
  congr 1
  rw [← Units.val_inj, Units.coe_mapEquiv]
  exact hIJ

def Ideal.mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) : (Ideal R')⁰ :=
  ⟨(P : Ideal R).map (g : R →+* R'), by
    have hinj : Function.Injective ((g : R →+* R') : R → R') := g.injective
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun hbot => ?_
    refine mem_nonZeroDivisors_iff_ne_zero.mp P.2 ?_
    rw [Ideal.zero_eq_bot] at hbot ⊢
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot⟩

@[scoped simp] lemma Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal"
variable [IsDedekindDomain R] [IsDedekindDomain R']

theorem ClassGroup.mulEquiv_mk0 (g : R ≃+* R') (P : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 P) = ClassGroup.mk0 (Ideal.mapNonZero g P) := by
  show ClassGroup.mulEquiv g (ClassGroup.mk _ (FractionalIdeal.mk0 (FractionRing R) P)) =
    ClassGroup.mk _ (FractionalIdeal.mk0 (FractionRing R') (Ideal.mapNonZero g P))
  refine ClassGroup.mulEquiv_mk_eq_mk g ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0,
    FractionalIdeal.ringEquivOfRingEquiv_coeIdeal, Ideal.coe_mapNonZero]

theorem ClassGroup.mulEquiv_refl_apply (C : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) C = C := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero,
    show ((RingEquiv.refl R : R ≃+* R) : R →+* R) = RingHom.id R from RingHom.ext fun _ => rfl,
    Ideal.map_id]

theorem ClassGroup.mulEquiv_trans_apply {R'' : Type*} [CommRing R''] [IsDomain R'']
    [IsDedekindDomain R''] (g : R ≃+* R') (h : R' ≃+* R'') (C : ClassGroup R) :
    ClassGroup.mulEquiv (g.trans h) C = ClassGroup.mulEquiv h (ClassGroup.mulEquiv g C) := by
  obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0, ClassGroup.mulEquiv_mk0, ClassGroup.mulEquiv_mk0]
  congr 1
  refine Subtype.ext ?_
  rw [Ideal.coe_mapNonZero, Ideal.coe_mapNonZero, Ideal.coe_mapNonZero,
    show ((g.trans h : R ≃+* R'') : R →+* R'') = (h : R' →+* R'').comp (g : R →+* R') from
      RingHom.ext fun _ => rfl,
    ← Ideal.map_map]

end ClassGroupFunctoriality'
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal"

end IsDedekindDomain.selmerGroup.K3aPf.CGF
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

theorem valuation_map_eq (σR : R ≃+* R) (σK : K ≃+* K) (hσ : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (v : HeightOneSpectrum R) (y : K) : v.valuation K (σK y) = (comapPrime σR v).valuation K y := by
  classical
  obtain ⟨⟨r, s⟩, hrs⟩ : ∃ q : R × R⁰, y * algebraMap R K q.2 = algebraMap R K q.1 := ⟨IsLocalization.sec R⁰ y, IsLocalization.sec_spec _ _⟩
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hσs : σR s ∈ R⁰ := mem_nonZeroDivisors_of_ne_zero (by simpa using hs0)
  have hy : y = IsLocalization.mk' K r s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]; exact hrs
  have hσy : σK y = IsLocalization.mk' K (σR r) ⟨σR s, hσs⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    change σK y * algebraMap R K (σR s) = algebraMap R K (σR r)
    rw [← hσ, ← hσ, ← map_mul, hrs]
  rw [hσy, hy, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk']

  have key : ∀ a : R, v.intValuation (σR a) = (comapPrime σR v).intValuation a := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    have hσa : σR a ≠ 0 := by simpa using ha
    rw [HeightOneSpectrum.intValuation_if_neg _ hσa, HeightOneSpectrum.intValuation_if_neg _ ha]
    congr 3
    rw [show (Ideal.span {σR a} : Ideal R) = (Ideal.span {a}).map (σR : R →+* R) by rw [Ideal.map_span, Set.image_singleton]; rfl]
    exact_mod_cast count_map σR v (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ha)
  rw [key, show ((⟨σR s, hσs⟩ : R⁰) : R) = σR s from rfl, key]

theorem valuationOfNeZero_map_eq (σR : R ≃+* R) (σK : K ≃+* K) (hσ : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (v : HeightOneSpectrum R) (y : Kˣ) : v.valuationOfNeZero (Units.map (σK : K →* K) y) = (comapPrime σR v).valuationOfNeZero y := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq, Units.coe_map]
  exact valuation_map_eq K σR σK hσ v y

theorem count_spanSingleton_map (σR : R ≃+* R) (σK : K ≃+* K) (hσ : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (v : HeightOneSpectrum R) (y : Kˣ) :
    count K v (spanSingleton R⁰ ((Units.map (σK : K →* K) y : Kˣ) : K)) = count K (comapPrime σR v) (spanSingleton R⁰ (y : K)) := by
  have h1 := toAdd_valuationOfNeZero_eq_neg_count v (Units.map (σK : K →* K) y)
  have h2 := toAdd_valuationOfNeZero_eq_neg_count (comapPrime σR v) y
  rw [valuationOfNeZero_map_eq K σR σK hσ] at h1
  omega

theorem count_coe_map (σ : R ≃+* R) (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    count K v ((I.map (σ : R →+* R) : Ideal R) : FractionalIdeal R⁰ K) = count K (comapPrime σ v) (I : FractionalIdeal R⁰ K) := by
  rw [count_coe K v (by rw [Ideal.zero_eq_bot]; exact map_ne_bot σ hI), count_coe K _ (by rw [Ideal.zero_eq_bot]; exact hI)]
  exact_mod_cast count_map σ v hI

theorem mulEquiv_primeClass_comapPrime (σ : R ≃+* R) (v : HeightOneSpectrum R) :
    ClassGroup.mulEquiv σ (primeClass (comapPrime σ v)) = primeClass v := by
  rw [primeClass, CGF.ClassGroup.mulEquiv_mk0, primeClass]
  congr 1
  exact Subtype.ext (map_comapPrime σ v)

end IsDedekindDomain.selmerGroup.K3aPf
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ) [Fact (0 < n)]

theorem exists_of_mem_sClasses {c : ClassGroup R} (hc : c ∈ sClasses S) :
    ∃ J : (FractionalIdeal R⁰ K)ˣ, (∀ v ∉ S, count K v (Units.val J) = 0) ∧ ClassGroup.mk K J = c := by
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨v, hv, rfl⟩ := hc
    refine ⟨primeUnit K v, fun w hw => ?_, mk_primeUnit K v⟩
    change count K w (v.asIdeal : FractionalIdeal R⁰ K) = 0
    exact count_maximal_coprime K w (fun h => hw (h ▸ hv))
  | one => exact ⟨1, fun v _ => by rw [Units.val_one, count_one], map_one _⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨J, hJ, rfl⟩ := iha
    obtain ⟨J', hJ', rfl⟩ := ihb
    exact ⟨J * J', fun v hv => by rw [Units.val_mul, count_mul K v J.ne_zero J'.ne_zero, hJ v hv, hJ' v hv, add_zero], map_mul _ _ _⟩
  | inv a _ iha =>
    obtain ⟨J, hJ, rfl⟩ := iha
    exact ⟨J⁻¹, fun v hv => by rw [Units.val_inv_eq_inv_val, count_inv, hJ v hv, neg_zero], map_inv _ _⟩

theorem exists_eq_spanSingleton_of_mk_eq_one {I : (FractionalIdeal R⁰ K)ˣ} (hI : ClassGroup.mk K I = 1) :
    ∃ w : Kˣ, (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ (w : K) := by
  obtain ⟨w, hw⟩ := (ClassGroup.mk_eq_one_iff.1 hI).principal
  have hw' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ w := by
    apply FractionalIdeal.coeToSubmodule_injective
    change ((I : FractionalIdeal R⁰ K) : Submodule R K) = ((spanSingleton R⁰ w : FractionalIdeal R⁰ K) : Submodule R K)
    rw [coe_spanSingleton]
    exact hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, spanSingleton_zero] at hw'
    exact I.ne_zero hw'
  exact ⟨Units.mk0 w hw0, hw'⟩

theorem mem_range_connectingHom_iff (c : ClassGroupModS S) : c ∈ (connectingHom K S n).range ↔ c ^ n = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [connectingHom_apply, ← radClass_npow K S n (isSel_rep K S n x), radClass_pow]
  · intro hc

    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨P, rfl⟩ := ClassGroup.mk0_surjective c₀
    set B : (FractionalIdeal R⁰ K)ˣ := FractionalIdeal.mk0 K P with hBdef
    rw [← ClassGroup.mk_mk0 K] at hc ⊢

    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← map_pow] at hc
    obtain ⟨J, hJ, hJB⟩ := exists_of_mem_sClasses K S hc
    have h1 : ClassGroup.mk K (B ^ n * J⁻¹) = 1 := by rw [map_mul, map_inv, ← hJB, mul_inv_cancel]
    obtain ⟨x₀, hx₀⟩ := exists_eq_spanSingleton_of_mk_eq_one K h1
    have hcount : ∀ v, count K v (spanSingleton R⁰ (x₀ : K)) = n * count K v (Units.val B) - count K v (Units.val J) := fun v => by
      rw [← hx₀, Units.val_mul, Units.val_inv_eq_inv_val, count_mul K v (B ^ n).ne_zero (inv_ne_zero J.ne_zero), count_inv,
        Units.val_pow_eq_pow_val, count_pow, sub_eq_add_neg]
    have hsel : IsSel K S n x₀ := fun v hv => ⟨count K v (Units.val B), by rw [hcount, hJ v hv, sub_zero]⟩
    refine ⟨⟨QuotientGroup.mk x₀, mk_mem_of_isSel K S n hsel⟩, ?_⟩
    rw [connectingHom_apply_mk K S n hsel]

    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
    let Js : (FractionalIdeal R⁰ K)ˣ := ∏ᶠ v, primeUnit K v ^ (if v ∈ S then count K v (Units.val B) else 0)
    have hJs_supp : ∀ᶠ v in Filter.cofinite, (if v ∈ S then count K v (Units.val B) else 0) = 0 :=
      (finite_factors (Units.val B)).mono fun v hv => by simp [hv]
    have hJs_count : ∀ v, count K v (Units.val Js) = if v ∈ S then count K v (Units.val B) else 0 := fun v => by
      change count K v ((∏ᶠ v, primeUnit K v ^ (if v ∈ S then count K v (Units.val B) else 0) : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = _
      rw [coe_finprod_primeUnit_zpow, count_finprod K v _ hJs_supp]
    have hprod : radU K S n x₀ * Js = B := by
      apply Units.ext
      apply eq_of_count_eq K (mul_ne_zero (rad_ne_zero K S n _) Js.ne_zero) B.ne_zero
      intro v
      change count K v (rad K S n x₀ * Units.val Js) = _
      rw [count_mul K v (rad_ne_zero K S n _) Js.ne_zero, count_rad, hJs_count, radExp]
      split_ifs with hv
      · simp
      · rw [hcount, hJ v hv, sub_zero, add_zero, mul_comm, Int.mul_ediv_cancel _ hn]
    have hJs_mem : ClassGroup.mk K Js ∈ sClasses S := mk_mem_sClasses K S Js fun v hv => by rw [hJs_count, if_neg hv]
    change (QuotientGroup.mk (ClassGroup.mk K (radU K S n x₀)) : ClassGroupModS S) = QuotientGroup.mk (ClassGroup.mk K (FractionalIdeal.mk0 K P))
    rw [show FractionalIdeal.mk0 K P = radU K S n x₀ * Js from hprod.symm, map_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 hJs_mem, mul_one]

theorem count_eq_zero_of_mem_unit {u : Kˣ} (hu : u ∈ S.unit K) (v : HeightOneSpectrum R) (hv : v ∉ S) :
    count K v (spanSingleton R⁰ (u : K)) = 0 := by
  have h1 : v.valuationOfNeZero u = 1 := by
    apply WithZero.coe_injective
    rw [HeightOneSpectrum.valuationOfNeZero_eq]
    exact hu v hv
  have := toAdd_valuationOfNeZero_eq_neg_count v u
  rw [h1, toAdd_one] at this
  omega

theorem mem_unit_of_count_eq_zero {u : Kˣ} (hu : ∀ v ∉ S, count K v (spanSingleton R⁰ (u : K)) = 0) : u ∈ S.unit K := fun v hv => by
  have := toAdd_valuationOfNeZero_eq_neg_count v u
  rw [hu v hv, neg_zero] at this
  have h1 : v.valuationOfNeZero u = 1 := by
    rw [← ofAdd_toAdd (v.valuationOfNeZero u), this, ofAdd_zero]
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, h1]
  rfl

end IsDedekindDomain.selmerGroup.K3aPf
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ) [Fact (0 < n)]

omit [Fact (0 < n)] in

theorem radClass_eq_one_of_mem_unit {u : Kˣ} (hu : u ∈ S.unit K) : radClass K S n u = 1 := by
  have hrad : radU K S n u = 1 := by
    apply Units.ext
    apply eq_of_count_eq K (rad_ne_zero K S n u) one_ne_zero
    intro v
    rw [count_one]
    rw [count_rad, radExp]
    split_ifs with hv
    · rfl
    · rw [count_eq_zero_of_mem_unit K S hu v hv, Int.zero_ediv]
  rw [radClass_eq, hrad, map_one, QuotientGroup.mk_one]

omit [Fact (0 < n)] in
theorem isSel_of_mem_unit {u : Kˣ} (hu : u ∈ S.unit K) : IsSel K S n u := fun v hv => by
  rw [count_eq_zero_of_mem_unit K S hu v hv]; exact dvd_zero _

theorem connectingHom_eq_one_iff (x : ↥(Sel K S n)) :
    connectingHom K S n x = 1 ↔ ∃ u : ↥(S.unit K), (QuotientGroup.mk (u : Kˣ) : Qn K n) = x.1 := by
  constructor
  · intro h
    rw [connectingHom_apply, radClass_eq, QuotientGroup.eq_one_iff] at h
    obtain ⟨J, hJ, hJx⟩ := exists_of_mem_sClasses K S h

    have h1 : ClassGroup.mk K (radU K S n (rep K S n x) * J⁻¹) = 1 := by rw [map_mul, map_inv, hJx, mul_inv_cancel]
    obtain ⟨w, hw⟩ := exists_eq_spanSingleton_of_mk_eq_one K h1

    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
    have hx₀ := isSel_rep K S n x
    have hcountw : ∀ v ∉ S, count K v (spanSingleton R⁰ ((rep K S n x : Kˣ) : K)) = n * count K v (spanSingleton R⁰ (w : K)) := by
      intro v hv
      have hc := congrArg (count K v) hw
      rw [Units.val_mul, Units.val_inv_eq_inv_val] at hc
      change count K v (rad K S n (rep K S n x) * (Units.val J)⁻¹) = _ at hc
      rw [count_mul K v (rad_ne_zero K S n _) (inv_ne_zero J.ne_zero), count_inv] at hc
      rw [count_rad, radExp, if_neg hv, hJ v hv, neg_zero, add_zero] at hc
      rw [← hc, Int.mul_ediv_cancel' (hx₀ v hv)]
    let u : Kˣ := rep K S n x * (w ^ n)⁻¹
    have hu : u ∈ S.unit K := mem_unit_of_count_eq_zero K S fun v hv => by
      change count K v (spanSingleton R⁰ (((rep K S n x * (w ^ n)⁻¹ : Kˣ)) : K)) = 0
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← spanSingleton_mul_spanSingleton,
        count_mul K v (spanSingleton_ne_zero_iff.2 (rep K S n x).ne_zero) (spanSingleton_ne_zero_iff.2 (inv_ne_zero (pow_ne_zero _ w.ne_zero))),
        ← spanSingleton_inv, count_inv, ← spanSingleton_pow, count_pow, hcountw v hv]
      ring
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [← mk_rep K S n x]
    apply QuotientGroup.eq.2
    refine ⟨w, ?_⟩
    change w ^ n = (rep K S n x * (w ^ n)⁻¹)⁻¹ * rep K S n x
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨u, hu⟩
    have hmem : (QuotientGroup.mk (u : Kˣ) : Qn K n) ∈ Sel K S n := hu ▸ x.2
    have : x = ⟨QuotientGroup.mk (u : Kˣ), hmem⟩ := Subtype.ext hu.symm
    rw [this, connectingHom_apply_mk K S n (isSel_of_mem_unit K S n u.2), radClass_eq_one_of_mem_unit K S n u.2]

end IsDedekindDomain.selmerGroup.K3aPf
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ) [Fact (0 < n)]

theorem mem_range_of_mk_eq_one (u : ↥(S.unit K)) (h : (QuotientGroup.mk (u : Kˣ) : Qn K n) = 1) :
    u ∈ (powMonoidHom n : ↥(S.unit K) →* ↥(S.unit K)).range := by
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 ((QuotientGroup.eq_one_iff _).1 h)
  rw [powMonoidHom_apply] at hz
  have hzunit : z ∈ S.unit K := fun v hv => by
    have hu := u.2 v hv
    rw [← hz, Units.val_pow_eq_pow_val, map_pow] at hu
    have hne : (n : ℕ) ≠ 0 := (Fact.out : 0 < n).ne'
    exact (pow_eq_one_iff.1 hu).resolve_right hne
  exact ⟨⟨z, hzunit⟩, Subtype.ext (show ((powMonoidHom n (⟨z, hzunit⟩ : ↥(S.unit K)) : ↥(S.unit K)) : Kˣ) = (u : Kˣ) from hz)⟩

end IsDedekindDomain.selmerGroup.K3aPf
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationOfNeZero_eq HeightOneSpectrum.ext HeightOneSpectrum.valuation_of_mk' HeightOneSpectrum.intValuation_if_neg selmerGroup mk HeightOneSpectrum"
namespace selmerGroup
p2m_export "IsDedekindDomain.selmerGroup" "fromUnit_ker valuation_ker_eq valuation toAdd_valuationOfNeZero_eq_neg_count primeClass sClasses ClassGroupModS radExp rad count_rad rad_ne_zero eq_of_count_eq radClass IsSel mk_spanSingleton primeUnit mk_primeUnit hasFiniteMulSupport_primeUnit_zpow coe_finprod_primeUnit_zpow eq_finprod_primeUnit mk_mem_sClasses radU radClass_eq radClass_pow isSel_of_mk_mem mk_mem_of_isSel Qn Sel radClass_npow rep mk_rep isSel_rep connectingHom connectingHom_apply_mk connectingHom_apply"
namespace K3aPf
p2m_open "IsDedekindDomain.selmerGroup IsDedekindDomain"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain FractionalIdeal"
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

theorem mk_mem_sClasses_of (I : (FractionalIdeal R⁰ K)ˣ) (hI : ∀ v, count K v (Units.val I) ≠ 0 → primeClass v ∈ sClasses S) :
    ClassGroup.mk K I ∈ sClasses S := by
  have hfin := hasFiniteMulSupport_primeUnit_zpow K (fun v => count K v (Units.val I)) (finite_factors _)
  rw [eq_finprod_primeUnit K I (fun v => count K v (Units.val I)) (fun v => rfl), MonoidHom.map_finprod _ hfin]
  refine finprod_induction (· ∈ sClasses S) (Subgroup.one_mem _) (fun _ _ => Subgroup.mul_mem _) fun v => ?_
  by_cases hv : count K v (Units.val I) = 0
  · change ClassGroup.mk K (primeUnit K v ^ count K v (Units.val I)) ∈ sClasses S
    rw [hv, zpow_zero, map_one]
    exact Subgroup.one_mem _
  · rw [map_zpow, mk_primeUnit]
    exact Subgroup.zpow_mem _ (hI v hv) _

theorem exists_eq_spanSingleton_of_mk_eq_one' {I : (FractionalIdeal R⁰ K)ˣ} (hI : ClassGroup.mk K I = 1) :
    ∃ w : Kˣ, (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ (w : K) := by
  obtain ⟨w, hw⟩ := (ClassGroup.mk_eq_one_iff.1 hI).principal
  have hw' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ w := by
    apply FractionalIdeal.coeToSubmodule_injective
    change ((I : FractionalIdeal R⁰ K) : Submodule R K) = ((spanSingleton R⁰ w : FractionalIdeal R⁰ K) : Submodule R K)
    rw [coe_spanSingleton]
    exact hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, spanSingleton_zero] at hw'
    exact I.ne_zero hw'
  exact ⟨Units.mk0 w hw0, hw'⟩

variable [Fact (0 < n)]

theorem connectingHom_map'
    (σR : R ≃+* R) (σK : K ≃+* K) (hσ : ∀ r : R, σK (algebraMap R K r) = algebraMap R K (σR r))
    (hσS : sClasses S ≤ (sClasses S).comap (ClassGroup.mulEquiv σR).toMonoidHom)
    (x : ↥(Sel K S n))
    (hx : (QuotientGroup.map _ ((powMonoidHom n : Kˣ →* Kˣ).range) (Units.map (σK : K →* K))
        (by rintro _ ⟨y, rfl⟩; exact ⟨Units.map (σK : K →* K) y, by ext; simp⟩) x.1) ∈ Sel K S n) :
    connectingHom K S n ⟨_, hx⟩ = QuotientGroup.map _ _ (ClassGroup.mulEquiv σR).toMonoidHom hσS (connectingHom K S n x) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  set x₀ : Kˣ := rep K S n x with hx₀def
  have hmap : QuotientGroup.map _ ((powMonoidHom n : Kˣ →* Kˣ).range) (Units.map (σK : K →* K))
      (by rintro _ ⟨y, rfl⟩; exact ⟨Units.map (σK : K →* K) y, by ext; simp⟩) x.1 = QuotientGroup.mk (Units.map (σK : K →* K) x₀) := by
    conv_lhs => rw [← mk_rep K S n x]
    rfl
  have hsel₀ : IsSel K S n x₀ := isSel_rep K S n x
  have hsel' : IsSel K S n (Units.map (σK : K →* K) x₀) := isSel_of_mk_mem K S n (hmap ▸ hx)
  have hL : connectingHom K S n ⟨_, hx⟩ = radClass K S n (Units.map (σK : K →* K) x₀) := by
    have : (⟨_, hx⟩ : ↥(Sel K S n)) = ⟨QuotientGroup.mk (Units.map (σK : K →* K) x₀), hmap ▸ hx⟩ := Subtype.ext hmap
    rw [this, connectingHom_apply_mk K S n hsel']
  rw [hL, connectingHom_apply, ← hx₀def, radClass_eq, radClass_eq, QuotientGroup.map_mk, MulEquiv.coe_toMonoidHom]

  obtain ⟨P, hP⟩ := ClassGroup.mk0_surjective (ClassGroup.mk K (radU K S n x₀))
  rw [← hP, CGF.ClassGroup.mulEquiv_mk0, ← ClassGroup.mk_mk0 K]

  have h1 : ClassGroup.mk K (radU K S n x₀ * (FractionalIdeal.mk0 K P)⁻¹) = 1 := by
    rw [map_mul, map_inv, ClassGroup.mk_mk0, hP, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_eq_spanSingleton_of_mk_eq_one' K h1
  have hP0 : (P : Ideal R) ≠ ⊥ := nonZeroDivisors.ne_zero P.2
  have hcountP : ∀ w, count K w ((P : Ideal R) : FractionalIdeal R⁰ K) = radExp K S n x₀ w - count K w (spanSingleton R⁰ (t : K)) := by
    intro w
    have hc := congrArg (count K w) ht
    rw [Units.val_mul, Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0] at hc
    change count K w (rad K S n x₀ * ((P : Ideal R) : FractionalIdeal R⁰ K)⁻¹) = _ at hc
    rw [count_mul K w (rad_ne_zero K S n _) (inv_ne_zero (coeIdeal_ne_zero.2 hP0)), count_inv, count_rad] at hc
    omega

  let Ut : (FractionalIdeal R⁰ K)ˣ := Units.mk0 (spanSingleton R⁰ ((Units.map (σK : K →* K) t : Kˣ) : K))
    (spanSingleton_ne_zero_iff.2 (Units.map (σK : K →* K) t).ne_zero)
  let E' : (FractionalIdeal R⁰ K)ˣ := (radU K S n (Units.map (σK : K →* K) x₀))⁻¹ * FractionalIdeal.mk0 K (CGF.Ideal.mapNonZero σR P) * Ut
  have hmapP0 : ((P : Ideal R).map (σR : R →+* R)) ≠ ⊥ := map_ne_bot σR hP0
  have hE'count : ∀ v, count K v (Units.val E') = -radExp K S n (Units.map (σK : K →* K) x₀) v + radExp K S n x₀ (comapPrime σR v) := by
    intro v
    change count K v ((rad K S n (Units.map (σK : K →* K) x₀))⁻¹ * (FractionalIdeal.mk0 K (CGF.Ideal.mapNonZero σR P) : FractionalIdeal R⁰ K) *
      spanSingleton R⁰ ((Units.map (σK : K →* K) t : Kˣ) : K)) = _
    rw [FractionalIdeal.coe_mk0, CGF.Ideal.coe_mapNonZero,
      count_mul K v (mul_ne_zero (inv_ne_zero (rad_ne_zero K S n _)) (coeIdeal_ne_zero.2 hmapP0)) (spanSingleton_ne_zero_iff.2 (Units.map (σK : K →* K) t).ne_zero),
      count_mul K v (inv_ne_zero (rad_ne_zero K S n _)) (coeIdeal_ne_zero.2 hmapP0), count_inv, count_rad,
      count_coe_map K σR v hP0, count_spanSingleton_map K σR σK hσ v t, hcountP]
    ring
  have hE'exp : ∀ v, radExp K S n (Units.map (σK : K →* K) x₀) v = if v ∈ S then 0 else count K (comapPrime σR v) (spanSingleton R⁰ (x₀ : K)) / n := by
    intro v
    rw [radExp, count_spanSingleton_map K σR σK hσ v x₀]
  have hE'mem : ClassGroup.mk K E' ∈ sClasses S := by
    apply mk_mem_sClasses_of K S E'
    intro v hv
    rw [hE'count, hE'exp, radExp] at hv
    by_cases hvS : v ∈ S
    · exact Subgroup.subset_closure (Set.mem_image_of_mem primeClass hvS)
    · by_cases hcvS : comapPrime σR v ∈ S
      · have := hσS (Subgroup.subset_closure (Set.mem_image_of_mem primeClass hcvS))
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mulEquiv_primeClass_comapPrime] at this
        exact this
      · exfalso
        rw [if_neg hvS, if_neg hcvS] at hv
        exact hv (by ring)

  apply QuotientGroup.eq.2
  rw [← map_inv, ← map_mul]
  have hE'eq : (radU K S n (Units.map (σK : K →* K) x₀))⁻¹ * FractionalIdeal.mk0 K (CGF.Ideal.mapNonZero σR P) = E' * Ut⁻¹ := by
    simp only [E', mul_inv_cancel_right]
  rw [hE'eq, map_mul, map_inv, mk_spanSingleton, inv_one, mul_one]
  exact hE'mem

end IsDedekindDomain.selmerGroup.K3aPf
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem LevelArith.finiteDimensional_unitsModP_sClass_selmerRep"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_eq_one_of_mem inflLevel_ρ_apply repModP repTorsionP ringOfIntegersAut placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset primeClass sPrimeClasses sPrimeClassesSubmodule mem_sPrimeClassesSubmodule sClassGroupRep unitsModP sClassTorsionP placesAbove unitsModPow unitsModPow.mk unitsModPow.mk_surjective smul_mk selmer selmerStable mem_selmerStable_iff selmerSubmodule selmerRepField fromSUnitsModP fromSUnitsModP_hom_mk selmerRep unitsModPToSelmerRep sPrimeClasses_eq_closure selmerStable_eq_selmer finiteDimensional_unitsModP_sClass_selmerRep"
namespace K3b
p2m_open "NumberField.LevelArith NumberField"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField"
p2m_open_scoped "nonZeroDivisors NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith Classical"

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]

omit [NumberField F] in

theorem placesAbove_placesOverPrimesFinset (S : Finset Nat.Primes) :
    SUnits.placesAbove E F (placesOverPrimesFinset E S) = placesOverPrimes F (S : Set Nat.Primes) := by
  ext w
  rw [SUnits.mem_placesAbove, mem_placesOverPrimesFinset, mem_placesOverPrimes_iff, mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  change ((q : ℕ) : 𝓞 E) ∈ (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 F))) ↔ _
  rw [Ideal.mem_comap, map_natCast]

omit [NumberField E] [NumberField F] in

theorem under_comapPrime (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) :
    (comapPrime (ringOfIntegersAut E F σ) w).under (𝓞 E) = w.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  change (w.asIdeal.comap ((ringOfIntegersAut E F σ : 𝓞 F ≃+* 𝓞 F) : 𝓞 F →+* 𝓞 F)).comap (algebraMap (𝓞 E) (𝓞 F)) =
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 F))
  rw [Ideal.comap_comap]
  congr 1
  ext e
  exact σ.commutes (e : E)

omit [NumberField E] [NumberField F] in
theorem comapPrime_mem_placesAbove_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) :
    comapPrime (ringOfIntegersAut E F σ) w ∈ SUnits.placesAbove E F S ↔ w ∈ SUnits.placesAbove E F S := by
  rw [SUnits.mem_placesAbove, SUnits.mem_placesAbove, under_comapPrime]

omit [NumberField E] [NumberField F] in
theorem comapPrime_comapPrime_symm (σ : 𝓞 F ≃+* 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) : comapPrime σ (comapPrime σ.symm w) = w := by
  apply HeightOneSpectrum.ext
  change (w.asIdeal.comap ((σ.symm : 𝓞 F ≃+* 𝓞 F) : 𝓞 F →+* 𝓞 F)).comap ((σ : 𝓞 F ≃+* 𝓞 F) : 𝓞 F →+* 𝓞 F) = w.asIdeal
  exact Ideal.comap_of_equiv σ

omit [NumberField E] [NumberField F] in
theorem ringOfIntegersAut_symm (σ : F ≃ₐ[E] F) : (ringOfIntegersAut E F σ).symm = ringOfIntegersAut E F σ⁻¹ := rfl

theorem sClasses_le_comap (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : F ≃ₐ[E] F) :
    sClasses (SUnits.placesAbove E F S) ≤ (sClasses (SUnits.placesAbove E F S)).comap (ClassGroup.mulEquiv (ringOfIntegersAut E F σ)).toMonoidHom := by
  rw [sClasses, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    ← comapPrime_comapPrime_symm F (ringOfIntegersAut E F σ) w, mulEquiv_primeClass_comapPrime]
  refine Subgroup.subset_closure (Set.mem_image_of_mem _ ?_)
  rw [ringOfIntegersAut_symm, comapPrime_mem_placesAbove_iff]
  exact hw

omit [NumberField E] [NumberField F] in

theorem algebraMap_ringOfIntegersAut (σ : F ≃ₐ[E] F) (r : 𝓞 F) :
    (σ : F ≃+* F) (algebraMap (𝓞 F) F r) = algebraMap (𝓞 F) F (ringOfIntegersAut E F σ r) := rfl

end NumberField.LevelArith.K3b
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem LevelArith.finiteDimensional_unitsModP_sClass_selmerRep"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_eq_one_of_mem inflLevel_ρ_apply repModP repTorsionP ringOfIntegersAut placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset primeClass sPrimeClasses sPrimeClassesSubmodule mem_sPrimeClassesSubmodule sClassGroupRep unitsModP sClassTorsionP placesAbove unitsModPow unitsModPow.mk unitsModPow.mk_surjective smul_mk selmer selmerStable mem_selmerStable_iff selmerSubmodule selmerRepField fromSUnitsModP fromSUnitsModP_hom_mk selmerRep unitsModPToSelmerRep sPrimeClasses_eq_closure selmerStable_eq_selmer finiteDimensional_unitsModP_sClass_selmerRep"
namespace K3b
p2m_open "NumberField.LevelArith NumberField"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField"
p2m_open_scoped "nonZeroDivisors NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith Classical"

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] (S : Finset Nat.Primes) (p : ℕ)

abbrev S' : Set (HeightOneSpectrum (𝓞 F)) := SUnits.placesAbove E F (placesOverPrimesFinset E S)

abbrev V : Type := Additive (ClassGroup (𝓞 F)) ⧸ sPrimeClassesSubmodule E F (S : Set Nat.Primes)

def toV : ClassGroup (𝓞 F) →* Multiplicative (V E F S) where
  toFun c := Multiplicative.ofAdd (Submodule.Quotient.mk (Additive.ofMul c) : V E F S)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toV_apply (c : ClassGroup (𝓞 F)) :
    toV E F S c = Multiplicative.ofAdd (Submodule.Quotient.mk (Additive.ofMul c) : V E F S) := rfl

theorem sClasses_eq_sPrimeClasses : sClasses (S' E F S) = sPrimeClasses E F (S : Set Nat.Primes) := by
  rw [sPrimeClasses_eq_closure, sClasses, S', placesAbove_placesOverPrimesFinset]
  rfl

theorem mem_ker_toV_iff (c : ClassGroup (𝓞 F)) : toV E F S c = 1 ↔ c ∈ sClasses (S' E F S) := by
  rw [toV_apply, sClasses_eq_sPrimeClasses]
  change Multiplicative.ofAdd (Submodule.Quotient.mk (Additive.ofMul c) : V E F S) = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.mk_eq_zero, mem_sPrimeClassesSubmodule]
  rfl

def ψ : ClassGroupModS (S' E F S) →* Multiplicative (V E F S) :=
  QuotientGroup.lift _ (toV E F S) fun c hc => (mem_ker_toV_iff E F S c).2 hc

theorem ψ_mk (c : ClassGroup (𝓞 F)) : ψ E F S (QuotientGroup.mk c) = toV E F S c := rfl

theorem ψ_injective : Function.Injective (ψ E F S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective a
  rw [ψ_mk, mem_ker_toV_iff] at ha
  exact (QuotientGroup.eq_one_iff c).2 ha

theorem ψ_surjective : Function.Surjective (ψ E F S) := by
  intro v
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd v)
  exact ⟨QuotientGroup.mk (Additive.toMul a), by rw [ψ_mk, toV_apply]; exact congrArg Multiplicative.ofAdd ha⟩

variable [Fact p.Prime]

scoped instance : Fact (0 < p) := ⟨(Fact.out : p.Prime).pos⟩

def toSel (x : selmerRepField E F (placesOverPrimesFinset E S) p) : ↥(Sel F (S' E F S) p) :=
  ⟨Additive.toMul (x.1 : Additive (unitsModPow F p)),
    by
      have h := (mem_selmerStable_iff E F (placesOverPrimesFinset E S) p _).1 x.2 1
      rwa [one_smul] at h⟩

def gFun (x : selmerRepField E F (placesOverPrimesFinset E S) p) : V E F S :=
  Multiplicative.toAdd (ψ E F S (connectingHom F (S' E F S) p (toSel E F S p x)))

theorem gFun_add (x y : selmerRepField E F (placesOverPrimesFinset E S) p) : gFun E F S p (x + y) = gFun E F S p x + gFun E F S p y := by
  unfold gFun
  rw [← toAdd_mul, ← map_mul, ← map_mul]
  rfl

theorem nsmul_gFun (x : selmerRepField E F (placesOverPrimesFinset E S) p) : p • gFun E F S p x = 0 := by
  unfold gFun
  have h := ((mem_range_connectingHom_iff F (S' E F S) p _).1 ⟨toSel E F S p x, rfl⟩)
  rw [← toAdd_pow, ← map_pow, h, map_one, toAdd_one]

end NumberField.LevelArith.K3b
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem LevelArith.finiteDimensional_unitsModP_sClass_selmerRep"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_eq_one_of_mem inflLevel_ρ_apply repModP repTorsionP ringOfIntegersAut placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset primeClass sPrimeClasses sPrimeClassesSubmodule mem_sPrimeClassesSubmodule sClassGroupRep unitsModP sClassTorsionP placesAbove unitsModPow unitsModPow.mk unitsModPow.mk_surjective smul_mk selmer selmerStable mem_selmerStable_iff selmerSubmodule selmerRepField fromSUnitsModP fromSUnitsModP_hom_mk selmerRep unitsModPToSelmerRep sPrimeClasses_eq_closure selmerStable_eq_selmer finiteDimensional_unitsModP_sClass_selmerRep"
namespace K3b
p2m_open "NumberField.LevelArith NumberField"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField CategoryTheory"
p2m_open_scoped "nonZeroDivisors NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith Classical"

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] (S : Finset Nat.Primes) (p : ℕ) [Fact p.Prime]

abbrev X₁F : Rep (ZMod p) (F ≃ₐ[E] F) := repModP p (SUnits.sUnitsRep E F (placesOverPrimesFinset E S))
abbrev X₂F : Rep (ZMod p) (F ≃ₐ[E] F) := selmerRepField E F (placesOverPrimesFinset E S) p
abbrev X₃F : Rep (ZMod p) (F ≃ₐ[E] F) := repTorsionP p (sClassGroupRep E F (S : Set Nat.Primes))

theorem gFun_mem_torsionBy (x : X₂F E F S p) : gFun E F S p x ∈ Submodule.torsionBy ℤ (V E F S) (p : ℤ) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  exact nsmul_gFun E F S p x

def gAddHom : X₂F E F S p →+ ↥(Submodule.torsionBy ℤ (V E F S) (p : ℤ)) where
  toFun x := ⟨gFun E F S p x, gFun_mem_torsionBy E F S p x⟩
  map_zero' := by
    apply Subtype.ext
    have h := gFun_add E F S p 0 0
    rw [add_zero] at h
    change gFun E F S p 0 = 0
    exact (add_eq_left.1 h.symm)
  map_add' x y := Subtype.ext (gFun_add E F S p x y)

theorem gAddHom_apply_coe (x : X₂F E F S p) : ((gAddHom E F S p x : ↥(Submodule.torsionBy ℤ (V E F S) (p : ℤ))) : V E F S) = gFun E F S p x := rfl

theorem smul_eq_map (σ : F ≃ₐ[E] F) (q : unitsModPow F p) :
    σ • q = QuotientGroup.map _ ((powMonoidHom p : Fˣ →* Fˣ).range) (Units.map ((σ : F ≃+* F) : F →* F))
      (by rintro _ ⟨y, rfl⟩; exact ⟨Units.map ((σ : F ≃+* F) : F →* F) y, by ext; simp⟩) q := by
  obtain ⟨u, rfl⟩ := unitsModPow.mk_surjective F p q
  rw [smul_mk]
  exact congrArg (unitsModPow.mk F p) (Units.ext rfl)

theorem gFun_ρ (σ : F ≃ₐ[E] F) (x : X₂F E F S p) :
    gFun E F S p ((X₂F E F S p).ρ σ x) = (sClassGroupRep E F (S : Set Nat.Primes)).ρ σ (gFun E F S p x) := by

  have hx' : (QuotientGroup.map _ ((powMonoidHom p : Fˣ →* Fˣ).range) (Units.map ((σ : F ≃+* F) : F →* F))
      (by rintro _ ⟨y, rfl⟩; exact ⟨Units.map ((σ : F ≃+* F) : F →* F) y, by ext; simp⟩) (toSel E F S p x).1) ∈ Sel F (S' E F S) p := by
    rw [← smul_eq_map]
    exact (toSel E F S p ((X₂F E F S p).ρ σ x)).2
  have hsel : toSel E F S p ((X₂F E F S p).ρ σ x) = ⟨_, hx'⟩ := Subtype.ext (smul_eq_map E F p σ _)
  have hnat := connectingHom_map' F (S' E F S) p (ringOfIntegersAut E F σ) (σ : F ≃+* F) (algebraMap_ringOfIntegersAut E F σ)
    (sClasses_le_comap E F (placesOverPrimesFinset E S) σ) (toSel E F S p x) hx'
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (connectingHom F (S' E F S) p (toSel E F S p x))
  unfold gFun
  rw [hsel, hnat, ← hc, QuotientGroup.map_mk, ψ_mk, ψ_mk]
  rfl

def gHom : X₂F E F S p ⟶ X₃F E F S p :=
  Rep.ofHom ⟨(gAddHom E F S p).toZModLinearMap p, fun σ => LinearMap.ext fun x => Subtype.ext (by
    change gFun E F S p ((X₂F E F S p).ρ σ x) = (sClassGroupRep E F (S : Set Nat.Primes)).ρ σ (gFun E F S p x)
    exact gFun_ρ E F S p σ x)⟩

theorem gHom_hom_apply_val (x : X₂F E F S p) : Subtype.val ((gHom E F S p).hom x) = gFun E F S p x := rfl

end NumberField.LevelArith.K3b
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

noncomputable section

namespace NumberField
p2m_export "NumberField" "mk place SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem LevelArith.finiteDimensional_unitsModP_sClass_selmerRep"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_eq_one_of_mem inflLevel_ρ_apply repModP repTorsionP ringOfIntegersAut placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset primeClass sPrimeClasses sPrimeClassesSubmodule mem_sPrimeClassesSubmodule sClassGroupRep unitsModP sClassTorsionP placesAbove unitsModPow unitsModPow.mk unitsModPow.mk_surjective smul_mk selmer selmerStable mem_selmerStable_iff selmerSubmodule selmerRepField fromSUnitsModP fromSUnitsModP_hom_mk selmerRep unitsModPToSelmerRep sPrimeClasses_eq_closure selmerStable_eq_selmer finiteDimensional_unitsModP_sClass_selmerRep"
namespace K3b
p2m_open "NumberField.LevelArith NumberField"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField CategoryTheory"
p2m_open_scoped "nonZeroDivisors NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith Classical Pointwise"

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] (S : Finset Nat.Primes) (p : ℕ) [Fact p.Prime]

abbrev fHom : X₁F E F S p ⟶ X₂F E F S p := fromSUnitsModP E F (placesOverPrimesFinset E S) p

theorem smul_mem_unit {u : Fˣ} (hu : u ∈ (S' E F S).unit F) (σ : F ≃ₐ[E] F) : σ • u ∈ (S' E F S).unit F := by
  intro w hw
  change w.valuation F ((σ : F ≃+* F) (u : F)) = 1
  rw [valuation_map_eq F (ringOfIntegersAut E F σ) (σ : F ≃+* F) (algebraMap_ringOfIntegersAut E F σ)]
  exact hu _ (by rwa [comapPrime_mem_placesAbove_iff])

theorem mem_sUnits_of_mem_unit {u : Fˣ} (hu : u ∈ (S' E F S).unit F) : u ∈ SUnits.sUnits E F (placesOverPrimesFinset E S) := by
  rw [SUnits.mem_sUnits_iff]
  intro σ w hw
  exact smul_mem_unit E F S hu σ w (by rwa [SUnits.mem_placesAbove])

theorem mem_unit_of_mem_sUnits {u : Fˣ} (hu : u ∈ SUnits.sUnits E F (placesOverPrimesFinset E S)) : u ∈ (S' E F S).unit F := by
  intro w hw
  have := (SUnits.mem_sUnits_iff E F _ u).1 hu 1 w (by rwa [SUnits.mem_placesAbove] at hw)
  simpa using this

theorem gFun_eq_zero_iff (x : X₂F E F S p) : gFun E F S p x = 0 ↔ ∃ u : X₁F E F S p, (fHom E F S p).hom u = x := by
  unfold gFun
  rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff, map_eq_one_iff _ (ψ_injective E F S), connectingHom_eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hus : (u : Fˣ) ∈ SUnits.sUnits E F (placesOverPrimesFinset E S) := mem_sUnits_of_mem_unit E F S u.2
    refine ⟨Submodule.Quotient.mk ⟨Additive.ofMul (u : Fˣ), hus⟩, ?_⟩
    apply Subtype.ext
    rw [fromSUnitsModP_hom_mk]
    change Additive.ofMul (unitsModPow.mk F p (u : Fˣ)) = (x.1 : Additive (unitsModPow F p))
    exact congrArg Additive.ofMul hu
  · rintro ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    exact ⟨⟨SUnits.val E F _ v, mem_unit_of_mem_sUnits E F S (SUnits.val_mem E F _ v)⟩, rfl⟩

omit [NumberField E] [NumberField F] [Fact p.Prime] in

theorem mk_natCast_smul_eq_zero {k : Type} [CommRing k] {W : Type} [AddCommGroup W] {iW : Module k W} (p : ℕ) (w : W) :
    (Submodule.Quotient.mk ((p : k) • w) : W ⧸ ((p : k) • (⊤ : Submodule k W))) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)

theorem fHom_injective : Function.Injective (fHom E F S p).hom := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have h1 : (unitsModPow.mk F p (SUnits.val E F _ v)) = 1 := by
    have := congrArg (fun y : X₂F E F S p => Additive.toMul (y.1 : Additive (unitsModPow F p))) hu
    simp [fromSUnitsModP_hom_mk] at this
    exact this
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 (mem_range_of_mk_eq_one F (S' E F S) p ⟨SUnits.val E F _ v, mem_unit_of_mem_sUnits E F S (SUnits.val_mem E F _ v)⟩ h1)

  have hzs : (z : Fˣ) ∈ SUnits.sUnits E F (placesOverPrimesFinset E S) := mem_sUnits_of_mem_unit E F S z.2
  let w : SUnits.sUnitsRep E F (placesOverPrimesFinset E S) := ⟨Additive.ofMul (z : Fˣ), hzs⟩
  have hv : v = (p : ℤ) • w := by
    apply Subtype.ext
    change Additive.ofMul (SUnits.val E F _ v) = (p : ℤ) • Additive.ofMul (z : Fˣ)
    rw [← ofMul_zpow, zpow_natCast]
    exact congrArg Additive.ofMul (congrArg Subtype.val hz).symm
  rw [hv]
  exact mk_natCast_smul_eq_zero p w

theorem gHom_surjective : Function.Surjective (gHom E F S p).hom := by
  intro y

  obtain ⟨c, hc⟩ := ψ_surjective E F S (Multiplicative.ofAdd (y.1 : V E F S))
  have hcp : c ^ p = 1 := by
    apply ψ_injective E F S
    rw [map_pow, hc, map_one, ← ofAdd_nsmul]
    have hy : (p : ℤ) • (y.1 : V E F S) = 0 := (Submodule.mem_torsionBy_iff _ _).1 y.2
    rw [Nat.cast_smul_eq_nsmul] at hy
    exact congrArg Multiplicative.ofAdd hy
  obtain ⟨s, hs⟩ := (mem_range_connectingHom_iff F (S' E F S) p c).2 hcp

  have hs' : Additive.ofMul (s.1 : unitsModPow F p) ∈ selmerSubmodule E F (placesOverPrimesFinset E S) p := by
    change (s.1 : unitsModPow F p) ∈ selmerStable E F (placesOverPrimesFinset E S) p
    rw [selmerStable_eq_selmer]
    exact s.2
  refine ⟨⟨_, hs'⟩, Subtype.ext ?_⟩
  rw [gHom_hom_apply_val]
  unfold gFun
  have : toSel E F S p ⟨_, hs'⟩ = s := Subtype.ext rfl
  rw [this, hs, hc, toAdd_ofAdd]

end NumberField.LevelArith.K3b
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

namespace NumberField
p2m_export "NumberField" "mk place SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.mem_sUnits_iff SUnits.sUnitsRep SUnits.val SUnits.val_mem LevelArith.finiteDimensional_unitsModP_sClass_selmerRep"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_eq_one_of_mem inflLevel_ρ_apply repModP repTorsionP ringOfIntegersAut placesOverPrimes mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset primeClass sPrimeClasses sPrimeClassesSubmodule mem_sPrimeClassesSubmodule sClassGroupRep unitsModP sClassTorsionP placesAbove unitsModPow unitsModPow.mk unitsModPow.mk_surjective smul_mk selmer selmerStable mem_selmerStable_iff selmerSubmodule selmerRepField fromSUnitsModP fromSUnitsModP_hom_mk selmerRep unitsModPToSelmerRep sPrimeClasses_eq_closure selmerStable_eq_selmer finiteDimensional_unitsModP_sClass_selmerRep"
namespace K3b
p2m_open "NumberField.LevelArith NumberField"

p2m_open "IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField CategoryTheory"
p2m_open_scoped "nonZeroDivisors NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith Classical"

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] (S : Finset Nat.Primes) (p : ℕ) [Fact p.Prime]

theorem gFun_fHom (u : X₁F E F S p) : gFun E F S p ((fHom E F S p).hom u) = 0 := (gFun_eq_zero_iff E F S p _).2 ⟨u, rfl⟩

theorem fHom_gHom : fHom E F S p ≫ gHom E F S p = 0 := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun u => ?_
  exact Subtype.ext (gFun_fHom E F S p u)

noncomputable def XF : ShortComplex (Rep.{0} (ZMod p) (F ≃ₐ[E] F)) := ShortComplex.mk (fHom E F S p) (gHom E F S p) (fHom_gHom E F S p)

theorem range_eq_ker : LinearMap.range (fHom E F S p).hom.toLinearMap = LinearMap.ker (gHom E F S p).hom.toLinearMap := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨u, rfl⟩
    exact Subtype.ext (gFun_fHom E F S p u)
  · intro hx
    obtain ⟨u, hu⟩ := (gFun_eq_zero_iff E F S p x).1 (congrArg Subtype.val hx)
    exact ⟨u, hu⟩

variable {Γ : Type} [Group Γ] (φ : Γ →* (F ≃ₐ[E] F))

noncomputable def Xres : ShortComplex (Rep.{0} (ZMod p) Γ) := (XF E F S p).map (Rep.resFunctor φ)

theorem shortExact_Xres : (Xres E F S p φ).ShortExact := by
  haveI : Mono (Xres E F S p φ).f := (Rep.mono_iff_injective _).2 (fHom_injective E F S p)
  haveI : Epi (Xres E F S p φ).g := (Rep.epi_iff_surjective _).2 (gHom_surjective E F S p)
  refine ShortComplex.ShortExact.mk ?_
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep (ZMod p) Γ) (ModuleCat (ZMod p))),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact range_eq_ker E F S p

end NumberField.LevelArith.K3b
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF.Ideal P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.IsDedekindDomain.selmerGroup.K3aPf.CGF P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP.NumberField.LevelArith.K3b"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (selmerRep K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (unitsModP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
      Module.finrank (ZMod p) (sClassTorsionP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by
  haveI : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal :=
    ⟨fun s hs g => Subgroup.mem_subgroupOf.2 (by simpa using hnorm g g.2 s (Subgroup.mem_subgroupOf.1 hs))⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex := ⟨fun h0 => by
    have : (L.fixingSubgroup.relIndex K.fixingSubgroup) = 0 := h0
    rw [this, Nat.coprime_zero_left] at hcop
    omega⟩
  haveI : Finite (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  have hcop' : (Nat.card (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)).Coprime p := hcop

  haveI : FiniteDimensional (ZMod p) (NumberField.LevelArith.K3b.Xres ↥K ↥(levelField K L hKL) S p (levelGal K L hKL)).X₂ :=
    (NumberField.LevelArith.finiteDimensional_unitsModP_sClass_selmerRep S K L hKL (p := p)).2.2.2

  have hX := NumberField.LevelArith.K3b.shortExact_Xres ↥K ↥(levelField K L hKL) S p (levelGal K L hKL)
  have h₂ : ∀ s ∈ L.fixingSubgroup.subgroupOf K.fixingSubgroup, (selmerRep K L hKL S p).ρ s = 1 := fun s hs => by
    rw [inflLevel_ρ_apply, levelGal_eq_one_of_mem K L hKL s (Subgroup.mem_subgroupOf.1 hs), map_one]
  exact Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime _ hcop' _ hX h₂ N

end S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP
end P2MW
export P2MW.S_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP (solution)
