-- Prove2me | solution 1 for NumberField.PrimeNormIndex.ideleClass_normCoset_index_dvd_of_finrank_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d25e00e1-0d93-5ed5-be24-a3a9213808ed

import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_PrimeNormIndex_AdmissibleExpAt
import Theorems.Thm_NumberField_PrimeNormIndex_ideleFirstIneqDataAt_of_finrank_eq_prime
import Theorems.Thm_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_prime
import Theorems.Thm_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PrimeNormIndex_ideleClass_normCoset_index_dvd_of_finrank_eq_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_ideleClass_normCoset_index_dvd_of_finrank_eq_prime.NumberField IsDedekindDomain LanglandsTunnell.P2.Artin"

namespace NumberField
p2m_export "NumberField" "InfinitePlace.mk_embedding InfinitePlace.embedding_of_isReal_apply mk place InfinitePlace.mk InfinitePlace.embedding_of_isReal RingOfIntegers InfinitePlace AdeleRing PrimeNormIndex.ideleFirstIneqDataAt_of_finrank_eq_prime PrimeNormIndex.secondInequalityCTM_of_finrank_eq_prime"
namespace PrimeNormIndex
p2m_export "NumberField.PrimeNormIndex" "admissibleExpAt IsAdmissibleModulusAt ideleFirstIneqDataAt_of_finrank_eq_prime secondInequalityCTM_of_finrank_eq_prime"
namespace NormCosetPrimeDegree
p2m_open "NumberField.PrimeNormIndex NumberField"

section Transport

open TensorProduct

variable {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E] [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F] [Algebra E F]

private theorem adelicNorm_eq_norm_symm (B : M4aHerbrand.AdeleBaseChange R E S F)
    (y : AdeleRing S F) :
    B.adelicNorm y =
      Algebra.norm (AdeleRing R E) ((letI := B.β.toAlgebra; B.tensorEquiv.symm) y) := by
  letI := B.β.toAlgebra
  show Algebra.norm (AdeleRing R E) y = _
  conv_lhs => rw [← B.tensorEquiv.apply_symm_apply y]
  exact Algebra.norm_eq_of_algEquiv B.tensorEquiv _

private theorem idelicNorm_range_eq_std (B : M4aHerbrand.AdeleBaseChange R E S F) :
    B.idelicNorm.range =
      (Units.map
        (Algebra.norm (AdeleRing R E) : ((AdeleRing R E) ⊗[E] F) →* AdeleRing R E)).range := by
  letI := B.β.toAlgebra
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    let e : AdeleRing S F ≃* ((AdeleRing R E) ⊗[E] F) :=
      (B.tensorEquiv.symm : AdeleRing S F ≃ₐ[AdeleRing R E] _).toRingEquiv.toMulEquiv
    refine ⟨Units.mapEquiv e u, Units.ext ?_⟩
    show Algebra.norm (AdeleRing R E) (B.tensorEquiv.symm (u : AdeleRing S F)) =
      B.adelicNorm (u : AdeleRing S F)
    exact (adelicNorm_eq_norm_symm B _).symm
  · rintro ⟨v, rfl⟩
    let e' : ((AdeleRing R E) ⊗[E] F) ≃* AdeleRing S F :=
      (B.tensorEquiv : _ ≃ₐ[AdeleRing R E] AdeleRing S F).toRingEquiv.toMulEquiv
    refine ⟨Units.mapEquiv e' v, Units.ext ?_⟩
    show B.adelicNorm (B.tensorEquiv (v : (AdeleRing R E) ⊗[E] F)) =
      Algebra.norm (AdeleRing R E) (v : (AdeleRing R E) ⊗[E] F)
    rw [adelicNorm_eq_norm_symm B]
    exact congrArg _ (B.tensorEquiv.symm_apply_apply _)

private theorem idelicNorm_range_eq (B B' : M4aHerbrand.AdeleBaseChange R E S F) :
    B.idelicNorm.range = B'.idelicNorm.range :=
  (idelicNorm_range_eq_std B).trans (idelicNorm_range_eq_std B').symm

end Transport

private theorem depth_le_admissibleExpAt (L M : Type*) [Field L] [NumberField L] [Field M]
    [Algebra L M] {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank L M = p)
    (v : HeightOneSpectrum (𝓞 L)) :
    1 + ∑ q ∈ (Module.finrank L M).primeFactors,
        ((Module.finrank L M).factorization q + 1) *
          Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) v.asIdeal
      ≤ admissibleExpAt L p v := by
  rw [hdeg, hp.primeFactors, Finset.sum_singleton, hp.factorization_self, admissibleExpAt]
  omega

private theorem le_count_of_pow_dvd (K : Type*) [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) {e : ℕ} (hpow : v.asIdeal ^ e ∣ 𝔪) :
    e ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors := by
  have h𝔪0 : (Associates.mk 𝔪) ≠ 0 :=
    Associates.mk_ne_zero.mpr (by rw [Ne, Ideal.zero_eq_bot]; exact h𝔪)
  have hirr := Associates.irreducible_mk.mpr v.irreducible
  refine (Associates.prime_pow_dvd_iff_le h𝔪0 hirr).mp ?_
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
  exact hpow

private theorem placeOf_embedding_of_isReal (K : Type*) [Field K] {w : InfinitePlace K}
    (hw : w.IsReal) :
    HeckeCharacter.placeOf K (InfinitePlace.embedding_of_isReal hw) = w := by
  show InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w
  have e : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) = w.embedding :=
    RingHom.ext fun x => InfinitePlace.embedding_of_isReal_apply hw x
  rw [e, InfinitePlace.mk_embedding]

private theorem unitIdeles_le_idelicNorm_range (L M : Type*) [Field L] [NumberField L] [Field M]
    [NumberField M] [Algebra L M] [IsGalois L M] {p : ℕ} (hp : p.Prime)
    (hdeg : Module.finrank L M = p) (𝔪 : Ideal (𝓞 L)) (hadm : IsAdmissibleModulusAt L M p 𝔪) :
    unitIdeles L 𝔪 ≤ (M4aHerbrand.GenuineDescent.genuineBaseChange L M).idelicNorm.range := by
  intro u hu
  obtain ⟨hunit, hcong, harch⟩ := hu
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range L M
    (M4aHerbrand.GenuineDescent.genuineBaseChange L M) u ?_ ?_ ?_
  · intro v
    exact hunit v
  · intro v hram
    have hpow : v.asIdeal ^ admissibleExpAt L p v ∣ 𝔪 := hadm.2 v hram
    have hvdvd : v.asIdeal ∣ 𝔪 :=
      dvd_trans (dvd_pow_self v.asIdeal (Nat.succ_ne_zero _)) hpow
    have h2 : Valued.v (((u : AdeleRing (𝓞 L) L).2 : FiniteAdeleRing (𝓞 L) L) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ)) :=
      hcong v hvdvd
    refine le_trans h2 ?_
    rw [WithZero.exp_le_exp]
    have hfin : 1 + ∑ q ∈ (Module.finrank L M).primeFactors,
        ((Module.finrank L M).factorization q + 1) *
          Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) v.asIdeal
        ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors :=
      le_trans (depth_le_admissibleExpAt L M hp hdeg v) (le_count_of_pow_dvd L hadm.1 v hpow)
    exact neg_le_neg (by exact_mod_cast hfin)
  · intro w hw _
    obtain ⟨τ, hτ⟩ : ∃ τ : L →+* ℝ, HeckeCharacter.placeOf L τ = w :=
      ⟨InfinitePlace.embedding_of_isReal hw, placeOf_embedding_of_isReal L hw⟩
    subst hτ
    exact harch τ

private theorem pow_ramificationIdx_dvd_span_natCast (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal ∣
      Ideal.span {((p : ℕ) : 𝓞 K)} := by
  rw [Ideal.dvd_iff_le]
  have h := Ideal.le_pow_ramificationIdx (p := Ideal.span {((p : ℕ) : ℤ)}) (P := v.asIdeal)
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

private theorem exists_isAdmissibleModulusAt (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] {p : ℕ} (hp : p.Prime) :
    ∃ 𝔣 : Ideal (𝓞 K), IsAdmissibleModulusAt K L p 𝔣 := by
  obtain ⟨𝔣₀, h𝔣₀, -⟩ := exists_admissibleModulus_supported K L
  have hP : Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨Ideal.span {((p : ℕ) : 𝓞 K)} * (Ideal.span {((p : ℕ) : 𝓞 K)} * 𝔣₀), ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hP h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hP h
    · exact h𝔣₀.1 h
  · intro v hv
    have hv𝔣₀ : v.asIdeal ∣ 𝔣₀ :=
      dvd_trans (dvd_pow_self v.asIdeal (by rw [admissibleExp]; omega)) (h𝔣₀.2 v hv)
    have hPv := pow_ramificationIdx_dvd_span_natCast K p v
    rw [admissibleExpAt, pow_succ, two_mul, pow_add, mul_assoc]
    exact mul_dvd_mul hPv (mul_dvd_mul hPv hv𝔣₀)

private theorem index_genuine_dvd (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p) :
    (M4aHerbrand.principalIdeles (𝓞 K) K ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range).index ∣ p := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  obtain ⟨𝔣, hadm⟩ := exists_isAdmissibleModulusAt K L hp
  have hray : (normRaySubgroup K L 𝔣).index ∣ Nat.card (L ≃ₐ[K] L) :=
    NumberField.PrimeNormIndex.secondInequalityCTM_of_finrank_eq_prime K L p hp hdeg
      (NumberField.PrimeNormIndex.ideleFirstIneqDataAt_of_finrank_eq_prime p hp) 𝔣
  have hidx := normRaySubgroup_index_eq_of_anchors K L 𝔣 hadm.1
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
    (HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster K L 𝔣)
    (HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit K L)
    (unitIdeles_le_idelicNorm_range K L hp hdeg 𝔣 hadm)
  rw [← hidx, ← hdeg, ← IsGalois.card_aut_eq_finrank]
  exact hray

end NumberField.PrimeNormIndex.NormCosetPrimeDegree

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (p : ℕ) (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (B : M4aHerbrand.AdeleBaseChange (NumberField.RingOfIntegers K) K
      (NumberField.RingOfIntegers L) L) :
    (M4aHerbrand.principalIdeles (NumberField.RingOfIntegers K) K ⊔
      B.idelicNorm.range).index ∣ p := by
  rw [NumberField.PrimeNormIndex.NormCosetPrimeDegree.idelicNorm_range_eq B
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L)]
  exact NumberField.PrimeNormIndex.NormCosetPrimeDegree.index_genuine_dvd K L hp hdeg

end S_NumberField_PrimeNormIndex_ideleClass_normCoset_index_dvd_of_finrank_eq_prime
end P2MW
export P2MW.S_NumberField_PrimeNormIndex_ideleClass_normCoset_index_dvd_of_finrank_eq_prime (solution)
