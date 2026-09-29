-- Prove2me | solution 1 for NumberField.PrimeNormIndex.ideleFirstIneqDataAt_of_finrank_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/df297a0e-d73f-56e8-96f6-571aecf827c6

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_PrimeNormIndex_AdmissibleExpAt
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PrimeNormIndex_ideleFirstIneqDataAt_of_finrank_eq_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_ideleFirstIneqDataAt_of_finrank_eq_prime.NumberField IsDedekindDomain LanglandsTunnell.P2.Artin"

universe v

namespace NumberField
p2m_export "NumberField" "InfinitePlace.mk_embedding InfinitePlace.embedding_of_isReal_apply mk place InfinitePlace.mk InfinitePlace.embedding_of_isReal RingOfIntegers InfinitePlace AdeleRing PrimeNormIndex.IsAdmissibleModulusAt"
namespace PrimeNormIndex
p2m_export "NumberField.PrimeNormIndex" "admissibleExpAt IsAdmissibleModulusAt"
namespace FirstIneqPrimeDegree
p2m_open "NumberField.PrimeNormIndex NumberField"

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

end NumberField.PrimeNormIndex.FirstIneqPrimeDegree

theorem solution
    (p : ℕ) (hp : p.Prime)
    (L : Type v) [Field L] [NumberField L] (M : Type v) [Field M] [NumberField M] [Algebra L M]
    [IsGalois L M] (hdeg : Module.finrank L M = p)
    (𝔣₀ : Ideal (NumberField.RingOfIntegers L))
    (hadm : NumberField.PrimeNormIndex.IsAdmissibleModulusAt L M p 𝔣₀) :
    LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt L M 𝔣₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  haveI : IsCyclic (M ≃ₐ[L] M) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])
  exact ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange L M).idelicNorm,
    HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster L M 𝔣₀,
    HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit L M,
    fun _ =>
      NumberField.PrimeNormIndex.FirstIneqPrimeDegree.unitIdeles_le_idelicNorm_range L M hp hdeg
        𝔣₀ hadm,
    (M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd L M
      (M4aHerbrand.GenuineDescent.genuineBaseChange L M)).2⟩

end S_NumberField_PrimeNormIndex_ideleFirstIneqDataAt_of_finrank_eq_prime
end P2MW
export P2MW.S_NumberField_PrimeNormIndex_ideleFirstIneqDataAt_of_finrank_eq_prime (solution)
