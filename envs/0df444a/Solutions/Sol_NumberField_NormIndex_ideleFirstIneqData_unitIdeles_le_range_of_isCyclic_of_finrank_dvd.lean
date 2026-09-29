-- Prove2me | solution 1 for NumberField.NormIndex.ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dd85c619-2a94-5da5-a29e-e5765df85a62

import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_NumberField_NormIndex_IsAdmissibleModulusOfDegree_of_dvd_degree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_NormIndex_ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_NormIndex_ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd.NumberField NumberField.NormIndex P2MW.S_NumberField_NormIndex_ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd.NumberField.NormIndex IsDedekindDomain LanglandsTunnell.P2.Artin"

universe u v

namespace NumberField
p2m_export "NumberField" "InfinitePlace.mk_embedding InfinitePlace.embedding_of_isReal_apply mk place InfinitePlace.mk InfinitePlace.embedding_of_isReal InfinitePlace AdeleRing NormIndex.IsAdmissibleModulusOfDegree NormIndex.IsAdmissibleModulusOfDegree.of_dvd_degree"
namespace NormIndex
p2m_export "NumberField.NormIndex" "IsAdmissibleModulusOfDegree IsAdmissibleModulusOfDegree.of_dvd_degree"
namespace FirstIneqOfDegree
p2m_open "NumberField.NormIndex NumberField"

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

private theorem unitIdeles_le_idelicNorm_range (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] {n : ℕ} (hn : n ≠ 0)
    (hdeg : Module.finrank K L ∣ n) (𝔪 : Ideal (𝓞 K))
    (hadm : IsAdmissibleModulusOfDegree K L n 𝔪) :
    unitIdeles K 𝔪 ≤ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range := by
  intro u hu
  obtain ⟨hunit, hcong, harch⟩ := hu
  have hadm' : IsAdmissibleModulusOfDegree K L (Module.finrank K L) 𝔪 :=
    NumberField.NormIndex.IsAdmissibleModulusOfDegree.of_dvd_degree K L hdeg hn hadm
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range K L
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L) u ?_ ?_ ?_
  · intro v
    exact hunit v
  · intro v hram
    have hpow : v.asIdeal ^ (1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal) ∣ 𝔪 :=
      hadm'.2 v hram
    have hvdvd : v.asIdeal ∣ 𝔪 :=
      dvd_trans (dvd_pow_self v.asIdeal (by omega)) hpow
    have h2 : Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ)) :=
      hcong v hvdvd
    refine le_trans h2 ?_
    rw [WithZero.exp_le_exp]
    have hfin : 1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal
        ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors :=
      le_count_of_pow_dvd K hadm.1 v hpow
    exact neg_le_neg (by exact_mod_cast hfin)
  · intro w hw _
    obtain ⟨τ, hτ⟩ : ∃ τ : K →+* ℝ, HeckeCharacter.placeOf K τ = w :=
      ⟨InfinitePlace.embedding_of_isReal hw, placeOf_embedding_of_isReal K hw⟩
    subst hτ
    exact harch τ

end NumberField.NormIndex.FirstIneqOfDegree

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (n : ℕ) (hn : n ≠ 0) (hdeg : Module.finrank K L ∣ n)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulusOfDegree K L n 𝔣) :
    ∃ Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ,
      (∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
        HeckeCharacter.IsAdjuster L (HeckeCharacter.modulusExt K L 𝔣) u α →
          HeckeCharacter.IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α)) ∧
      (∀ u : (AdeleRing (𝓞 L) L)ˣ,
        HeckeCharacter.fadContentHom K (HeckeCharacter.projFin K (Nrm u)) =
          HeckeCharacter.fracRelNormUnit K L
            (HeckeCharacter.fadContentHom L (HeckeCharacter.projFin L u))) ∧
      LanglandsTunnell.P2.Artin.unitIdeles K 𝔣 ≤ Nrm.range ∧
      Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index := by
  exact ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
    HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster K L 𝔣,
    HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit K L,
    NumberField.NormIndex.FirstIneqOfDegree.unitIdeles_le_idelicNorm_range K L hn hdeg 𝔣 hadm,
    (M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd K L
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L)).2⟩

end S_NumberField_NormIndex_ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd
end P2MW
export P2MW.S_NumberField_NormIndex_ideleFirstIneqData_unitIdeles_le_range_of_isCyclic_of_finrank_dvd (solution)
