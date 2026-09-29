-- Prove2me | solution 1 for HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/eb31ef4d-4c8a-577d-8b9d-80b5f3fb60e8

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_M4aHerbrand_ideleClass_normCoset_index_ne_zero_and_finrank_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeOf isAdjuster_idelicNorm_of_isAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit"
namespace FirstIneqPackage
p2m_open "HeckeCharacter"

private theorem depth_le_admissibleExp (K L : Type*) [Field K] [NumberField K] [Field L]
    [Algebra K L] (h24 : Module.finrank K L ∣ 24) (v : HeightOneSpectrum (𝓞 K)) :
    1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal
      ≤ admissibleExp K v := by
  have h2f : (Module.finrank K L).factorization 2 ≤ 3 := by
    by_contra hgt
    have hgt' := Nat.lt_of_not_le hgt
    have hd : (2 : ℕ) ^ 4 ∣ 24 :=
      dvd_trans (dvd_trans (pow_dvd_pow 2 hgt') (Nat.ordProj_dvd _ _)) h24
    exact absurd hd (by decide)
  have h3f : (Module.finrank K L).factorization 3 ≤ 1 := by
    by_contra hgt
    have hgt' := Nat.lt_of_not_le hgt
    have hd : (3 : ℕ) ^ 2 ∣ 24 :=
      dvd_trans (dvd_trans (pow_dvd_pow 3 hgt') (Nat.ordProj_dvd _ _)) h24
    exact absurd hd (by decide)
  have hkey : ∀ p < 25, Nat.Prime p → p ∣ 24 → p = 2 ∨ p = 3 := by decide
  have hsub : (Module.finrank K L).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hp24 : p ∣ 24 := hpd.trans h24
    have hlt : p < 25 := lt_of_le_of_lt (Nat.le_of_dvd (by norm_num) hp24) (by norm_num)
    rcases hkey p hlt hpp hp24 with h | h <;> simp [h]
  have hsum : ∑ p ∈ (Module.finrank K L).primeFactors,
      ((Module.finrank K L).factorization p + 1) *
        Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal
      ≤ ∑ p ∈ ({2, 3} : Finset ℕ),
      ((Module.finrank K L).factorization p + 1) *
        Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal :=
    Finset.sum_le_sum_of_subset hsub
  have hpair : ∑ p ∈ ({2, 3} : Finset ℕ),
      ((Module.finrank K L).factorization p + 1) *
        Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal
      = ((Module.finrank K L).factorization 2 + 1) *
          Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) v.asIdeal
        + ((Module.finrank K L).factorization 3 + 1) *
          Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) v.asIdeal := by
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  have hc2 : (((2 : ℕ) : ℤ)) = (2 : ℤ) := by norm_num
  have hc3 : (((3 : ℕ) : ℤ)) = (3 : ℤ) := by norm_num
  have hE2 : ((Module.finrank K L).factorization 2 + 1) *
      Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) v.asIdeal
      ≤ 4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal := by
    rw [hc2]
    exact Nat.mul_le_mul (by omega) le_rfl
  have hE3 : ((Module.finrank K L).factorization 3 + 1) *
      Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) v.asIdeal
      ≤ 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal := by
    rw [hc3]
    exact Nat.mul_le_mul (by omega) le_rfl
  rw [admissibleExp]
  calc 1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal
      ≤ 1 + (((Module.finrank K L).factorization 2 + 1) *
            Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) v.asIdeal
          + ((Module.finrank K L).factorization 3 + 1) *
            Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) v.asIdeal) :=
        Nat.add_le_add_left (hpair ▸ hsum) 1
    _ ≤ 1 + (4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
          + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal) :=
        Nat.add_le_add_left (Nat.add_le_add hE2 hE3) 1
    _ = 4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
          + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal + 1 := by
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
    placeOf K (InfinitePlace.embedding_of_isReal hw) = w := by
  show InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w
  have e : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) = w.embedding :=
    RingHom.ext fun x => InfinitePlace.embedding_of_isReal_apply hw x
  rw [e, InfinitePlace.mk_embedding]

private theorem unitIdeles_le_idelicNorm_range (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (h24 : Module.finrank K L ∣ 24)
    (𝔪 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔪) :
    unitIdeles K 𝔪 ≤ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range := by
  intro u hu
  obtain ⟨hunit, hcong, harch⟩ := hu
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range K L
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L) u ?_ ?_ ?_
  · intro v
    exact hunit v
  · intro v hram
    have hpow : v.asIdeal ^ admissibleExp K v ∣ 𝔪 := hadm.2 v hram
    have hvdvd : v.asIdeal ∣ 𝔪 :=
      dvd_trans (dvd_pow_self v.asIdeal (Nat.succ_ne_zero _)) hpow
    have h2 : Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ)) :=
      hcong v hvdvd
    refine le_trans h2 ?_
    rw [WithZero.exp_le_exp]
    have hfin : 1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) v.asIdeal
        ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors :=
      le_trans (depth_le_admissibleExp K L h24 v) (le_count_of_pow_dvd K hadm.1 v hpow)
    exact neg_le_neg (by exact_mod_cast hfin)
  · intro w hw _
    obtain ⟨τ, hτ⟩ : ∃ τ : K →+* ℝ, placeOf K τ = w :=
      ⟨InfinitePlace.embedding_of_isReal hw, placeOf_embedding_of_isReal K hw⟩
    subst hτ
    exact harch τ

end HeckeCharacter.FirstIneqPackage

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (h24 : Module.finrank K L ∣ 24) (𝔣 : Ideal (𝓞 K)) :
    IdeleFirstIneqDataAt K L 𝔣 :=
  ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
    HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster K L 𝔣,
    HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit K L,
    HeckeCharacter.FirstIneqPackage.unitIdeles_le_idelicNorm_range K L h24 𝔣,
    (M4aHerbrand.ideleClass_normCoset_index_ne_zero_and_finrank_dvd K L
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L)).2⟩

end S_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic
end P2MW
export P2MW.S_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic (solution)
