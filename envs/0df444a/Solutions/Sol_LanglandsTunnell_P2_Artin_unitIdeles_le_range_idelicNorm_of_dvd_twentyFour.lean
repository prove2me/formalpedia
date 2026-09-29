-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.unitIdeles_le_range_idelicNorm_of_dvd_twentyFour
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/eb657722-d518-523a-b99d-bbca7162a434

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_dvd_twentyFour
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply
open scoped IsMulCommutative

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : F ≃ₐ[E] F, x ^ (ℓ ^ k) = 1) (hk : ℓ ^ k ∣ 24)
    (hdeg : Module.finrank E F ∣ 24)
    (𝔣 : Ideal (𝓞 E)) (hadm : IsAdmissibleModulus E F 𝔣) :
    unitIdeles E 𝔣 ≤ ((genuineBaseChange E F).idelicNorm).range := by
  classical
  intro u hu
  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite ℚ E F
  have hn0 : Module.finrank E F ≠ 0 := Module.finrank_pos.ne'
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range E F (genuineBaseChange E F) u
    (fun v => hu.1 v) ?_ ?_
  ·
    intro v hv
    have hdvd : v.asIdeal ^ admissibleExp E v ∣ 𝔣 := hadm.2 v hv
    have hane : admissibleExp E v ≠ 0 := Nat.succ_ne_zero _
    have hv𝔣 : v.asIdeal ∣ 𝔣 := (dvd_pow_self v.asIdeal hane).trans hdvd
    refine le_trans (hu.2.1 v hv𝔣) ?_
    rw [WithZero.exp_le_exp, neg_le_neg_iff]

    have h2 : (Module.finrank E F).factorization 2 ≤ 3 := by
      by_contra h
      push Not at h
      have h16 : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 h).trans ((Nat.ordProj_dvd _ 2).trans hdeg)
      norm_num at h16
    have h3 : (Module.finrank E F).factorization 3 ≤ 1 := by
      by_contra h
      push Not at h
      have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 h).trans ((Nat.ordProj_dvd _ 3).trans hdeg)
      norm_num at h9
    have hsub : (Module.finrank E F).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      have hp24 : p ∣ 24 := hp'.2.1.trans hdeg
      have hple : p ≤ 24 := Nat.le_of_dvd (by norm_num) hp24
      have hpp := hp'.1
      interval_cases p <;> simp_all (config := {decide := true})
    have hsum : ∑ p ∈ (Module.finrank E F).primeFactors,
        ((Module.finrank E F).factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal
        ≤ 4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
          + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal := by
      refine (Finset.sum_le_sum_of_subset hsub).trans ?_
      rw [Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
      push_cast
      have e2 : ((Module.finrank E F).factorization 2 + 1) * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
          ≤ 4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal :=
        Nat.mul_le_mul_right _ (by omega)
      have e3 : ((Module.finrank E F).factorization 3 + 1) * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal
          ≤ 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal :=
        Nat.mul_le_mul_right _ (by omega)
      exact Nat.add_le_add e2 e3
    have hdepth : 1 + ∑ p ∈ (Module.finrank E F).primeFactors,
        ((Module.finrank E F).factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal
        ≤ admissibleExp E v := by
      unfold admissibleExp
      omega

    have hcount : admissibleExp E v ≤ (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors := by
      rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hadm.1) (Associates.irreducible_mk.mpr v.irreducible),
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hdvd
    exact_mod_cast hdepth.trans hcount
  ·
    intro w hw _
    have key : ∀ (τ : E →+* ℝ) (w' : InfinitePlace E) (hw' : w'.IsReal), placeOf E τ = w' →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw'
          (((u : AdeleRing (𝓞 E) E).1 : InfiniteAdeleRing E) w') := by
      rintro τ w' hw' rfl
      exact hu.2.2 τ
    refine key (InfinitePlace.embedding_of_isReal hw) w hw ?_
    show InfinitePlace.mk _ = w
    conv_rhs => rw [← InfinitePlace.mk_embedding w]
    congr 1
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hw x

end S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_dvd_twentyFour
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_range_idelicNorm_of_dvd_twentyFour (solution)
