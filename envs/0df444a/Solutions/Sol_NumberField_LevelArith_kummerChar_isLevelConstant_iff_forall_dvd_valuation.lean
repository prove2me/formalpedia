-- Prove2me | solution 1 for NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c1ab5522-e772-5c9d-998f-c7f627e38f86

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import Theorems.Thm_NumberField_LevelArith_inertia_apply_eq_of_dvd_valuation
import Theorems.Thm_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
import Theorems.Thm_NumberField_LevelArith_kummerChar_mul_and_add_and_level
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped Pointwise

local instance CycBaseK2bRam.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

namespace CycBaseK2bRam

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]

lemma exists_natPrime_mem (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by

  have key : ∀ n : ℕ, n ≠ 0 → ((n : ℕ) : 𝓞 ↥F) ∈ w.asIdeal → ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn0 hn
      by_cases h1 : n = 1
      · subst h1
        exact absurd (w.asIdeal.eq_top_of_isUnit_mem hn (by simp)) w.isPrime.ne_top
      · have hmin : (Nat.minFac n).Prime := Nat.minFac_prime h1
        have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
        obtain ⟨c, hc⟩ := hdvd
        have hc0 : c ≠ 0 := by rintro rfl; exact hn0 (by rw [hc, mul_zero])
        rw [hc, Nat.cast_mul] at hn
        rcases w.isPrime.mem_or_mem hn with h | h
        · exact ⟨_, hmin, h⟩
        · have hclt : c < n := by
            rw [hc]
            exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hc0) hmin.one_lt
          exact ih c hclt hc0 h
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
  refine key _ ?_ hmem
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

omit [FiniteDimensional ℚ ↥F] in

lemma natPrime_eq_of_mem (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F)) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (h : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal) (h' : ((q' : ℕ) : 𝓞 ↥F) ∈ w.asIdeal) : q = q' := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime ((Nat.coprime_primes hq hq').mpr hne)
  apply w.isPrime.ne_top
  apply w.asIdeal.eq_top_of_isUnit_mem _ isUnit_one
  have h1 : ((a : ℤ) : 𝓞 ↥F) * q + ((b : ℤ) : 𝓞 ↥F) * q' = 1 := by exact_mod_cast hab
  rw [← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ h')

lemma liesOverPrime_of_mem (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F)) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1)
    {q : ℕ} (hq : q.Prime) (hqw : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal) : A.LiesOverPrime q := by
  have hcoe : ∀ z : ↥F, (z : AlgebraicClosure ℚ) = algebraMap (↥F) (AlgebraicClosure ℚ) z := fun _ => rfl
  have hqF : w.valuation (↥F) (q : ↥F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 ↥F) ↥F) q, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hqw
  show (q : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff_or]
  right
  intro hqinv
  have h1 : (((q : ↥F)⁻¹ : ↥F) : AlgebraicClosure ℚ) ∈ A := by
    rw [hcoe, map_inv₀, map_natCast]; exact hqinv
  have h2 := (hA _).mp h1
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr
    (Nat.cast_ne_zero.mpr hq.ne_zero)))] at h2
  exact absurd hqF (not_lt.mpr h2)

omit [FiniteDimensional ℚ ↥F] in

lemma mem_fixingSubgroup_sup_adjoin {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {y : AlgebraicClosure ℚ}
    (hσF : σ ∈ F.fixingSubgroup) (hσy : σ y = y) :
    σ ∈ (F ⊔ IntermediateField.adjoin ℚ {y}).fixingSubgroup := by
  have hle : Subgroup.zpowers σ ≤ (F ⊔ IntermediateField.adjoin ℚ {y}).fixingSubgroup := by
    rw [← IntermediateField.le_iff_le, sup_le_iff]
    constructor
    · rw [IntermediateField.le_iff_le]; exact (Subgroup.zpowers_le).mpr hσF
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y :=
        (Subgroup.zpowers_le).mpr hσy
      exact hst hf
  exact hle (Subgroup.mem_zpowers σ)

omit [FiniteDimensional ℚ ↥F] in
lemma mem_fixingSubgroup_of_sup_left {E E' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : σ ∈ (E ⊔ E').fixingSubgroup) : σ ∈ E.fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone le_sup_left h

omit [FiniteDimensional ℚ ↥F] in
lemma mem_fixingSubgroup_of_sup_right {E E' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : σ ∈ (E ⊔ E').fixingSubgroup) : σ ∈ E'.fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone le_sup_right h

end CycBaseK2bRam

theorem solution
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) (hζF : ζ ∈ F) (x : (↥F)ˣ) :
    (∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
        ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F'.fixingSubgroup → kummerChar p ζ hζ F x σ = 0) ↔
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F), w ∉ placesOverPrimes ↥F (S : Set Nat.Primes) →
        (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x) := by
  have hp : p.Prime := Fact.out
  have hcoe : ∀ z : ↥F, (z : AlgebraicClosure ℚ) = algebraMap (↥F) (AlgebraicClosure ℚ) z := fun _ => rfl

  have hfix : ∀ σ : ↥F.fixingSubgroup, kummerChar p ζ hζ F x σ = 0 →
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = kummerRoot p F x := by
    intro σ h0
    rw [kummerChar_spec p ζ hζ F x σ, h0, ZMod.val_zero, pow_zero, one_mul]
  constructor
  ·
    rintro ⟨F', hF', hkill⟩ w hw
    by_contra hndvd
    obtain ⟨A, hA, σ, hσI, hσF, hσy⟩ :=
      NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation p F x w hndvd
        (kummerRoot p F x) (kummerRoot_pow p F x)
    obtain ⟨q, hq, hqw⟩ := CycBaseK2bRam.exists_natPrime_mem F w
    have hqS : (⟨q, hq⟩ : Nat.Primes) ∉ S := fun hqS => hw ⟨⟨q, hq⟩, hqS, hqw⟩
    have hAq : A.LiesOverPrime ((⟨q, hq⟩ : Nat.Primes) : ℕ) := CycBaseK2bRam.liesOverPrime_of_mem F w A hA hq hqw
    have hσ : σ ∈ (F ⊔ F').fixingSubgroup := (hF.sup hF').2 _ hqS A hAq hσI
    have hσF1 : σ ∈ F.fixingSubgroup := CycBaseK2bRam.mem_fixingSubgroup_of_sup_left hσ
    exact hσy (hfix ⟨σ, hσF1⟩ (hkill ⟨σ, hσF1⟩ (CycBaseK2bRam.mem_fixingSubgroup_of_sup_right hσ)))
  ·
    intro hdiv
    refine ⟨F ⊔ IntermediateField.adjoin ℚ {kummerRoot p F x}, ⟨?_, fun q hqS A hAq σ hσI => ?_⟩,
      fun σ hσ => (kummerChar_mul_and_add_and_level p ζ hζ F hζF).2.2 x σ hσ⟩
    ·
      haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {kummerRoot p F x}) :=
        IntermediateField.adjoin.finiteDimensional
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (kummerRoot p F x)).isIntegral)
      exact IntermediateField.finiteDimensional_sup F _
    ·
      have hσF : σ ∈ F.fixingSubgroup := hF.2 q hqS A hAq hσI
      have hσF' : ∀ z : ↥F, σ z = z := fun z => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσF z z.2
      have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.ne_zero
      have hqinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∉ A := by
        have h := hAq
        unfold ValuationSubring.LiesOverPrime at h
        rw [ValuationSubring.mem_nonunits_iff_or] at h
        exact h.resolve_left hq0
      obtain ⟨w, hw, -⟩ := NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one (↥F)
        (algebraMap (↥F) (AlgebraicClosure ℚ)) A ⟨((q : ℕ) : ↥F)⁻¹, by rwa [map_inv₀, map_natCast]⟩
      have hA : ∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1 := hw
      have hqw : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
        have h := NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one (↥F)
          (algebraMap (↥F) (AlgebraicClosure ℚ)) A w hw q (by
            rw [map_natCast]; exact (ValuationSubring.mem_nonunits_iff A).mp hAq)
        rwa [Int.cast_natCast] at h
      have hw' : w ∉ placesOverPrimes ↥F (S : Set Nat.Primes) := by
        rintro ⟨q', hq'S, hq'w⟩
        have := CycBaseK2bRam.natPrime_eq_of_mem F w q.2 q'.2 hqw hq'w
        exact hqS (by rw [show q = q' from Subtype.ext this]; exact hq'S)
      have hqp : (q : ℕ) ≠ p := by
        intro h; apply hqS
        rw [show q = pPrime p from Subtype.ext h]; exact hpS
      have hy := NumberField.LevelArith.inertia_apply_eq_of_dvd_valuation p F x w q q.2 hqp hqw (hdiv w hw')
        (kummerRoot p F x) (kummerRoot_pow p F x) A hA σ hσI hσF'
      exact CycBaseK2bRam.mem_fixingSubgroup_sup_adjoin F hσF hy

end S_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation
end P2MW
export P2MW.S_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation (solution)
