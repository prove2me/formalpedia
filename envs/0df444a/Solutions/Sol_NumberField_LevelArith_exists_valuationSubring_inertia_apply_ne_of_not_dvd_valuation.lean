-- Prove2me | solution 1 for NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/810d16ab-7524-57e7-a6f6-8c1bee335e2c

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import Theorems.Thm_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation

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

namespace CycBaseRamAtW

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
        obtain ⟨c, hc⟩ := Nat.minFac_dvd n
        have hc0 : c ≠ 0 := by rintro rfl; exact hn0 (by rw [hc, mul_zero])
        rw [hc, Nat.cast_mul] at hn
        rcases w.isPrime.mem_or_mem hn with h | h
        · exact ⟨_, hmin, h⟩
        · have hclt : c < n := by
            rw [hc]
            exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hc0) hmin.one_lt
          exact ih c hclt hc0 h
  refine key _ ?_ (Ideal.absNorm_mem w.asIdeal)
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

end CycBaseRamAtW

theorem solution
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (x : (↥F)ˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F))
    (hw : ¬ (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = ((x : ↥F) : AlgebraicClosure ℚ)) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), (∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1) ∧
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, (∀ z : ↥F, σ z = z) ∧ σ y ≠ y := by
  have hp : p.Prime := Fact.out
  have hcoe : ∀ z : ↥F, (z : AlgebraicClosure ℚ) = algebraMap (↥F) (AlgebraicClosure ℚ) z := fun _ => rfl
  obtain ⟨q, hq, hqw⟩ := CycBaseRamAtW.exists_natPrime_mem F w
  obtain ⟨P, hPq, hPw, σ, hσI, hσF, hσy⟩ :=
    ValuationSubring.exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
      F p hp x w q hq hqw hw y hy
  refine ⟨P, fun z => ?_, σ, hσI, hσF, hσy⟩

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∉ P := by
    have h := hPq
    unfold ValuationSubring.LiesOverPrime at h
    rw [ValuationSubring.mem_nonunits_iff_or] at h
    exact h.resolve_left hq0
  obtain ⟨v, hv, -⟩ := NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one (↥F)
    (algebraMap (↥F) (AlgebraicClosure ℚ)) P ⟨((q : ℕ) : ↥F)⁻¹, by rwa [map_inv₀, map_natCast]⟩
  have hvw : v = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext r
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥F), hPw r, ← ValuationSubring.mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff_or]
    show v.valuation (↥F) (algebraMap (𝓞 ↥F) (↥F) r) < 1 ↔
      ((algebraMap (↥F) (AlgebraicClosure ℚ)) (algebraMap (𝓞 ↥F) (↥F) r) = 0 ∨
        ((algebraMap (↥F) (AlgebraicClosure ℚ)) (algebraMap (𝓞 ↥F) (↥F) r))⁻¹ ∉ P)
    have hr : (algebraMap (↥F) (AlgebraicClosure ℚ)) (algebraMap (𝓞 ↥F) (↥F) r) ∈ P := by
      rw [hv]; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v r
    rcases eq_or_ne (algebraMap (𝓞 ↥F) (↥F) r) 0 with h0 | h0
    ·
      rw [h0, map_zero]
      exact ⟨fun _ => Or.inl rfl, fun _ => zero_lt_one⟩
    · have hpos : 0 < v.valuation (↥F) (algebraMap (𝓞 ↥F) (↥F) r) :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h0)
      have hne : (algebraMap (↥F) (AlgebraicClosure ℚ)) (algebraMap (𝓞 ↥F) (↥F) r) ≠ 0 :=
        (map_ne_zero _).mpr h0
      constructor
      · intro hlt
        right
        intro hinv
        have h2 := (hv ((algebraMap (𝓞 ↥F) (↥F) r)⁻¹)).mp (by rwa [map_inv₀])
        rw [map_inv₀, inv_le_one₀ hpos] at h2
        exact absurd hlt (not_lt.mpr h2)
      · rintro (h00 | hinv)
        · exact absurd h00 hne
        · have h2 : ¬ v.valuation (↥F) ((algebraMap (𝓞 ↥F) (↥F) r)⁻¹) ≤ 1 := fun hle => hinv (by
            have h3 := (hv ((algebraMap (𝓞 ↥F) (↥F) r)⁻¹)).mpr hle; rwa [map_inv₀] at h3)
          rw [map_inv₀, inv_le_one₀ hpos, not_le] at h2
          exact h2
  rw [hcoe, hv z, hvw]

end S_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
end P2MW
export P2MW.S_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation (solution)
