-- Prove2me | solution 1 for GlobalTheory.PlaceSum.finsum_le_sum_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:23.638333+00:00
-- url     : https://prove2.me/submissions/20577dba-6d4d-483b-b2e5-d2f75db8d57e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
import Theorems.Thm_GlobalTheory_PlaceSum_finite_resChar_eq
import Theorems.Thm_GlobalTheory_PlaceSum_sum_ram_log_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.PlaceSum
theorem _root_.solution (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hφ : ∀ p, 0 ≤ φ p) (ν : HeightOneSpectrum (𝓞 K) → ℝ) (h0 : ∀ la, 0 ≤ ν la)
    (hle : ∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) (hz : ∀ la, resCharOf la ∉ S → ν la = 0) :
    (Function.support ν).Finite ∧
      (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤
        ∑ p ∈ S, φ p * Real.log p := by
  classical
  have hsub : Function.support ν ⊆ ⋃ p ∈ S, {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p} := by
    intro la hla
    simp only [Set.mem_iUnion]
    exact ⟨resCharOf la, by by_contra h; exact hla (hz la h), rfl⟩
  have hfin : (Function.support ν).Finite :=
    (Set.Finite.biUnion S.finite_toSet fun p hp => finite_resChar_eq (hS p hp)).subset hsub
  refine ⟨hfin, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · have hmap : ∀ la ∈ hfin.toFinset, resCharOf la ∈ S := by
      intro la hla
      by_contra h
      exact (hfin.mem_toFinset.1 hla) (hz la h)
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_le_sum fun p hp => ?_
    have hb := sum_ram_log_le (K := K) (hS p hp) (hfin.toFinset.filter fun la => resCharOf la = p)
      (fun la hla => (Finset.mem_filter.1 hla).2)
    calc _ ≤ ∑ la ∈ hfin.toFinset.filter (fun la => resCharOf la = p),
          (φ p / Module.finrank ℚ K) * ((ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal)) := by
          refine Finset.sum_le_sum fun la hla => ?_
          have h := (Finset.mem_filter.1 hla).2
          have h2 := hle la
          rw [h] at h2
          rw [abs_of_nonneg (h0 la)]
          have h3 : 0 ≤ Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K :=
            div_nonneg (Real.log_natCast_nonneg _) hn.le
          refine (mul_le_mul_of_nonneg_right h2 h3).trans (le_of_eq ?_)
          ring
      _ ≤ (φ p / Module.finrank ℚ K) * ((Module.finrank ℚ K : ℝ) * Real.log p) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hb (div_nonneg (hφ p) hn.le)
      _ = φ p * Real.log p := by field_simp
  · intro la hla
    rw [Set.Finite.coe_toFinset]
    intro h
    exact hla (by simp [h])
end GlobalTheory.PlaceSum
