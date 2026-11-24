-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.exists_mul_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:38.682127+00:00
-- url     : https://prove2.me/submissions/cf6dc065-c8a1-4fef-b3f3-73577218c023

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_le_exp_neg_one_of_lt_one
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exp_neg_one_pow
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exists_exp_le_intValuation
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exists_mem_comap_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) (y : K)
    (hy : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      w.valuation K y ≤ 1) :
    ∃ a : 𝓞 E, a ∉ v.asIdeal ∧ algebraMap E K (a : E) * y ∈ (algebraMap (𝓞 K) K).range := by
  classical
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  obtain ⟨k, hk⟩ := exists_exp_le_intValuation hc0
  have hI : Ideal.span {c} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc0
  set F := (Ideal.finite_factors hI).toFinset
  let f : HeightOneSpectrum (𝓞 K) → 𝓞 E := fun w =>
    if h : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal then
      Classical.choose (exists_mem_comap_not_mem v w h) else 1
  have hf : ∀ w, f w ∉ v.asIdeal := fun w => by
    by_cases h : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (exists_mem_comap_not_mem v w h)).2
    · simp only [f, dif_neg h]; exact fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hfw : ∀ w, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal →
      algebraMap (𝓞 E) (𝓞 K) (f w) ∈ w.asIdeal := fun w h => by
    simp only [f, dif_pos h]; exact (Classical.choose_spec (exists_mem_comap_not_mem v w h)).1
  let a : 𝓞 E := ∏ w ∈ F, f w ^ k
  have ha : a ∉ v.asIdeal := by
    refine Finset.prod_induction _ (· ∉ v.asIdeal) (fun x y hx hy h => (v.isPrime.mem_or_mem h).elim hx hy)
      (fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)) fun w _ h => hf w (v.isPrime.mem_of_pow_mem k h)
  refine ⟨a, ha, HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => ?_⟩
  have hA : algebraMap E K (a : E) = ((algebraMap (𝓞 E) (𝓞 K) a : 𝓞 K) : K) := rfl
  have hc' : w.valuation K (c : K) ≠ 0 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact w.intValuation_ne_zero c hc0
  rw [hA, map_mul, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hc'
  have hb1 := w.intValuation_le_one b
  have ha1 := w.intValuation_le_one (algebraMap (𝓞 E) (𝓞 K) a)
  by_cases hv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal
  · have := hy w hv
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at this
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * (w.intValuation b / w.intValuation c)
        ≤ 1 * (w.intValuation b / w.intValuation c) := mul_le_mul' ha1 le_rfl
      _ ≤ 1 := by rw [one_mul]; exact this
  by_cases hwF : w ∈ F
  · have hlt : w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) < 1 :=
      (w.intValuation_lt_one_iff_mem _).2 (hfw w hv)
    have hle : w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) ≤ WithZero.exp (-(k : ℤ)) := by
      have e : a = f w ^ k * ∏ x ∈ F.erase w, f x ^ k := (Finset.mul_prod_erase F (fun x => f x ^ k) hwF).symm
      rw [e, map_mul, map_mul, map_pow, map_pow, ← exp_neg_one_pow]
      calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) ^ k *
            w.intValuation (algebraMap (𝓞 E) (𝓞 K) (∏ x ∈ F.erase w, f x ^ k))
          ≤ w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) ^ k * 1 := mul_le_mul' le_rfl (w.intValuation_le_one _)
        _ ≤ WithZero.exp (-1) ^ k := by rw [mul_one]; exact pow_le_pow_left' (le_exp_neg_one_of_lt_one hlt) k
    rw [mul_div_assoc', div_le_one₀ (zero_lt_iff.2 hc')]
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * w.intValuation b
        ≤ WithZero.exp (-(k : ℤ)) * 1 := mul_le_mul' hle hb1
      _ ≤ w.intValuation c := by rw [mul_one]; exact hk w
  · have h1 : w.intValuation c = 1 := by
      refine le_antisymm (w.intValuation_le_one c) (not_lt.1 fun h => hwF ?_)
      rw [Set.Finite.mem_toFinset]
      exact (w.intValuation_lt_one_iff_dvd c).1 h
    rw [h1, div_one]
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * w.intValuation b ≤ 1 * 1 := mul_le_mul' ha1 hb1
      _ = 1 := one_mul 1
end GlobalTheory.NormCompat.NormCont
