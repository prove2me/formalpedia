-- Prove2me | solution 1 for KStar.Ram.complIntegers_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:19.238176+00:00
-- url     : https://prove2.me/submissions/f05604dd-6cf1-413b-9ed0-c4ff2e518df7

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_InertiaRamification_ComplDefY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
private theorem cdy_val (a : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_of_algebraMap a
private theorem cdy_max {π : 𝓞 E} (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers E) =
      Ideal.span {algebraMap (𝓞 E) (w.adicCompletionIntegers E) π} := by
  ext y
  rw [Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, mem_maximalIdeal,
    mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion E) = 1 ↔ Valued.v (y : w.adicCompletion E) ≤
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) π : w.adicCompletionIntegers E) :
      w.adicCompletion E)
  rw [cdy_val, hπ]
  have hy : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion E) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega
private theorem cdy_pow (π : 𝓞 E) (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  simp
private theorem cdy_mem (n : ℕ) (y : w.adicCompletionIntegers E) :
    y ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n ↔
      Valued.v (y : w.adicCompletion E) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, ← map_pow,
    ← cdy_pow w π hπ n, ← cdy_val]
  rfl
private theorem cdy_comap (n : ℕ) : (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
    (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n := by
  ext a
  rw [Ideal.mem_comap, cdy_mem, cdy_val, w.intValuation_le_pow_iff_mem]
private theorem cdy_ball (n : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ x : w.adicCompletion E,
    Valued.v x ≤ WithZero.exp (-(n : ℤ)) ↔ ‖x‖ ≤ r := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
    (WithZero.exp (-(n : ℤ)))
  refine ⟨‖p‖, norm_pos_iff.2 ?_, fun x => by rw [Valued.toNormedField.norm_le_iff, hp]⟩
  rintro rfl
  rw [map_zero] at hp
  exact WithZero.exp_ne_zero hp.symm
variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]
end KStar.Ram
end

set_option autoImplicit false
open KStar KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
namespace KStar.Ram
theorem _root_.solution (n : ℕ) :
    (w.asIdeal ^ n).map (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) =
        maximalIdeal (w.adicCompletionIntegers E) ^ n ∧
      (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
        (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n ∧
      (∀ y : w.adicCompletionIntegers E, ∃ x : 𝓞 E,
        y - algebraMap (𝓞 E) _ x ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n) := by
  refine ⟨?_, cdy_comap w n, fun y => ?_⟩
  · refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cdy_comap w n).ge) ?_
    obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
    rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, ← map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← w.intValuation_le_pow_iff_mem, cdy_pow w π hπ]
  · obtain ⟨r, hr, h⟩ := cdy_ball w n
    obtain ⟨t, ht⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt
      (y : w.adicCompletion E) hr
    rw [dist_eq_norm] at ht
    have ht' := (h _).2 ht.le
    have hv : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
      fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
    have hn : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have ht1 : w.valuation E t ≤ 1 := by
      rw [← hv, ← sub_sub_cancel (y : w.adicCompletion E) (algebraMap E (w.adicCompletion E) t)]
      exact Valuation.map_sub_le _ y.2 (ht'.trans hn)
    obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer ht1
      (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
    refine ⟨a, ?_⟩
    rw [cdy_mem]
    have e : ((y - algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
        w.adicCompletion E) = ((y : w.adicCompletion E) - algebraMap E (w.adicCompletion E) t) -
        algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E a - t) := by
      rw [map_sub, sub_sub, add_sub_cancel]
      rfl
    rw [e]
    refine Valuation.map_sub_le _ ht' ?_
    rw [hv]
    exact ha.le
end KStar.Ram
