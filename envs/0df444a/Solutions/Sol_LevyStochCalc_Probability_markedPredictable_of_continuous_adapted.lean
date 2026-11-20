-- Prove2me | solution 1 for LevyStochCalc.Probability.markedPredictable_of_continuous_adapted
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:21:05.064649+00:00
-- url     : https://prove2.me/submissions/1c95e0be-e5c5-46ae-98f1-0c415ab757bd

import Definitions.Def_LevyStochCalc_Probability_PredictableContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A continuous adapted process, cut to a window, is marked predictable

Freezing a continuous adapted process at the left endpoints of the level-`n` dyadic slabs gives a
step process whose coefficients are known at those endpoints, hence a marked predictable process
for every level. The endpoints increase to the time from strictly below, so on a window of finite
mark measure the frozen processes converge pointwise to the process itself, which is therefore
marked predictable there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Poisson (dyadicLeft dyadicLeft_lt sub_le_dyadicLeft)



theorem _root_.solution {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e =>
      (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e) := by
  classical
  -- pointwise limit of the step processes
  have hlim : ∀ p : Ω × ℝ × E, Tendsto (fun n => stepEval X A T n p.1 p.2.1 p.2.2) atTop
      (𝓝 ((Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X p.2.1 p.1) (p.2.1, p.2.2))) := by
    rintro ⟨ω, s, e⟩
    by_cases hin : (s, e) ∈ Set.Ioc (0 : ℝ) T ×ˢ A
    · obtain ⟨⟨hs0, hsT⟩, he⟩ := hin
      rw [Set.indicator_of_mem (show (s, e) ∈ Set.Ioc (0 : ℝ) T ×ˢ A from ⟨⟨hs0, hsT⟩, he⟩)]
      simp_rw [stepEval_eq hs0 hsT he ω]
      have hd : Tendsto (fun n => dyadicLeft n s) atTop (𝓝 s) := by
        have hlow : Tendsto (fun n : ℕ => s - (1 / 2 : ℝ) ^ n) atTop (𝓝 s) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num)).const_sub s
          simpa using this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
          (fun n => sub_le_dyadicLeft n) (fun n => (dyadicLeft_lt hs0 n).le)
      exact ((hXc ω).tendsto s).comp hd
    · rw [Set.indicator_of_notMem hin]
      -- eventually every slab misses (s, e)
      have hev : ∀ᶠ n in atTop, stepEval X A T n ω s e = 0 := by
        by_cases he : e ∈ A
        · have hsout : ¬ (0 < s ∧ s ≤ T) := fun h => hin ⟨h, he⟩
          by_cases hs0 : 0 < s
          · have hsT : T < s := by
              by_contra h; exact hsout ⟨hs0, not_lt.mp h⟩
            obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hsT) (by norm_num : (1 / 2 : ℝ) < 1)
            refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
            unfold stepEval
            refine Finset.sum_eq_zero (fun i hi => Set.indicator_of_notMem ?_ _)
            rintro ⟨⟨_, h2⟩, _⟩
            have hpow : (0 : ℝ) < 2 ^ n := by positivity
            have hi' := Finset.mem_range.mp hi
            have hT0 : 0 ≤ T := by
              by_contra hT; push Not at hT
              have : ⌈T * 2 ^ n⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by nlinarith)
              omega
            have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T * 2 ^ n)
            have hi1 : ((i : ℝ) + 1) ≤ ⌈T * 2 ^ n⌉₊ := by exact_mod_cast hi'
            have hhalf : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ N :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
            have hs2 : s * 2 ^ n ≤ (i : ℝ) + 1 := (le_div_iff₀ hpow).mp h2
            have e2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
              rw [one_div_pow, div_mul_cancel₀ _ hpow.ne']
            nlinarith
          · refine Filter.Eventually.of_forall (fun n => ?_)
            unfold stepEval
            refine Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem ?_ _)
            rintro ⟨⟨h1, _⟩, _⟩
            have : (0 : ℝ) ≤ (i : ℝ) / 2 ^ n := by positivity
            linarith [not_lt.mp hs0]
        · refine Filter.Eventually.of_forall (fun n => ?_)
          unfold stepEval
          exact Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (fun h => he h.2) _)
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  have hmeas : ∀ n, Measurable[markedPredictableSigma ℱ ν]
      (fun p : Ω × ℝ × E => stepEval X A T n p.1 p.2.1 p.2.2) :=
    fun n => markedPredictable_stepEval hX hA hAν T n
  exact @measurable_of_tendsto_metrizable _ _ (markedPredictableSigma ℱ ν) _ _ _ _ _ _ hmeas
    (tendsto_pi_nhds.mpr hlim)

