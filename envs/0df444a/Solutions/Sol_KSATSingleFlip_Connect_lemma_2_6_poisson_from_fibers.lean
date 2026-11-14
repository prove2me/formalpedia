-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_poisson_from_fibers
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:52:24.502533+00:00
-- url     : https://prove2.me/submissions/93c4f7ae-701a-4b52-be16-0acac3b67f3e

import Theorems.Thm_KSATSingleFlip_Connect_poisson_fixed_count_mean
import Theorems.Thm_KSATSingleFlip_Connect_poisson_two_sided_tail
import Theorems.Thm_KSATSingleFlip_Connect_count_mixture_bound
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_budget
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (F : Ω → ℝ) (hF : Measurable F)
    (r : ℝ≥0) (hr : 0 < r) (hNlaw : Measure.map N μ = poissonMeasure r)
    (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hrν : (r:ℝ) = ν*n)
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L))
    (g : ℕ → ℝ) (hg : Integrable g (poissonMeasure r))
    (hstep : ∀ j, |g (j+1)-g j| ≤ L)
    (hzero : ∀ ω, N ω = 0 → F ω = g 0)
    (hfiber : ∀ j : ℕ, 1 ≤ j →
      μ ({ω | N ω = j} ∩ {ω | F ω ≤ g j - a*n/2}) ≤
        μ {ω | N ω = j} * ENNReal.ofReal (Real.exp (-(a*n)^2/(8*(j:ℝ)*L^2)))) :
    μ.real {ω | F ω ≤ (∫ k, g k ∂(poissonMeasure r)) - a*n} ≤
      3 * Real.exp (-(a^2*n)/(128*(ν+1)*L^2)) := by
  classical
  let M : ℝ := ∫ k, g k ∂(poissonMeasure r)
  let x : ℝ := a*n/(4*L)
  let t : ℝ := a^2*n/(128*(ν+1)*L^2)
  let B : Set Ω := {ω | x ≤ |(N ω:ℝ)-(r:ℝ)|}
  let E : Set Ω := {ω | F ω ≤ M-a*n}
  let p : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-t))
  have hLp : 0 < L := by linarith
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hE : MeasurableSet E := by dsimp [E]; exact measurableSet_le hF measurable_const
  have hB : MeasurableSet B := by
    dsimp [B]
    exact (show MeasurableSet {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} from MeasurableSet.of_discrete).preimage hN
  have hbad : μ B ≤ ENNReal.ofReal (2*Real.exp (-t)) := by
    have htbound := KSATSingleFlip.Connect.poisson_two_sided_tail r hr x hx
    have hbadreal : μ.real B = (poissonMeasure r).real {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} := by
      simp only [measureReal_def]
      rw [← hNlaw, Measure.map_apply hN (MeasurableSet.of_discrete)]
      rfl
    have hnum : x^2/(8*((r:ℝ)+x)) ≥ t := by
      have hb := KSATSingleFlip.Connect.lemma_2_6_poisson_budget ν a L n (ν*n) hν ha ha1 hL hn (by positivity)
        (by simp; positivity) hsqrt
      simpa [x,t,hrν] using hb.2.2
    have hexp : Real.exp (-(x^2/(8*((r:ℝ)+x)))) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hreal : μ.real B ≤ 2*Real.exp (-t) := by
      rw [hbadreal]
      apply htbound.trans
      simp only [neg_div] at hexp ⊢
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    have h := ENNReal.ofReal_le_ofReal hreal
    simpa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ B)] using h
  have hfiber' : ∀ j : ℕ, μ ((E \ B) ∩ N ⁻¹' {j}) ≤ μ (N ⁻¹' {j})*p := by
    intro j
    by_cases hjgood : |(j:ℝ)-(r:ℝ)| ≤ x
    swap
    · have hempty : ((E \ B) ∩ N ⁻¹' {j}) = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨_,hb⟩ hNj
        have hbk : ¬ x ≤ |(N ω:ℝ)-(r:ℝ)| := hb
        have : |(j:ℝ)-(r:ℝ)| < x := by simpa [hNj] using lt_of_not_ge hbk
        exact hjgood (le_of_lt this)
      simp [hempty]
    by_cases hj : j = 0
    · subst j
      have hempty : ((E \ B) ∩ N ⁻¹' {0}) = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨he,hb⟩ hNω
        have hc : |(0:ℝ)-(r:ℝ)| ≤ a*n/(4*L) := by
          have hh : |(N ω:ℝ)-(r:ℝ)| < x := lt_of_not_ge hb
          simpa [hNω,x] using le_of_lt hh
        have hbgt := KSATSingleFlip.Connect.lemma_2_6_poisson_budget ν a L n 0 hν ha ha1 hL hn (by norm_num)
          (by simpa [hrν] using hc) hsqrt
        have hcmp := KSATSingleFlip.Connect.poisson_fixed_count_mean r g hg L (le_of_lt hLp) hstep 0
        have hdiff : |g 0-M| ≤ a*n/2 := le_trans hcmp (by simpa [M,hrν] using hbgt.1)
        have hFω := hzero ω hNω
        have hEω : F ω ≤ M-a*n := he
        have hlow := neg_abs_le (g 0-M)
        nlinarith [mul_pos ha hn]
      simp [hempty]
    · have hjp : 1 ≤ j := by omega
      have hjr : (0:ℝ) < j := by exact_mod_cast hjp
      have hbound : μ ((E \ B) ∩ N ⁻¹' {j}) ≤
          μ ({ω | N ω = j} ∩ {ω | F ω ≤ g j-a*n/2}) := by
        apply measure_mono
        intro ω hω
        have hNω : N ω = j := hω.2
        have hclose : |(j:ℝ)-(r:ℝ)| ≤ a*n/(4*L) := by
          have hh : |(N ω:ℝ)-(r:ℝ)| < x := lt_of_not_ge hω.1.2
          simpa [hNω,x] using le_of_lt hh
        have hbud := KSATSingleFlip.Connect.lemma_2_6_poisson_budget ν a L n j hν ha ha1 hL hn (by positivity)
          (by simpa [hrν] using hclose) hsqrt
        have hcmp := KSATSingleFlip.Connect.poisson_fixed_count_mean r g hg L (le_of_lt hLp) hstep j
        have hdiff : |g j-M| ≤ a*n/2 := le_trans hcmp (by simpa [M,hrν] using hbud.1)
        have he : F ω ≤ M-a*n := hω.1.1
        have hlow := neg_abs_le (g j-M)
        have hgj : M-a*n/2 ≤ g j := by linarith
        refine ⟨hNω, ?_⟩
        change F ω ≤ g j-a*n/2
        linarith only [he, hgj]
      have hcloseRate : Real.exp (-(a*n)^2/(8*(j:ℝ)*L^2)) ≤ Real.exp (-t) := by
        have hbud := KSATSingleFlip.Connect.lemma_2_6_poisson_budget ν a L n j hν ha ha1 hL hn (by positivity)
          (by simpa [hrν,x] using hjgood) hsqrt
        have hden : 0 < 8*(j:ℝ)*L^2 := by positivity
        have hden' : 0 < 128*(ν+1)*L^2 := by positivity
        have hrate : t ≤ (a*n)^2/(8*(j:ℝ)*L^2) := by
          dsimp [t]
          apply (div_le_div_iff₀ hden' hden).2
          nlinarith [mul_nonneg (sq_nonneg a) (mul_nonneg (le_of_lt hn) (sub_nonneg.mpr hbud.2.1)), sq_nonneg L]
        apply Real.exp_le_exp.mpr
        simp only [neg_div]
        linarith
      refine hbound.trans ((hfiber j hjp).trans ?_)
      dsimp [p]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hcloseRate) _
  have h := KSATSingleFlip.Connect.count_mixture_bound μ N hN E B hE hB p hfiber'
  have htotal : μ E ≤ ENNReal.ofReal (3*Real.exp (-t)) := by
    calc
      μ E ≤ p + μ B := h
      _ ≤ ENNReal.ofReal (Real.exp (-t)) + ENNReal.ofReal (2*Real.exp (-t)) := by dsimp [p]; gcongr
      _ = ENNReal.ofReal (3*Real.exp (-t)) := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hreal := ENNReal.toReal_le_toReal (measure_ne_top μ E) ENNReal.ofReal_ne_top |>.2 htotal
  have hrval : (ENNReal.ofReal (3*Real.exp (-t))).toReal = 3*Real.exp (-t) := ENNReal.toReal_ofReal (by positivity)
  rw [hrval] at hreal
  simpa only [measureReal_def, E, M, t, neg_div] using hreal
