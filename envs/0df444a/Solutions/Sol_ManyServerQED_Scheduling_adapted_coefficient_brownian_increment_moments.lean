-- Prove2me | solution 1 for ManyServerQED.Scheduling.adapted_coefficient_brownian_increment_moments
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:15:15.810139+00:00
-- url     : https://prove2.me/submissions/15322c95-4e54-4365-89a8-a8bfa0e8f0f0

import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter
open ManyServerQED.Scheduling
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin k → ℝ) (hW : IsStdFBrownian P F W)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Ω → ℝ) (hA : Measurable[F s] A) (i j : Fin k) :
    (∫ ω, A ω * (W t ω i - W s ω i) ∂P) = 0 ∧
      (∫ ω, A ω * ((W t ω i - W s ω i) * (W t ω j - W s ω j)) ∂P) =
        (if i = j then (t:ℝ) - (s:ℝ) else 0) * (∫ ω, A ω ∂P) := by
  let d (i : Fin k) (ω : Ω) := W t ω i - W s ω i
  let V (ω : Ω) (u : ℝ≥0) := W (s + u) ω - W s ω
  let mV : MeasurableSpace Ω := MeasurableSpace.comap V inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hV : @Measurable Ω (ℝ≥0 → Fin k → ℝ) mV inferInstance V :=
    Measurable.of_comap_le le_rfl
  have hD (i : Fin k) : @Measurable Ω ℝ mV inferInstance (d i) := by
    have hh := (measurable_pi_apply i).comp ((measurable_pi_apply (t-s)).comp hV)
    have hs : s + (t-s) = t := add_tsub_cancel_of_le hst
    simpa [Function.comp_def, V, d, hs] using hh
  have hAmbient (i : Fin k) : AEMeasurable (d i) P :=
    ((hW.brownian i).isGaussianProcess.aemeasurable t).sub
      ((hW.brownian i).isGaussianProcess.aemeasurable s)
  have hAa : @Measurable Ω ℝ mΩ inferInstance A := hA.mono (F.le s) le_rfl
  have hInd {Q : Ω → ℝ} (hQ : @Measurable Ω ℝ mV inferInstance Q) :
      IndepFun A Q P :=
    indep_of_indep_of_le (hW.indep_incr s).symm hA.comap_le hQ.comap_le
  have hmean (i : Fin k) : (∫ ω, d i ω ∂P) = 0 := by
    have hm := ((hW.brownian i).hasLaw_sub t s).integral_eq
    change (∫ ω, d i ω ∂P) = _ at hm
    simpa only [integral_id_gaussianReal] using hm
  have hcross : (∫ ω, d i ω * d j ω ∂P) = if i=j then (t:ℝ)-(s:ℝ) else 0 := by
    classical
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hstR : (s:ℝ) ≤ (t:ℝ) := by exact_mod_cast hst
      have hL := (hW.brownian i).hasLaw_sub t s
      have h1 : ∫ ω, d i ω ^ 2 ∂P =
          ∫ z, z ^ 2 ∂(gaussianReal 0 (nndist ((t : ℝ≥0) : ℝ) (s : ℝ))) :=
        hL.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
      have h2 := variance_fun_id_gaussianReal (μ := (0 : ℝ))
        (v := nndist ((t : ℝ≥0) : ℝ) (s : ℝ))
      rw [variance_eq_integral (X := fun z : ℝ => z) aemeasurable_id'] at h2
      simp only [integral_id_gaussianReal, sub_zero] at h2
      simp only [← pow_two]
      rw [h1, h2, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hstR)]
    · rw [if_neg hij]
      let G (f : ℝ≥0 → ℝ) := f t - f s
      have hG : Measurable G := (measurable_pi_apply t).sub (measurable_pi_apply s)
      have hxy : IndepFun (d i) (d j) P := (hW.indep_coord.indepFun hij).comp hG hG
      rw [hxy.integral_fun_mul_eq_mul_integral (hAmbient i).aestronglyMeasurable
        (hAmbient j).aestronglyMeasurable, hmean,zero_mul]
  constructor
  · change (∫ ω, A ω * d i ω ∂P) = 0
    rw [(hInd (hD i)).integral_fun_mul_eq_mul_integral hAa.aestronglyMeasurable
      (hAmbient i).aestronglyMeasurable, hmean,mul_zero]
  · classical
    change (∫ ω, A ω * (d i ω*d j ω) ∂P) = _
    have he := (hInd ((hD i).mul (hD j))).integral_fun_mul_eq_mul_integral hAa.aestronglyMeasurable
      ((hAmbient i).mul (hAmbient j)).aestronglyMeasurable
    change (∫ ω, A ω * (d i ω * d j ω) ∂P) =
      (∫ ω, A ω ∂P) * ∫ ω, d i ω * d j ω ∂P at he
    rw [he, hcross]
    ring
