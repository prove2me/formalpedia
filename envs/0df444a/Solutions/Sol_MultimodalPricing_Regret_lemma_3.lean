-- Prove2me | solution 1 for MultimodalPricing.Regret.lemma_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T23:35:33.091216+00:00
-- url     : https://prove2.me/submissions/d55cd244-01c9-490e-9919-1661c30ee0c7

import Definitions.Def_MultimodalPricing_Regret_Regret
import Mathlib

open MeasureTheory ProbabilityTheory MultimodalPricing.Regret

namespace MultimodalPricingLemma3Disproof

noncomputable def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

lemma measurable_clampUnit : Measurable clampUnit :=
  measurable_const.max (measurable_const.min measurable_id)

lemma clampUnit_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clampUnit x = x := by
  simp [clampUnit, min_eq_right h1, max_eq_right h0]

noncomputable def detKernel (M : ℝ) : DemandKernel :=
  Kernel.deterministic (fun hp : ObservationPrefix × ℝ => clampUnit (hp.2 - M))
    (measurable_clampUnit.comp (measurable_snd.sub measurable_const))

lemma smooth_shifted (M : ℝ) : Smooth 1 1 M (M + 1) (fun p => p - M) := by
  refine ⟨le_rfl, one_pos, by linarith, ?_, ⟨fun _ p => p - M, ?_, ?_, ?_, ?_⟩⟩
  · intro p hp
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  · intro p _
    rfl
  · intro q hq
    omega
  · intro q _ p hp
    rw [abs_le]
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  · intro p _ p' _
    have hsub : (p - M) - (p' - M) = p - p' := by ring
    rw [hsub, one_mul]

lemma isDemandKernel_shifted (M : ℝ) :
    IsDemandKernel M (M + 1) (fun p => p - M) (detKernel M) := by
  refine ⟨by unfold detKernel; infer_instance, fun h p hp => ?_⟩
  have h0 : 0 ≤ p - M := by linarith [hp.1]
  have h1 : p - M ≤ 1 := by linarith [hp.2]
  have hcl : clampUnit (p - M) = p - M := clampUnit_of_mem h0 h1
  have hk : detKernel M (h, p) = Measure.dirac (p - M) := by
    simp [detKernel, Kernel.deterministic_apply, hcl]
  rw [hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Icc]
    have hmem : p - M ∈ Set.Icc (0 : ℝ) 1 := ⟨h0, h1⟩
    simp [Set.indicator_of_mem hmem]
  · exact integrable_dirac (by simp)
  · simp

noncomputable def obsConst (M : ℝ) : Observation PUnit where
  info := Filtration.const ℕ inferInstance le_rfl
  price := fun _ _ => M
  demand := fun _ _ => 0

lemma isObservation_shifted (M : ℝ) :
    IsObservation (Measure.dirac PUnit.unit) 1 M (M + 1) (fun p => p - M) (obsConst M) := by
  refine ⟨detKernel M, isDemandKernel_shifted M, ?_, ?_, ?_, ?_⟩
  · intro n _
    exact measurable_const
  · intro n _
    exact measurable_const
  · exact Filter.Eventually.of_forall (fun _ n _ => by
      dsimp [obsConst]
      exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, zero_le_one⟩⟩)
  · intro n _ A _ S hS
    have hk (ω) : (detKernel M (observationPrefix (obsConst M).price (obsConst M).demand n ω,
        (obsConst M).price n ω)) S = (Measure.dirac (0 : ℝ)) S := by
      simp [detKernel, obsConst, Kernel.deterministic_apply, clampUnit]
    rw [lintegral_congr hk]
    by_cases hu : PUnit.unit ∈ A
    · have hA_eq : A = Set.univ := Set.eq_univ_of_forall fun ω => by cases ω; exact hu
      rw [hA_eq, Measure.restrict_univ, Set.univ_inter, lintegral_const, measure_univ, mul_one]
      by_cases h0 : (0 : ℝ) ∈ S
      · have hpre : (obsConst M).demand n ⁻¹' S = Set.univ := Set.eq_univ_of_forall fun _ => h0
        rw [hpre, measure_univ, Measure.dirac_apply_of_mem h0]
      · have hpre : (obsConst M).demand n ⁻¹' S = ∅ := by
          ext _; simp [obsConst, h0]
        rw [hpre, measure_empty, Measure.dirac_apply' _ hS]
        simp [h0]
    · have hA_eq : A = ∅ := by
        ext ω; cases ω; simp [hu]
      rw [hA_eq, Set.empty_inter, measure_empty, Measure.restrict_empty, lintegral_zero_measure]

lemma localRun_shifted (M δ : ℝ) :
    LocalRun (Measure.dirac PUnit.unit) 1 1 M (M + 1) 1 1 δ (obsConst M) := by
  refine Filter.Eventually.of_forall (fun _ n hn => ?_)
  obtain rfl : n = 0 := by omega
  refine ⟨?_, fun hne => False.elim (hne (by simp [history]))⟩
  dsimp [obsConst]
  exact ⟨le_rfl, by linarith⟩

lemma bestReward_ge (M : ℝ) (hM : 0 ≤ M) :
    M + 1 ≤ bestReward M (M + 1) (fun p => p - M) := by
  unfold bestReward
  apply le_csSup
  · refine ⟨M + 1, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    unfold reward
    have hq0 : 0 ≤ q := by linarith [hq.1]
    have hq1 : q ≤ M + 1 := hq.2
    have hqm0 : 0 ≤ q - M := by linarith [hq.1]
    have hqm1 : q - M ≤ 1 := by linarith [hq.2]
    nlinarith
  · refine ⟨M + 1, ⟨by linarith, le_rfl⟩, ?_⟩
    unfold reward
    ring

end MultimodalPricingLemma3Disproof

open MultimodalPricingLemma3Disproof in
theorem solution : ¬ (∃ B : ℝ, 0 < B ∧
      ∀ (k T t : ℕ) (C a b Δ : ℝ) (f : ℝ → ℝ),
      Smooth k C a b f → 0 ≤ a → C * (b - a) ^ k ≤ Δ →
      1 ≤ t → t ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (O : Observation Ω),
        IsObservation μ t a b f O →
        LocalRun μ t k a b C Δ (1 / (T : ℝ) ^ 2) O →
        μ {ω | (Δ + max 1 C / Real.sqrt t) * (3 * k * Real.log (2 * k * T)) <
          averagePseudoRegret t a b f O.price ω} ≤ ENNReal.ofReal (B / T)) := by
  rintro ⟨B, hB, H⟩
  let T : ℕ := ⌈B⌉₊ + 2
  have hT1 : 1 ≤ T := by omega
  have hBT : B / (T : ℝ) < 1 := by
    have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    have hTpos : (0 : ℝ) < (T : ℝ) := by positivity
    rw [div_lt_one hTpos]
    dsimp [T]
    push_cast
    linarith
  let thresh : ℝ := (1 + max (1 : ℝ) 1 / Real.sqrt (1 : ℕ)) *
    (3 * (1 : ℕ) * Real.log (2 * (1 : ℕ) * (T : ℝ)))
  let M : ℝ := max 0 thresh
  have hM0 : 0 ≤ M := le_max_left 0 thresh
  have hM_th : thresh ≤ M := le_max_right 0 thresh
  have hbound : (1 : ℝ) * ((M + 1) - M) ^ (1 : ℕ) ≤ 1 := by norm_num
  have hprob := H 1 T 1 1 M (M + 1) 1 (fun p => p - M)
    (smooth_shifted M) hM0 hbound le_rfl hT1
    PUnit (Measure.dirac PUnit.unit) (obsConst M)
    (isObservation_shifted M) (localRun_shifted M (1 / (T : ℝ) ^ 2))
  have havg : M + 1 ≤ averagePseudoRegret 1 M (M + 1) (fun p => p - M) (obsConst M).price PUnit.unit := by
    unfold averagePseudoRegret
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, div_one, obsConst, reward, sub_self,
      mul_zero, sub_zero]
    exact bestReward_ge M hM0
  have hmem : PUnit.unit ∈ {ω : PUnit |
      ((1 : ℝ) + max 1 1 / Real.sqrt (1 : ℕ)) * (3 * (1 : ℕ) * Real.log (2 * (1 : ℕ) * (T : ℝ))) <
        averagePseudoRegret 1 M (M + 1) (fun p => p - M) (obsConst M).price ω} := by
    change thresh < averagePseudoRegret 1 M (M + 1) (fun p => p - M) (obsConst M).price PUnit.unit
    linarith
  have hmeas_one : (Measure.dirac PUnit.unit : Measure PUnit) {ω : PUnit |
      ((1 : ℝ) + max 1 1 / Real.sqrt (1 : ℕ)) * (3 * (1 : ℕ) * Real.log (2 * (1 : ℕ) * (T : ℝ))) <
        averagePseudoRegret 1 M (M + 1) (fun p => p - M) (obsConst M).price ω} = 1 := by
    rw [Measure.dirac_apply_of_mem hmem]
  rw [hmeas_one] at hprob
  have hrhs_lt : ENNReal.ofReal (B / (T : ℝ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr hBT
  exact not_lt_of_ge hprob hrhs_lt
