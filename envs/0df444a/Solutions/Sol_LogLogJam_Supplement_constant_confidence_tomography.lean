-- Prove2me | solution 1 for LogLogJam.Supplement.constant_confidence_tomography
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:42.027626+00:00
-- url     : https://prove2.me/submissions/0085a096-6410-4b02-b0e6-de680a7210bf

import Mathlib
import Theorems.Thm_LogLogJam_Supplement_split_tomography

open MeasureTheory ProbabilityTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

open LogLogJam LogLogJam.Supplement

/-- The exact success functional and integer sample threshold of registered
Theorem 8.16 in the usual high-confidence range δ ≤ 1/2. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 3 → 0 < δ → δ ≤ 1 / 2 →
    ∀ m : ℕ, C * Real.log (1 / δ) / ε ^ 2 ≤ m →
    ∃ (S : AdaptiveScheme 1 m ℝ)
      (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
      (∀ (t : Fin m) (x y : Fin t → ℝ), S.povm t x = S.povm t y) ∧
      IsMarkovKernel est ∧
      ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
        ENNReal.ofReal (1 - δ) ≤ ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
          traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
          ∂(transcriptLaw S ρ.coefficients) := by
  obtain ⟨K, hK, alg⟩ := split_tomography
  refine ⟨75 * K, by positivity, ?_⟩
  intro ε δ he he' hd hd' m hm
  have hlog : Real.log (2 / (δ / 2)) ≤ 3 * Real.log (1 / δ) := by
    have two_pos : 0 < (2 : ℝ) := by norm_num
    have h₀ : 2 ≤ 1 / δ := (le_div_iff₀ hd).mpr (by linarith)
    have hlog' := Real.log_le_log two_pos h₀
    rw [show 2 / (δ / 2) = 2 * (2 * (1 / δ)) by ring,
      Real.log_mul (by norm_num) (by positivity : 2 * (1 / δ) ≠ 0), Real.log_mul (by norm_num) (by positivity : 1 / δ ≠ 0)]
    linarith
  have hn : K * Real.log (2 / (δ / 2)) / (ε / 5)^2 ≤ m := by
    refine le_trans ?_ hm
    rw [show K * Real.log (2 / (δ / 2)) / (ε / 5)^2 =
      (25 * K * Real.log (2 / (δ / 2))) / ε^2 by ring]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hlog hK.le]) (sq_nonneg ε)
  obtain ⟨S, D, hS, hD, hpure, hfail⟩ := alg (ε/5) (δ/2) (by positivity) (by linarith)
    (by positivity) (by linarith) m hn
  refine ⟨S, Kernel.deterministic D hD, hS.1, inferInstance, ?_⟩
  intro ρ hρ
  let ν := transcriptLaw S ρ.coefficients
  let bad := {x | ENNReal.ofReal ε < traceDist ρ.coefficients (D x).coefficients}
  have hb : ν bad ≤ ENNReal.ofReal δ := by
    simpa only [show 5 * (ε/5) = ε by ring, show 2 * (δ/2) = δ by ring] using hfail ρ hρ
  have hprob (t : ℕ) (ht : t ≤ m) : IsProbabilityMeasure (sequentialLaw (S.round ρ.coefficients) t ht) := by
    induction t with
    | zero => simpa [sequentialLaw] using (inferInstance : IsProbabilityMeasure (Measure.dirac (fun i : Fin 0 => Fin.elim0 (α := ℝ) i)))
    | succ t ih =>
      let :=  ih (Nat.le_of_succ_le ht)
      let :=  S.round_markov ρ.coefficients ⟨t,ht⟩
      simp only [sequentialLaw]
      apply Measure.isProbabilityMeasure_map
      apply Measurable.aemeasurable
      refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using (measurable_snd : Measurable (Prod.snd : (Fin t → ℝ) × ℝ → ℝ))
      · simpa [Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_fst : Measurable (Prod.fst : (Fin t → ℝ) × ℝ → (Fin t → ℝ)))
  let : IsProbabilityMeasure ν := hprob m le_rfl
  let H := toMeasurable ν bad
  have hH : MeasurableSet H := measurableSet_toMeasurable _ _
  have hCompl : ENNReal.ofReal (1 - δ) ≤ ν Hᶜ := by
    rw [measure_compl hH (measure_ne_top _ _), measure_univ, ENNReal.ofReal_sub 1 hd.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left ((measure_toMeasurable bad).trans_le hb) _
  refine hCompl.trans ?_
  rw [← lintegral_indicator_one hH.compl]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ Hᶜ
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    change 1 ≤ Measure.dirac (D x) _
    rw [Measure.dirac_apply_of_mem]
    exact ⟨hpure x, le_of_not_gt (fun badx => hx ((subset_toMeasurable ν bad) badx))⟩
  · simp [Set.indicator_of_notMem hx]
