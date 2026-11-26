-- Prove2me | solution 1 for LogLogJam.Supplement.weak_success_localization
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:27:06.00404+00:00
-- url     : https://prove2.me/submissions/25e4027f-cbb7-4252-947d-8b02bd4fc9fb

import Mathlib
import Theorems.Thm_LogLogJam_Supplement_split_tomography
import Theorems.Thm_LogLogJam_Supplement_one_readout_localization
import Theorems.Thm_LogLogJam_Supplement_local_randomized_refinement
open MeasureTheory ProbabilityTheory BosonicLearn Filter
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open LogLogJam LogLogJam.Supplement
open scoped ENNReal Classical

private theorem transcript_probability {m : ℕ} (S : AdaptiveScheme 1 m ℝ) (ρ : State (Occupation (Fin 1))) :
    IsProbabilityMeasure (transcriptLaw S ρ.coefficients) := by
  have h (t : ℕ) (ht : t ≤ m) : IsProbabilityMeasure (sequentialLaw (S.round ρ.coefficients) t ht) := by
    induction t with
    | zero => simpa [sequentialLaw] using (inferInstance : IsProbabilityMeasure (Measure.dirac (fun i : Fin 0 => Fin.elim0 (α := ℝ) i)))
    | succ t ih =>
      let := ih (Nat.le_of_succ_le ht)
      let := S.round_markov ρ.coefficients ⟨t,ht⟩
      simp only [sequentialLaw]
      apply Measure.isProbabilityMeasure_map
      apply Measurable.aemeasurable
      refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using (measurable_snd : Measurable (Prod.snd : (Fin t → ℝ) × ℝ → ℝ))
      · simpa [Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_fst : Measurable (Prod.fst : (Fin t → ℝ) × ℝ → (Fin t → ℝ)))
  exact h m le_rfl

private theorem good_integral {X : Type} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (e : X → ℝ≥0∞) (d : ℝ≥0∞) (f : X → ℝ≥0∞) (k : ℝ≥0∞)
    (hfail : ν {x | d < e x} ≤ ENNReal.ofReal (1/4)) (h : ∀ x, e x ≤ d → k ≤ f x) :
    ENNReal.ofReal (1/2) * k ≤ ∫⁻ x, f x ∂ν := by
  let bad := {x | d < e x}
  let H := toMeasurable ν bad
  have hH : MeasurableSet H := measurableSet_toMeasurable _ _
  have hG : ENNReal.ofReal (1/2) ≤ ν Hᶜ := by
    rw [measure_compl hH (measure_ne_top _ _),measure_univ]
    have ht : ν H ≤ ENNReal.ofReal (1/4) := (measure_toMeasurable bad).trans_le hfail
    refine le_trans ?_ (tsub_le_tsub_left ht 1)
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 (by norm_num : 0≤(1/4:ℝ))]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  calc
    _ ≤ ν Hᶜ * k := by gcongr
    _ = ∫⁻ x, Hᶜ.indicator (fun _ => k) x ∂ν := by rw [lintegral_indicator hH.compl,lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ _ := by
      apply lintegral_mono;intro x
      by_cases hx : x∈Hᶜ
      · rw [Set.indicator_of_mem hx];apply h;exact le_of_not_gt (fun hx' => hx (subset_toMeasurable ν bad hx'))
      · simp [Set.indicator_of_notMem hx]

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 3 →
    ∀ m : ℕ, 1 ≤ m →
      ∃ (S : AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (min (1/2) (c*(m:ℝ)*ε^2)) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧ traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(transcriptLaw S ρ.coefficients) := by
  obtain ⟨C,hC,alg⟩ := split_tomography
  obtain ⟨b,hb,one⟩ := one_readout_localization
  obtain ⟨a,ha,localize⟩ := local_randomized_refinement
  let K := 25*C*Real.log 16
  have hK : 0<K := mul_pos (by positivity) (Real.log_pos (by norm_num))
  let c := min (b/(9*K)) (a/(2*K))
  refine ⟨c, lt_min (by positivity) (by positivity), ?_⟩
  intro ε he hε m hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases hlow : (m:ℝ) < 9*K
  · obtain ⟨S,L,hS,hL,hl⟩ := one ε he hε m hm
    refine ⟨S,L,hS,hL,fun ρ hρ => (ENNReal.ofReal_le_ofReal ?_).trans (hl ρ hρ)⟩
    refine (min_le_right ..).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    calc
      c*(m:ℝ) ≤ b/(9*K)*m := mul_le_mul_of_nonneg_right (min_le_left ..) hmpos.le
      _ ≤ b/(9*K)*(9*K) := mul_le_mul_of_nonneg_left hlow.le (by positivity)
      _ = b := div_mul_cancel₀ _ (by positivity)
  let d := Real.sqrt (K/m)
  have hd : 0<d := Real.sqrt_pos.2 (div_pos hK hmpos)
  have hd2 : d^2 = K/m := Real.sq_sqrt (by positivity)
  have hdm : d^2 * m = K := by rw [hd2,div_mul_cancel₀ _ hmpos.ne']
  have hsmall : d ≤ 1/3 := by
    have h₁ : d^2 ≤ 1/9 := by rw [hd2];apply (div_le_iff₀ hmpos).mpr;linarith [le_of_not_gt hlow]
    nlinarith
  have hn : C*Real.log (2/(1/8:ℝ))/(d/5)^2 ≤ m := by
    rw [show (2/(1/8:ℝ))=16 by norm_num]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [K] at hdm; nlinarith only [hdm]
  obtain ⟨S,D,hS,hD,hpure,hfail⟩ := alg (d/5) (1/8) (by positivity) (by linarith)
    (by norm_num) (by norm_num) m hn
  have hf (ρ) (hρ : IsPureCentGauss ρ) : transcriptLaw S ρ.coefficients
      {x | ENNReal.ofReal d < traceDist ρ.coefficients (D x).coefficients} ≤ ENNReal.ofReal (1/4) := by
    simpa only [show 5*(d/5)=d by ring,show 2*(1/8:ℝ)=1/4 by norm_num] using hfail ρ hρ
  by_cases hc : d ≤ ε
  · refine ⟨S,Kernel.deterministic D hD,hS.1,inferInstance,?_⟩
    intro ρ hρ
    let _ := transcript_probability S ρ
    refine (ENNReal.ofReal_le_ofReal (min_le_left ..)).trans ?_
    rw [← mul_one (ENNReal.ofReal (1/2))]
    apply good_integral _ _ _ _ _ (hf ρ hρ)
    intro x hx
    change 1 ≤ Measure.dirac (D x) _
    apply le_of_eq; symm; apply Measure.dirac_apply_of_mem
    exact ⟨hpure x,hx.trans (ENNReal.ofReal_le_ofReal hc)⟩
  · obtain ⟨L,hL,hl⟩ := localize ε d he (le_of_not_ge hc) hsmall
    let _ := hL
    refine ⟨S,L.comap D hD,hS.1,inferInstance,?_⟩
    intro ρ hρ
    let _ := transcript_probability S ρ
    have hcoeff : c*(m:ℝ)*ε^2 ≤ (1/2)*(a*(ε/d)^2) := by
      have hc' : c ≤ a/(2*K) := min_le_right .. 
      calc
        _ ≤ (a/(2*K))*(m:ℝ)*ε^2 := by gcongr
        _ = _ := by rw [← hdm];field_simp
    refine (ENNReal.ofReal_le_ofReal ((min_le_right ..).trans hcoeff)).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num : 0≤(1/2:ℝ))]
    apply good_integral _ _ _ _ _ (hf ρ hρ)
    intro x hx
    exact hl (D x) ρ (hpure x) hρ hx
