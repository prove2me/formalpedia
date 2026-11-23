-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoComponentsFromDriversV1
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-23T21:20:13.955995+00:00
-- url     : https://prove2.me/submissions/2ade358e-6b68-4ab0-8eff-b9e58c7f608a

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma indep_map_of_comap {α β : Type*} {m₁ m₂ : MeasurableSpace β}
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} {f : α → β} (hf : Measurable f)
    (hm₁ : m₁ ≤ mβ) (hm₂ : m₂ ≤ mβ)
    (h : ProbabilityTheory.Indep (m₁.comap f) (m₂.comap f) μ) :
    ProbabilityTheory.Indep m₁ m₂ (μ.map f) := by
  rw [ProbabilityTheory.Indep_iff] at h ⊢
  intro s t hs ht
  have hsβ : MeasurableSet[mβ] s := hm₁ _ hs
  have htβ : MeasurableSet[mβ] t := hm₂ _ ht
  have hst : (μ.map f) (s ∩ t) = μ (f ⁻¹' (s ∩ t)) := Measure.map_apply hf (hsβ.inter htβ)
  have hs' : (μ.map f) s = μ (f ⁻¹' s) := Measure.map_apply hf hsβ
  have ht' : (μ.map f) t = μ (f ⁻¹' t) := Measure.map_apply hf htβ
  rw [hst, hs', ht', Set.preimage_inter]
  exact h (f ⁻¹' s) (f ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

private lemma exists_baseBrownian_cont :
    ∃ B₁ : LevyStochCalc.Brownian.BrownianMotion ProbabilityTheory.gaussianLimit,
      ∀ ω₁, Continuous (fun t => B₁.W t ω₁) := by
  classical
  have hmod := ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification
  let Y := hmod.choose
  have hYmeas : ∀ t, Measurable (Y t) := hmod.choose_spec.1
  have hYae : ∀ t, Y t =ᵐ[ProbabilityTheory.gaussianLimit] ProbabilityTheory.preBrownian t :=
    hmod.choose_spec.2.1
  have hYholder := hmod.choose_spec.2.2
  have hYpre : ProbabilityTheory.IsPreBrownianReal Y ProbabilityTheory.gaussianLimit :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.congr (fun t => (hYae t).symm)
  have hYcont : ∀ ω, Continuous (fun t => Y t ω) := by
    intro ω
    rw [continuous_iff_continuousAt]
    intro t
    have hβ_pos : (0 : ℝ≥0) < (1 / 4 : ℝ≥0) := by norm_num
    have hbdd : BddAbove (Set.range (fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)))) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨n, rfl⟩
      have hpos : (0 : ℝ) < 2 * ((n + 2 : ℕ) : ℝ) := by positivity
      rw [div_le_iff₀ hpos]
      push_cast
      linarith
    have hβ_lt : ((1 / 4 : ℝ≥0) : ℝ) <
        ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
      have h1 : ((1 / 4 : ℝ≥0) : ℝ) < (((1 + 2 : ℕ) : ℝ) - 1) / (2 * (1 + 2 : ℕ)) := by
        norm_num
      exact lt_of_lt_of_le h1 (le_ciSup hbdd 1)
    rcases hYholder ω t (1 / 4 : ℝ≥0) hβ_pos hβ_lt with ⟨U, hU, C, hHolder⟩
    exact (hHolder.continuousOn hβ_pos).continuousAt hU
  exact ⟨LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal hYpre hYmeas hYcont,
    fun ω₁ => LevyStochCalc.Brownian.continuous_realTime hYcont ω₁⟩

private lemma exists_zero_prm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    ∃ N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P (0 : Measure ℝ),
      ∀ ω, N.N ω = 0 := by
  classical
  have hpm0 : LevyStochCalc.Poisson.poissonMeasureENN 0 = Measure.dirac (0 : ℝ≥0∞) := by
    unfold LevyStochCalc.Poisson.poissonMeasureENN
    ext s hs
    rw [Measure.map_apply measurable_from_top hs, Measure.dirac_apply' _ hs]
    rw [ProbabilityTheory.poissonMeasure, Measure.sum_apply _ (measurable_from_top hs)]
    rw [tsum_eq_single 0]
    · simp [Measure.dirac_apply' _ (measurable_from_top hs), Set.indicator]
    · intro b hb
      cases b with
      | zero => exact absurd rfl hb
      | succ k => simp
  refine ⟨{
    N := fun _ => 0
    measurable_eval := fun _ => measurable_const
    integer_valued := fun _ _ => Filter.Eventually.of_forall (fun _ => ⟨0, by simp⟩)
    infinite_at_infinite_intensity := fun _ h => by
      simp [LevyStochCalc.Poisson.referenceIntensity] at h
    poisson_law := fun _ _ => by
      simp [LevyStochCalc.Poisson.referenceIntensity, hpm0, Measure.map_const]
    independent_disjoint := fun _ _ _ => by
      rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets _
      simp only [Measure.coe_zero, Pi.zero_apply]
      have hconst : ∀ i, (fun _ : Ω => (0 : ℝ≥0∞)) ⁻¹' sets i =
          if (0 : ℝ≥0∞) ∈ sets i then Set.univ else ∅ := fun i => by
        ext ω; by_cases h : (0 : ℝ≥0∞) ∈ sets i <;> simp [h]
      by_cases hall : ∀ i ∈ S, (0 : ℝ≥0∞) ∈ sets i
      · have hL : (⋂ i ∈ S, (fun _ : Ω => (0 : ℝ≥0∞)) ⁻¹' sets i) = Set.univ := by
          ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
          exact fun i hi => hall i hi
        rw [hL, measure_univ]
        symm
        apply Finset.prod_eq_one
        intro i hi
        rw [hconst i, if_pos (hall i hi), measure_univ]
      · push Not at hall
        rcases hall with ⟨i0, hi0, hnot⟩
        have hL : (⋂ i ∈ S, (fun _ : Ω => (0 : ℝ≥0∞)) ⁻¹' sets i) = ∅ := by
          ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro h; exact hnot (h i0 hi0)
        rw [hL, measure_empty]
        symm
        apply Finset.prod_eq_zero hi0
        rw [hconst i0, if_neg hnot, measure_empty]
    joint_past_future_independent := fun _ _ _ _ _ => by
      simp only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const, iSup_bot]
      exact ProbabilityTheory.indep_bot_left _ }, fun _ => rfl⟩

private lemma exists_nonzero_at_zero_brownian :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : LevyStochCalc.Brownian.BrownianMotion P) (ω₀ : Ω), B.W 0 ω₀ = 1 := by
  classical
  rcases exists_baseBrownian_cont with ⟨B₁, hB₁_cont⟩
  let Ω := (ℝ≥0 → ℝ) × Bool
  let emb : (ℝ≥0 → ℝ) → Ω := fun ω₁ => (ω₁, false)
  have hemb : Measurable emb := measurable_id.prodMk measurable_const
  let P : Measure Ω := ProbabilityTheory.gaussianLimit.map emb
  have hPprob : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hemb.aemeasurable
  let Wmod : ℝ → Ω → ℝ := fun t ω => if ω.2 then 1 else B₁.W t ω.1
  have hWmod_meas : ∀ t : ℝ, Measurable (Wmod t) := fun t => by
    have hpred : MeasurableSet {ω : Ω | ω.2 = true} :=
      (measurableSet_singleton true).preimage measurable_snd
    exact Measurable.ite hpred measurable_const ((B₁.measurable_eval t).comp measurable_fst)
  have hWmod_joint : Measurable (Function.uncurry Wmod) := by
    have hpred : MeasurableSet {p : ℝ × Ω | p.2.2 = true} :=
      (measurableSet_singleton true).preimage (measurable_snd.comp measurable_snd)
    have hcomp : Measurable (fun p : ℝ × Ω => B₁.W p.1 p.2.1) :=
      B₁.joint_measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact Measurable.ite hpred measurable_const hcomp
  let B : LevyStochCalc.Brownian.BrownianMotion P :=
    { W := Wmod
      measurable_eval := hWmod_meas
      joint_measurable := hWmod_joint
      initial_zero := by
        have h1 : ∀ᵐ ω₁ ∂ProbabilityTheory.gaussianLimit, Wmod 0 (emb ω₁) = 0 := by
          simpa [Wmod, emb] using B₁.initial_zero
        rw [ae_iff]
        have hms : MeasurableSet {ω : Ω | Wmod 0 ω ≠ 0} :=
          ((measurableSet_singleton (0 : ℝ)).preimage (hWmod_meas 0)).compl
        rw [Measure.map_apply hemb hms]
        simpa [ae_iff] using h1
      increment_gaussian := by
        intro s t hs hst
        have hsub : Measurable (fun ω : Ω => Wmod t ω - Wmod s ω) :=
          (hWmod_meas t).sub (hWmod_meas s)
        rw [Measure.map_map hsub hemb]
        have hcomp : (fun ω : Ω => Wmod t ω - Wmod s ω) ∘ emb =
            fun ω₁ => B₁.W t ω₁ - B₁.W s ω₁ := by
          funext ω₁; simp [Wmod, emb]
        rw [hcomp]
        exact B₁.increment_gaussian hs hst
      continuous_paths := ae_of_all _ fun ω => by
        rcases ω with ⟨ω₁, b⟩
        cases b with
        | true => simpa [Wmod] using (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
        | false => simpa [Wmod] using hB₁_cont ω₁
      negative_zero := by
        intro s hs
        have h1 : ∀ᵐ ω₁ ∂ProbabilityTheory.gaussianLimit, Wmod s (emb ω₁) = 0 := by
          simpa [Wmod, emb] using B₁.negative_zero s hs
        rw [ae_iff]
        have hms : MeasurableSet {ω : Ω | Wmod s ω ≠ 0} :=
          ((measurableSet_singleton (0 : ℝ)).preimage (hWmod_meas s)).compl
        rw [Measure.map_apply hemb hms]
        simpa [ae_iff] using h1
      joint_increment_independent := by
        intro s t hs hst
        have hm₁ : (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (Wmod j) inferInstance) ≤
            (inferInstance : MeasurableSpace Ω) :=
          iSup₂_le fun j _ => (hWmod_meas j).comap_le
        have hm₂ : MeasurableSpace.comap (fun ω => Wmod t ω - Wmod s ω) inferInstance ≤
            (inferInstance : MeasurableSpace Ω) :=
          ((hWmod_meas t).sub (hWmod_meas s)).comap_le
        refine indep_map_of_comap hemb hm₁ hm₂ ?_
        have hc₁ : (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (Wmod j) inferInstance).comap emb =
            ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (B₁.W j) inferInstance := by
          rw [MeasurableSpace.comap_iSup]
          refine iSup_congr fun j => ?_
          rw [MeasurableSpace.comap_iSup]
          refine iSup_congr fun _ => ?_
          rw [MeasurableSpace.comap_comp]
          rfl
        have hc₂ : (MeasurableSpace.comap (fun ω => Wmod t ω - Wmod s ω) inferInstance).comap emb =
            MeasurableSpace.comap (fun ω₁ => B₁.W t ω₁ - B₁.W s ω₁) inferInstance := by
          rw [MeasurableSpace.comap_comp]
          rfl
        rw [hc₁, hc₂]
        exact B₁.joint_increment_independent hs hst }
  exact ⟨Ω, inferInstance, P, hPprob, B, ((fun _ => (0 : ℝ)), true), rfl⟩

theorem solution :
    ¬ (∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
      (_ : ProbabilityTheory.IsLevyMeasure levyMeasure)
      [SigmaFinite levyMeasure]
      {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (B : LevyStochCalc.Brownian.BrownianMotion P)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
      (_ : ProbabilityTheory.IndepFun
        (fun ω => fun (t : ℝ) => B.W t ω)
        (fun ω => N.N ω) P),
      ∃ (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
        (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
        (∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) ∧
        (∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω) ∧
        ProbabilityTheory.IsLevyProcess Xgauss P ∧
        ProbabilityTheory.IsLevyProcess Xlarge P ∧
        ProbabilityTheory.IsLevyProcess Xsmall P ∧
        Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
        MeasureTheory.Martingale Xsmall ℱ P ∧
        (∀ t, MemLp (Xsmall t) 2 P) ∧
        (∀ᵐ ω ∂P,
          (∀ t : ℝ≥0,
            ContinuousWithinAt (fun s => Xsmall s ω) (Set.Ici t) t) ∧
          Set.Countable
            {t : ℝ≥0 | ¬ ContinuousAt (fun s => Xsmall s ω) t} ∧
          ∀ t : ℝ≥0, 0 < t →
            ∃ l : ℝ,
              Tendsto (fun s => Xsmall s ω) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
              (Xsmall t ω ≠ l → |Xsmall t ω - l| < 1)) ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (Xsmall t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              ∫ x in Set.Ioo (-1 : ℝ) 1,
                ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) ∧
        Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) := by
  intro hthm
  rcases exists_nonzero_at_zero_brownian with ⟨Ω, mΩ, P, hPprob, B, ω₀, hB0⟩
  rcases exists_zero_prm P with ⟨N, hN0⟩
  have hlevy : ProbabilityTheory.IsLevyMeasure (0 : Measure ℝ) := ⟨by simp, by simp⟩
  have hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P := by
    have hfun : (fun ω => N.N ω) = fun _ => (0 : Measure (ℝ × ℝ)) := funext hN0
    rw [hfun, ProbabilityTheory.IndepFun_iff_Indep, MeasurableSpace.comap_const]
    exact ProbabilityTheory.indep_bot_right _
  rcases hthm 0 1 0 hlevy P B N hDrivers with
    ⟨Xgauss, _, _, _, hXg_eq, _, hXg_levy, _⟩
  have h0 : Xgauss 0 ω₀ = 0 := congrFun hXg_levy.start_zero ω₀
  have h1 : Xgauss 0 ω₀ = 1 := by
    have := hXg_eq 0 ω₀
    simpa [hB0] using this
  linarith
