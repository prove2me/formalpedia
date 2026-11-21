-- Prove2me | solution 1 for MeasureTheory.conditional_mean_of_eventwise_probability_law
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T15:27:43.5441+00:00
-- url     : https://prove2.me/submissions/bc63d021-d16d-44e0-bae7-85559c2dabf6

import Mathlib

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal

private lemma simpleFunc_integrable_of_isProbabilityMeasure
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (s : SimpleFunc E ℝ) :
    Integrable (⇑s) μ := by
  refine Integrable.of_bound s.stronglyMeasurable.aestronglyMeasurable (∑ y ∈ s.range, |y|) ?_
  filter_upwards with x
  have hx : s x ∈ s.range := SimpleFunc.mem_range_self s x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun i _ => abs_nonneg i) hx

theorem solution
    {Ω : Type*} {E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → E) (hX : Measurable X)
    (ν : Ω → Measure E) (hν : ∀ ω, IsProbabilityMeasure (ν ω))
    (hLaw : ∀ B : Set E, MeasurableSet B →
      P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P]
        fun ω => (ν ω B).toReal)
    (f : E → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ω, ∀ᵐ x ∂(ν ω), ‖f x‖ ≤ C) :
    Integrable (fun ω => f (X ω)) P ∧
      P[(fun ω => f (X ω)) | m] =ᵐ[P] fun ω => ∫ x, f x ∂(ν ω) := by
  classical
  have hXa : @Measurable Ω E mΩ _ X := hX.mono hm le_rfl
  have hpre : ∀ u : Set E, MeasurableSet u → @MeasurableSet Ω mΩ (X ⁻¹' u) :=
    fun u hu => hu.preimage hXa
  haveI hPtrim : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  haveI hPtrimS : SigmaFinite (P.trim hm) := inferInstance
  -- ### Step 1: the a.e. bound set
  set B : Set E := {x | ‖f x‖ ≤ C} with hB
  have hBm : MeasurableSet B := by
    rw [hB]; exact measurableSet_le hf.norm measurable_const
  have hνB : ∀ ω, ν ω B = 1 := by
    intro ω
    haveI := hν ω
    have h0 : ν ω Bᶜ = 0 := by
      have h' : ν ω {x : E | ¬ ‖f x‖ ≤ C} = 0 := ae_iff.mp (hbound ω)
      have hset : Bᶜ = {x : E | ¬ ‖f x‖ ≤ C} := by rw [hB]; rfl
      rw [hset]; exact h'
    have hcomp := measure_compl (μ := ν ω) hBm.compl (measure_ne_top (ν ω) _)
    rw [compl_compl] at hcomp
    rw [hcomp, h0, measure_univ, tsub_zero]
  -- ### Step 2: P (X ⁻¹' B) = 1
  have hPB : P (X ⁻¹' B) = 1 := by
    have hlaw := hLaw B hBm
    have hone : (fun ω => (ν ω B).toReal) = fun _ => (1 : ℝ) := by
      funext ω; rw [hνB ω, ENNReal.toReal_one]
    have e1 : ∫ ω, (P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m]) ω ∂P = 1 := by
      rw [integral_congr_ae hlaw, hone]
      simp
    have e2 : ∫ ω, (P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m]) ω ∂P = P.real (X ⁻¹' B) := by
      rw [integral_condExp (μ := P) (m := m)
        (f := (X ⁻¹' B).indicator (fun _ => (1 : ℝ))) hm]
      exact integral_indicator_one (hpre B hBm)
    have h1 : P.real (X ⁻¹' B) = 1 := by rw [← e2, e1]
    rw [Measure.real_def, ENNReal.toReal_eq_one_iff] at h1
    exact h1
  have hae_bound : ∀ᵐ ω ∂P, ‖f (X ω)‖ ≤ C := by
    rw [ae_iff]
    have hc : P (X ⁻¹' B)ᶜ = 0 := by
      have hcomp := measure_compl (μ := P) (hpre B hBm) (measure_ne_top P (X ⁻¹' B))
      rw [hPB, measure_univ] at hcomp
      rw [hcomp, tsub_self]
    have hset : {ω | ¬ ‖f (X ω)‖ ≤ C} = (X ⁻¹' B)ᶜ := by rw [hB]; rfl
    rw [hset]; exact hc
  have hInt_fX : Integrable (fun ω => f (X ω)) P :=
    Integrable.of_bound (hf.comp hXa).aestronglyMeasurable C hae_bound
  -- ### Step 3: measurability of ω ↦ ∫ f d(ν ω)
  have hsum_meas : ∀ (t : Finset ℝ) (u : ℝ → Ω → ℝ), (∀ y ∈ t, Measurable[m] (u y)) →
      Measurable[m] (fun ω => ∑ y ∈ t, u y ω) := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using measurable_const (μ := P) (b := (0 : ℝ))
    | insert a t ha ih =>
      have h1 : (fun ω => ∑ i ∈ insert a t, u i ω) = fun ω => u a ω + ∑ i ∈ t, u i ω := by
        funext ω; rw [Finset.sum_insert ha]
      rw [h1]
      exact (hu a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))
  have h0mem : (0 : ℝ) ∈ Set.Icc (-C) C := ⟨by linarith, hC⟩
  set sf : ℕ → SimpleFunc E ℝ :=
    fun n => SimpleFunc.approxOn f hf (Set.Icc (-C) C) 0 h0mem n with hsf
  have hsf_mem : ∀ n x, sf n x ∈ Set.Icc (-C) C := fun n x => SimpleFunc.approxOn_mem hf h0mem n x
  have hsf_norm : ∀ n x, ‖sf n x‖ ≤ C := by
    intro n x
    have h := hsf_mem n x
    rw [Set.mem_Icc] at h
    simpa [Real.norm_eq_abs] using abs_le.mpr h
  have hconv : ∀ ω, Tendsto (fun n => ∫ x, sf n x ∂(ν ω)) atTop (𝓝 (∫ x, f x ∂(ν ω))) := by
    intro ω
    haveI := hν ω
    refine tendsto_integral_of_dominated_convergence (μ := ν ω) (F := fun n x => sf n x) (f := f)
      (fun _ => C) (fun n => (sf n).stronglyMeasurable.aestronglyMeasurable)
      (integrable_const C) ?_ ?_
    · intro n
      filter_upwards with x using hsf_norm n x
    · filter_upwards [hbound ω] with x hx
      refine SimpleFunc.tendsto_approxOn hf h0mem (x := x) (subset_closure ?_)
      rw [Set.mem_Icc]
      exact abs_le.mp (by simpa [Real.norm_eq_abs] using hx)
  set G : ℕ → Ω → ℝ := fun n ω =>
    ∑ y ∈ (sf n).range, y * (P[(X ⁻¹' ((sf n) ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) | m]) ω with hG
  have hG_meas : ∀ n, Measurable[m] (G n) := by
    intro n
    refine hsum_meas _ _ ?_
    intro y _
    exact stronglyMeasurable_condExp.measurable.const_mul y
  have hG_eq : ∀ n, (fun ω => ∫ x, sf n x ∂(ν ω)) =ᵐ[P] G n := by
    intro n
    have hper : ∀ ω, ∫ x, sf n x ∂(ν ω)
        = ∑ y ∈ (sf n).range, y * (ν ω).real ((sf n) ⁻¹' {y}) := by
      intro ω
      haveI := hν ω
      rw [SimpleFunc.integral_eq_sum _
        (simpleFunc_integrable_of_isProbabilityMeasure (ν ω) (sf n))]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_eq_mul, mul_comm]
    have hterm : ∀ y ∈ (sf n).range,
        (fun ω => y * (ν ω).real ((sf n) ⁻¹' {y}))
          =ᵐ[P] (fun ω => y * (P[(X ⁻¹' ((sf n) ⁻¹' {y})).indicator
            (fun _ => (1 : ℝ)) | m]) ω) := by
      intro y _
      have h := hLaw ((sf n) ⁻¹' {y}) ((sf n).measurableSet_fiber y)
      have h2 : ∀ᵐ ω ∂P, (ν ω).real ((sf n) ⁻¹' {y})
          = (P[(X ⁻¹' ((sf n) ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) | m]) ω := by
        filter_upwards [h] with ω hω
        simpa [Measure.real_def] using hω.symm
      filter_upwards [h2] with ω hω
      rw [hω]
    have hsum_eq : ∀ (t : Finset ℝ) (v w : ℝ → Ω → ℝ), (∀ y ∈ t, v y =ᵐ[P] w y) →
        (fun ω => ∑ y ∈ t, v y ω) =ᵐ[P] (fun ω => ∑ y ∈ t, w y ω) := by
      intro t v w hv
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hv a (Finset.mem_insert_self a t)).add
          (ih fun y hy => hv y (Finset.mem_insert_of_mem hy))
    rw [funext hper]
    exact hsum_eq _ _ _ hterm
  set G' : Ω → ℝ := fun ω => limsup (fun n => G n ω) atTop with hG'
  have hG'_meas : Measurable[m] G' := by
    rw [hG']; exact Measurable.limsup hG_meas
  have hg_eq_limsup : (fun ω => ∫ x, f x ∂(ν ω)) =ᵐ[P] G' := by
    filter_upwards [ae_all_iff.mpr hG_eq] with ω hω
    refine (Tendsto.limsup_eq ?_).symm
    rw [← funext hω]
    exact hconv ω
  have hgm : AEStronglyMeasurable[m] (fun ω => ∫ x, f x ∂(ν ω)) P :=
    ⟨G', hG'_meas.stronglyMeasurable, hg_eq_limsup⟩
  have hgn : ∀ n, AEStronglyMeasurable[m] (fun ω => ∫ x, sf n x ∂(ν ω)) P :=
    fun n => ⟨G n, (hG_meas n).stronglyMeasurable, hG_eq n⟩
  -- ### Step 4: the identity for simple functions
  have hId_simple : ∀ (s : SimpleFunc E ℝ) (t : Set Ω), MeasurableSet[m] t → P t < ∞ →
      ∫ ω in t, (∫ x, s x ∂(ν ω)) ∂P = ∫ ω in t, s (X ω) ∂P := by
    intro s t ht htfin
    haveI htfin' : IsFiniteMeasure (P.restrict t) := ⟨by simpa using htfin⟩
    have hper : ∀ ω, ∫ x, s x ∂(ν ω) = ∑ y ∈ s.range, y * (ν ω).real (s ⁻¹' {y}) := by
      intro ω
      haveI := hν ω
      rw [SimpleFunc.integral_eq_sum _ (simpleFunc_integrable_of_isProbabilityMeasure (ν ω) s)]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_eq_mul, mul_comm]
    have hterm2 : ∀ y ∈ s.range,
        ∫ ω in t, (X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) ω ∂P
          = P.real (t ∩ X ⁻¹' (s ⁻¹' {y})) := by
      intro y _
      have hmeas : MeasurableSet (s ⁻¹' {y}) := s.measurableSet_fiber y
      rw [setIntegral_indicator (f := fun _ => (1 : ℝ)) (hpre _ hmeas), setIntegral_const]
      simp
    have hterm : ∀ y ∈ s.range,
        ∫ ω in t, (ν ω).real (s ⁻¹' {y}) ∂P = P.real (t ∩ X ⁻¹' (s ⁻¹' {y})) := by
      intro y hy
      have hmeas : MeasurableSet (s ⁻¹' {y}) := s.measurableSet_fiber y
      have h1 : ∫ ω in t, (ν ω).real (s ⁻¹' {y}) ∂P
          = ∫ ω in t, (P[(X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) | m]) ω ∂P := by
        refine setIntegral_congr_ae (hm t ht) ?_
        filter_upwards [hLaw (s ⁻¹' {y}) hmeas] with ω hω _
        simpa [Measure.real_def] using hω.symm
      have h2 : ∫ ω in t, (P[(X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) | m]) ω ∂P
          = ∫ ω in t, (X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) ω ∂P := by
        refine setIntegral_condExp hm ?_ ht
        exact Integrable.indicator (integrable_const 1) (hpre _ hmeas)
      rw [h1, h2, hterm2 y hy]
    have hint_term : ∀ y ∈ s.range, Integrable (fun ω => y * (ν ω).real (s ⁻¹' {y})) (P.restrict t) := by
      intro y _
      refine Integrable.of_bound ?_ |y| ?_
      · have h' : AEStronglyMeasurable[m] (fun ω => (ν ω).real (s ⁻¹' {y})) P := by
          refine ⟨(P[(X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) | m]),
            stronglyMeasurable_condExp, ?_⟩
          filter_upwards [hLaw (s ⁻¹' {y}) (s.measurableSet_fiber y)] with ω hω
          simpa [Measure.real_def] using hω.symm
        have h1 : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (fun ω => (ν ω).real (s ⁻¹' {y})) P :=
          h'.mono hm
        exact (h1.const_mul y).mono_measure Measure.restrict_le_self
      · filter_upwards with ω
        have h0 : 0 ≤ (ν ω).real (s ⁻¹' {y}) := measureReal_nonneg
        have h1 : (ν ω).real (s ⁻¹' {y}) ≤ 1 := by
          simpa using measureReal_mono (μ := ν ω) (Set.subset_univ _) (measure_ne_top (ν ω) Set.univ)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
        calc |y| * (ν ω).real (s ⁻¹' {y}) ≤ |y| * 1 := by gcongr
          _ = |y| := mul_one _
    have hL : ∫ ω in t, (∫ x, s x ∂(ν ω)) ∂P
        = ∑ y ∈ s.range, y * ∫ ω in t, (ν ω).real (s ⁻¹' {y}) ∂P := by
      simp_rw [hper]
      rw [integral_finsetSum (μ := P.restrict t)]
      · exact Finset.sum_congr rfl fun y hy => by rw [integral_const_mul]
      · intro y hy; exact hint_term y hy
    have hpt : ∀ x, s x = ∑ y ∈ s.range, y * (s ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) x := by
      intro x
      have hx : s x ∈ s.range := SimpleFunc.mem_range_self s x
      rw [Finset.sum_eq_single (s x)]
      · simp
      · intro y _ hy
        have hxy : x ∉ s ⁻¹' {y} := by
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact fun h => hy h.symm
        simp [hxy]
      · intro h; exact absurd hx h
    have hR : ∫ ω in t, s (X ω) ∂P
        = ∑ y ∈ s.range, y * ∫ ω in t, (X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      have hpt2 : ∀ ω, s (X ω) = ∑ y ∈ s.range, y *
          (X ⁻¹' (s ⁻¹' {y})).indicator (fun _ => (1 : ℝ)) ω := by
        intro ω
        rw [hpt (X ω)]
        exact Finset.sum_congr rfl fun y _ => rfl
      simp_rw [hpt2]
      rw [integral_finsetSum (μ := P.restrict t)]
      · exact Finset.sum_congr rfl fun y hy => by rw [integral_const_mul]
      · intro y _
        exact Integrable.const_mul
          (Integrable.indicator (integrable_const 1) (hpre _ (s.measurableSet_fiber y))) y
    rw [hL, hR]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hterm y hy, hterm2 y hy]
  -- ### Step 5: extend to f
  have hId : ∀ t : Set Ω, MeasurableSet[m] t → P t < ∞ →
      ∫ ω in t, (∫ x, f x ∂(ν ω)) ∂P = ∫ ω in t, f (X ω) ∂P := by
    intro t ht htfin
    haveI htfin' : IsFiniteMeasure (P.restrict t) := ⟨by simpa using htfin⟩
    have hL : Tendsto (fun n => ∫ ω in t, (∫ x, sf n x ∂(ν ω)) ∂P) atTop
        (𝓝 (∫ ω in t, (∫ x, f x ∂(ν ω)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (μ := P.restrict t)
        (F := fun n ω => ∫ x, sf n x ∂(ν ω)) (f := fun ω => ∫ x, f x ∂(ν ω)) (fun _ => C) ?_ ?_ ?_ ?_
      · intro n
        exact ((hgn n).mono hm).mono_measure Measure.restrict_le_self
      · exact integrable_const C
      · intro n
        filter_upwards with ω
        refine (norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq ?_
        · filter_upwards with x using hsf_norm n x
        · rw [probReal_univ, mul_one]
      · filter_upwards with ω using hconv ω
    have hR : Tendsto (fun n => ∫ ω in t, sf n (X ω) ∂P) atTop
        (𝓝 (∫ ω in t, f (X ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (μ := P.restrict t)
        (F := fun n ω => sf n (X ω)) (f := fun ω => f (X ω)) (fun _ => C) ?_ ?_ ?_ ?_
      · intro n
        exact ((sf n).measurable.comp hXa).aestronglyMeasurable
      · exact integrable_const C
      · intro n
        filter_upwards with ω using hsf_norm n (X ω)
      · filter_upwards [ae_restrict_of_ae hae_bound] with ω hω
        refine SimpleFunc.tendsto_approxOn hf h0mem (x := X ω) (subset_closure ?_)
        rw [Set.mem_Icc]
        exact abs_le.mp (by simpa [Real.norm_eq_abs] using hω)
    have heq : ∀ n, ∫ ω in t, (∫ x, sf n x ∂(ν ω)) ∂P = ∫ ω in t, sf n (X ω) ∂P :=
      fun n => hId_simple (sf n) t ht htfin
    rw [← tendsto_nhds_unique (by simpa only [heq] using hL) hR]
  -- ### Step 6: integrability and uniqueness
  have hInt_g : Integrable (fun ω => ∫ x, f x ∂(ν ω)) P := by
    refine Integrable.of_bound (hgm.mono hm) C ?_
    filter_upwards with ω
    have hb : ∀ n, ‖∫ x, sf n x ∂(ν ω)‖ ≤ C := by
      intro n
      refine (norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq ?_
      · filter_upwards with x using hsf_norm n x
      · rw [probReal_univ, mul_one]
    exact le_of_tendsto (hconv ω).norm (Eventually.of_forall hb)
  refine ⟨hInt_fX, ?_⟩
  have hmain := ae_eq_condExp_of_forall_setIntegral_eq (μ := P) (m := m) hm hInt_fX
    (fun t ht _ => (hInt_g.mono_measure Measure.restrict_le_self))
    (fun t ht htfin => hId t ht htfin) hgm
  exact hmain.symm
