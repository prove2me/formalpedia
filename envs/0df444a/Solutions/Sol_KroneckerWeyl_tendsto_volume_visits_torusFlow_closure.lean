-- Prove2me | solution 1 for KroneckerWeyl.tendsto_volume_visits_torusFlow_closure
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:55:05.215008+00:00
-- url     : https://prove2.me/submissions/5531ae5b-c561-48ab-bf60-a6388abf68f0

import Mathlib
import Theorems.Thm_KroneckerWeyl_tendsto_average_torusFlow_closure

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Sol_KroneckerWeyl_tendsto_volume_visits_torusFlow_closure

/-- Squeeze lemma: if the time averages of every continuous function over the windows
`[l T, r T]` converge to the `μ`-integral over `G`, then the proportion of time in `[l T, r T]`
spent in a set `U` whose trace on `G` has `μ`-null relative boundary converges to `μ (U ∩ G)`. -/
theorem visits_of_average {ι : Type*} [Fintype ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [IsProbabilityMeasure μ]
    (l r : ℝ → ℝ) (hlr : ∀ᶠ T in atTop, l T < r T)
    (havg : ∀ u : C(UnitAddTorus ι, ℂ), Tendsto (fun T : ℝ => (r T - l T)⁻¹ •
        ∫ t in (l T)..(r T), u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)))
    (U : Set (UnitAddTorus ι))
    (h0 : μ (frontier (Subtype.val ⁻¹' U : Set G)) = 0) :
    Tendsto (fun T : ℝ =>
          (volume {t : ℝ | t ∈ Set.Icc (l T) (r T) ∧
            (fun k => ((t * τ k : ℝ) : UnitAddCircle)) ∈ U}).toReal / (r T - l T))
        atTop (𝓝 (μ (Subtype.val ⁻¹' U : Set G)).toReal) := by
  set flow : ℝ → UnitAddTorus ι := fun t k => ((t * τ k : ℝ) : UnitAddCircle) with hflow
  have hflow_cont : Continuous flow := by
    rw [hflow]
    fun_prop
  have hmem : ∀ t, flow t ∈ G := fun t => by
    rw [← SetLike.mem_coe, hG]
    exact subset_closure (Set.mem_range_self t)
  let γ : ℝ → G := fun t => ⟨flow t, hmem t⟩
  have hγ : Continuous γ := hflow_cont.subtype_mk hmem
  have hγm : Measurable γ := hγ.measurable
  -- the empirical measures
  let ν : ℝ → Measure G := fun T =>
    (ENNReal.ofReal (r T - l T))⁻¹ • (volume.restrict (Set.Icc (l T) (r T))).map γ
  have hν_apply : ∀ T, ∀ s : Set G, MeasurableSet s →
      ν T s = (ENNReal.ofReal (r T - l T))⁻¹ *
        volume {t : ℝ | t ∈ Set.Icc (l T) (r T) ∧ γ t ∈ s} := by
    intro T s hs
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.map_apply hγm hs,
      Measure.restrict_apply (hγm hs)]
    congr 2
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_comm
  have hν_prob : ∀ T, l T < r T → IsProbabilityMeasure (ν T) := by
    intro T hT
    constructor
    rw [hν_apply T _ MeasurableSet.univ]
    simp only [Set.mem_univ, and_true, Set.ofPred_mem_eq, Real.volume_Icc]
    exact ENNReal.inv_mul_cancel (by simpa using hT) ENNReal.ofReal_ne_top
  let μP : ProbabilityMeasure G := ⟨μ, inferInstance⟩
  let νP : ℝ → ProbabilityMeasure G := fun T =>
    if h : l T < r T then (⟨ν T, hν_prob T h⟩ : ProbabilityMeasure G) else μP
  have hνP : ∀ T, l T < r T → (νP T : Measure G) = ν T := by
    intro T hT
    have hT' : νP T = (⟨ν T, hν_prob T hT⟩ : ProbabilityMeasure G) := dif_pos hT
    rw [hT']
    rfl
  -- weak convergence of the empirical measures
  have hlim : Tendsto νP atTop (𝓝 μP) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hGc : IsClosed (G : Set (UnitAddTorus ι)) := by
      rw [hG]
      exact isClosed_closure
    obtain ⟨g, hg⟩ :=
      ContinuousMap.exists_extension hGc.isClosedEmbedding_subtypeVal (f : C(G, ℝ))
    have hgf : ∀ x : G, g (x : UnitAddTorus ι) = f x := fun x =>
      DFunLike.congr_fun hg x
    let u : C(UnitAddTorus ι, ℂ) := (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp g
    have hu : ∀ x, u x = ((g x : ℝ) : ℂ) := fun x => rfl
    have h1 := (Complex.continuous_re.tendsto _).comp (havg u)
    have hR : ∫ x : G, u (x : UnitAddTorus ι) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      ext x
      rw [hu, hgf]
    rw [hR, Complex.ofReal_re] at h1
    refine h1.congr' ?_
    filter_upwards [hlr] with T hT
    rw [Function.comp_apply, hνP T hT]
    simp only [hu]
    rw [intervalIntegral.integral_ofReal, Complex.real_smul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [ν]
    rw [integral_smul_measure, integral_map hγm.aemeasurable f.continuous.aestronglyMeasurable,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hT.le), smul_eq_mul,
      intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact hgf (γ t)
  -- portmanteau for the interior and the closure
  set U' : Set G := Subtype.val ⁻¹' U with hU'
  have hA := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim
    (E := interior U') (by
      change μ _ = 0
      exact measure_mono_null frontier_interior_subset h0)
  have hF := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim
    (E := closure U') (by
      change μ _ = 0
      exact measure_mono_null frontier_closure_subset h0)
  change Tendsto _ _ (𝓝 (μ (interior U'))) at hA
  change Tendsto _ _ (𝓝 (μ (closure U'))) at hF
  have hcl : μ (closure U') ≤ μ (interior U') :=
    calc μ (closure U') ≤ μ (interior U' ∪ frontier U') := by
          refine measure_mono ?_
          rw [frontier, Set.union_sdiff_self]
          exact Set.subset_union_right
      _ ≤ μ (interior U') + μ (frontier U') := measure_union_le _ _
      _ = μ (interior U') := by rw [h0, add_zero]
  have hAU : μ (interior U') = μ U' :=
    le_antisymm (measure_mono interior_subset)
      ((measure_mono subset_closure).trans hcl)
  have hFU : μ (closure U') = μ U' :=
    le_antisymm (hcl.trans (measure_mono interior_subset)) (measure_mono subset_closure)
  have hA' := (ENNReal.tendsto_toReal (measure_ne_top μ (interior U'))).comp hA
  have hF' := (ENNReal.tendsto_toReal (measure_ne_top μ (closure U'))).comp hF
  rw [hAU] at hA'
  rw [hFU] at hF'
  -- the empirical measure of a Borel set is the proportion of visiting times
  have hreal : ∀ T, l T < r T → ∀ s : Set G, MeasurableSet s →
      ((νP T : Measure G) s).toReal =
        (volume {t : ℝ | t ∈ Set.Icc (l T) (r T) ∧ γ t ∈ s}).toReal / (r T - l T) := by
    intro T hT s hs
    rw [hνP T hT, hν_apply T s hs, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hT.le), div_eq_inv_mul]
  have hfin : ∀ T, ∀ S : Set ℝ, S ⊆ Set.Icc (l T) (r T) → volume S ≠ ⊤ := fun T S hS =>
    ((measure_mono hS).trans_lt measure_Icc_lt_top).ne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA' hF' ?_ ?_
  · filter_upwards [hlr] with T hT
    rw [Function.comp_apply, hreal T hT _ isOpen_interior.measurableSet]
    have hpos : 0 < r T - l T := sub_pos.mpr hT
    refine div_le_div_of_nonneg_right ?_ hpos.le
    refine ENNReal.toReal_mono (hfin T _ fun t ht => ht.1) (measure_mono ?_)
    rintro t ⟨ht1, ht2⟩
    exact ⟨ht1, interior_subset (s := U') ht2⟩
  · filter_upwards [hlr] with T hT
    rw [Function.comp_apply, hreal T hT _ isClosed_closure.measurableSet]
    have hpos : 0 < r T - l T := sub_pos.mpr hT
    refine div_le_div_of_nonneg_right ?_ hpos.le
    refine ENNReal.toReal_mono (hfin T _ fun t ht => ht.1) (measure_mono ?_)
    rintro t ⟨ht1, ht2⟩
    exact ⟨ht1, subset_closure (s := U') ht2⟩

end Sol_KroneckerWeyl_tendsto_volume_visits_torusFlow_closure

open Sol_KroneckerWeyl_tendsto_volume_visits_torusFlow_closure

theorem solution {ι : Type*} [Finite ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (UnitAddTorus ι))
    (h0 : μ (frontier (Subtype.val ⁻¹' U : Set G)) = 0) :
    Tendsto
        (fun T : ℝ =>
          (volume {t : ℝ | t ∈ Set.Icc 0 T ∧
            (fun k => ((t * τ k : ℝ) : UnitAddCircle)) ∈ U}).toReal / T)
        atTop (𝓝 (μ (Subtype.val ⁻¹' U : Set G)).toReal) ∧
      Tendsto
        (fun T : ℝ =>
          (volume {t : ℝ | t ∈ Set.Icc (-T) T ∧
            (fun k => ((t * τ k : ℝ) : UnitAddCircle)) ∈ U}).toReal / (2 * T))
        atTop (𝓝 (μ (Subtype.val ⁻¹' U : Set G)).toReal) := by
  cases nonempty_fintype ι
  have h := KroneckerWeyl.tendsto_average_torusFlow_closure τ G hG μ
  constructor
  · have key := visits_of_average τ G hG μ (fun _ => 0) (fun T => T) (eventually_gt_atTop 0)
      (fun u => by simpa only [sub_zero] using (h u).1) U h0
    simpa only [sub_zero] using key
  · have e : ∀ T : ℝ, T - -T = 2 * T := fun T => by ring
    have key := visits_of_average τ G hG μ (fun T => -T) (fun T => T)
      ((eventually_gt_atTop 0).mono fun T hT => by linarith)
      (fun u => by simpa only [e] using (h u).2) U h0
    simpa only [e] using key
