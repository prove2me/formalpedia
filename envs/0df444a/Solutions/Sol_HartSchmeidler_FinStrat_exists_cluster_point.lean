-- Prove2me | solution 1 for HartSchmeidler.FinStrat.exists_cluster_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:28:20.16231+00:00
-- url     : https://prove2.me/submissions/80aae5e5-8a09-46d4-b649-e23536966617

import Definitions.Def_HartSchmeidler_FinStrat_Game



namespace HartSchmeidler.FinStrat

open MeasureTheory

section Meas

variable {ι : Type*} {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

open Classical in
/-- Continuous functions depending on finitely many coordinates. -/
noncomputable def cylAlg : Subalgebra ℝ C(∀ i, S i, ℝ) where
  carrier := {f | ∃ J : Finset ι, ∀ x y : (∀ i, S i), (∀ j ∈ J, x j = y j) → f x = f y}
  mul_mem' := by
    rintro f g ⟨J, hJ⟩ ⟨K, hK⟩
    refine ⟨J ∪ K, fun x y hxy => ?_⟩
    simp only [ContinuousMap.mul_apply]
    rw [hJ x y (fun j hj => hxy j (Finset.mem_union_left _ hj)),
      hK x y (fun j hj => hxy j (Finset.mem_union_right _ hj))]
  add_mem' := by
    rintro f g ⟨J, hJ⟩ ⟨K, hK⟩
    refine ⟨J ∪ K, fun x y hxy => ?_⟩
    simp only [ContinuousMap.add_apply]
    rw [hJ x y (fun j hj => hxy j (Finset.mem_union_left _ hj)),
      hK x y (fun j hj => hxy j (Finset.mem_union_right _ hj))]
  algebraMap_mem' := by
    intro r
    exact ⟨∅, fun x y _ => rfl⟩

open Classical in
lemma cylAlg_measurable (f : C(∀ i, S i, ℝ)) (hf : f ∈ (cylAlg (S := S))) : Measurable f := by
  obtain ⟨J, hJ⟩ := hf
  let d : ∀ i, S i := fun i => Classical.arbitrary (S i)
  let ext : (∀ j : J, S j) → (∀ i, S i) := fun y j => if h : j ∈ J then y ⟨j, h⟩ else d j
  have hg : Measurable (fun y : (∀ j : J, S j) => f (ext y)) := measurable_of_countable _
  have hπ : Measurable (fun (x : ∀ i, S i) (j : J) => x j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have : (f : (∀ i, S i) → ℝ) = (fun y : (∀ j : J, S j) => f (ext y)) ∘ (fun (x : ∀ i, S i) (j : J) => x j) := by
    funext x
    simp only [Function.comp]
    apply hJ
    intro j hj
    simp [ext, hj]
  rw [this]
  exact hg.comp hπ

theorem meas_of_cont (f : C(∀ i, S i, ℝ)) : Measurable f := by
  classical
  have hsep : (cylAlg (S := S)).SeparatesPoints := by
    intro x y hxy
    have : ∃ j, x j ≠ y j := by
      by_contra h; push_neg at h; exact hxy (funext h)
    obtain ⟨j, hj⟩ := this
    let e : C(∀ i, S i, ℝ) :=
      ⟨fun z => if z j = x j then 1 else 0,
        (continuous_of_discreteTopology (f := fun a : S j => if a = x j then (1:ℝ) else 0)).comp
          (continuous_apply j)⟩
    refine ⟨e, ⟨e, ⟨{j}, fun a b hab => ?_⟩, rfl⟩, ?_⟩
    · have := hab j (by simp)
      simp [e, this]
    · simp [e, hj.symm]
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hf0 : f ∈ (cylAlg (S := S)).topologicalClosure := by rw [htop]; trivial
  have hf : f ∈ closure ((cylAlg (S := S) : Subalgebra ℝ C(∀ i, S i, ℝ)) : Set C(∀ i, S i, ℝ)) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hf0; exact hf0
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  refine measurable_of_tendsto_metrizable (f := fun n => (u n : (∀ i, S i) → ℝ))
    (fun n => cylAlg_measurable _ (hu n)) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact ((continuous_eval_const x).tendsto f).comp hlim

end Meas


section Riesz

open CompactlySupported in
lemma riesz_gen {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [m : MeasurableSpace X]
    [BorelSpace X] (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) (h1 : L 1 = 1) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂ν = L f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀
      { toFun := fun g => L ⟨g, g.continuous⟩
        map_add' := fun g g' => by
          rw [← map_add]; congr 1
        map_smul' := fun c g => by
          simp only [RingHom.id_apply]
          rw [← map_smul]; congr 1 }
      (fun g hg => hpos _ (fun x => hg x))
  have hint : ∀ f : C(X, ℝ), ∫ x, f x ∂(RealRMK.rieszMeasure Λ) = L f := by
    intro f
    have := RealRMK.integral_rieszMeasure Λ ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact this.trans rfl
  refine ⟨RealRMK.rieszMeasure Λ, ⟨?_⟩, hint⟩
  have h := hint 1
  rw [h1] at h
  simp at h
  have hf : IsFiniteMeasure (RealRMK.rieszMeasure Λ) := inferInstance
  have : (RealRMK.rieszMeasure Λ).real Set.univ = 1 := by simpa using h
  rw [measureReal_def] at this
  rwa [← ENNReal.toReal_eq_one_iff]

end Riesz


section Cluster

variable {ι : Type*} [Nonempty ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

lemma integrable_cont (μ : Measure (∀ i, S i)) [IsFiniteMeasure μ] (f : C(∀ i, S i, ℝ)) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
  exact Integrable.of_bound (meas_of_cont f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun s => hC _ ⟨s, rfl⟩)

lemma pi_le_borel : (MeasurableSpace.pi : MeasurableSpace (∀ i, S i)) ≤ borel (∀ i, S i) := by
  refine iSup_le fun i => ?_
  have : @Measurable (∀ i, S i) (S i) (borel _) _ (fun b => b i) := by
    letI : MeasurableSpace (∀ i, S i) := borel _
    haveI : OpensMeasurableSpace (∀ i, S i) := ⟨le_rfl⟩
    intro s _
    exact ((isOpen_discrete s).preimage (continuous_apply i)).measurableSet
  exact this.comap_le

theorem ecp_core {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure (∀ i, S i)) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure (∀ i, S i), IsProbabilityMeasure p ∧
      ∀ (fs : Finset C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d : D, d₀ ≤ d ∧ ∀ f ∈ fs, |∫ s, f s ∂p - ∫ s, f s ∂(q d)| < ε := by
  classical
  haveI : ∀ d, IsProbabilityMeasure (q d) := hq
  let 𝒰 : Ultrafilter D := Ultrafilter.of Filter.atTop
  have h𝒰 : (𝒰 : Filter D) ≤ Filter.atTop := Ultrafilter.of_le _
  have hbd : ∀ (f : C(∀ i, S i, ℝ)) d, ∫ s, f s ∂(q d) ∈ Set.Icc (-‖f‖) ‖f‖ := by
    intro f d
    have h := norm_integral_le_of_norm_le_const (μ := q d) (f := fun s => f s) (C := ‖f‖)
      (Filter.Eventually.of_forall fun s => ContinuousMap.norm_coe_le_norm f s)
    simp only [probReal_univ, mul_one] at h
    exact abs_le.1 (by simpa using h)
  have hlim : ∀ f : C(∀ i, S i, ℝ), ∃ x, Filter.Tendsto (fun d => ∫ s, f s ∂(q d)) (𝒰 : Filter D) (nhds x) := by
    intro f
    obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := -‖f‖) (b := ‖f‖)).ultrafilter_le_nhds
      (𝒰.map (fun d => ∫ s, f s ∂(q d)))
      (by
        rw [Ultrafilter.coe_map, Filter.le_principal_iff]
        exact Filter.mem_map.2 (Filter.Eventually.of_forall (fun d => hbd f d)))
    exact ⟨x, hx⟩
  choose a ha using hlim
  have hadd : ∀ f g : C(∀ i, S i, ℝ), a (f + g) = a f + a g := by
    intro f g
    have h2 : (fun d => ∫ s, (f + g) s ∂(q d)) = fun d => ∫ s, f s ∂(q d) + ∫ s, g s ∂(q d) := by
      funext d
      simp only [ContinuousMap.add_apply]
      exact integral_add (integrable_cont _ f) (integrable_cont _ g)
    have h3 := (ha f).add (ha g)
    have h4 := ha (f + g)
    rw [h2] at h4
    exact tendsto_nhds_unique h4 h3
  have hsmul : ∀ (c : ℝ) (f : C(∀ i, S i, ℝ)), a (c • f) = c * a f := by
    intro c f
    have h2 : (fun d => ∫ s, (c • f) s ∂(q d)) = fun d => c * ∫ s, f s ∂(q d) := by
      funext d
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    have h3 := (ha f).const_mul c
    have h4 := ha (c • f)
    rw [h2] at h4
    exact tendsto_nhds_unique h4 h3
  have hpos : ∀ f : C(∀ i, S i, ℝ), 0 ≤ f → 0 ≤ a f := fun f hf =>
    ge_of_tendsto' (ha f) fun d => integral_nonneg fun s => hf s
  have hone : a 1 = 1 := by
    have h4 := ha 1
    have h2 : (fun d => ∫ s, (1 : C(∀ i, S i, ℝ)) s ∂(q d)) = fun _ => (1:ℝ) := by
      funext d; simp
    rw [h2] at h4
    exact tendsto_nhds_unique h4 tendsto_const_nhds
  let L : C(∀ i, S i, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a, map_add' := hadd, map_smul' := fun c f => by simpa using hsmul c f }
  obtain ⟨ν, hν, hνint⟩ := @riesz_gen (∀ i, S i) _ _ _ (borel _) (@BorelSpace.mk _ _ (borel _) rfl) L hpos hone
  have hint : ∀ f : C(∀ i, S i, ℝ), ∫ s, f s ∂(ν.trim pi_le_borel) = a f := by
    intro f
    have h := integral_trim (μ := ν) pi_le_borel (meas_of_cont f).stronglyMeasurable
    exact h.symm.trans (hνint f)
  refine ⟨ν.trim pi_le_borel, ⟨?_⟩, ?_⟩
  · rw [trim_measurableSet_eq pi_le_borel MeasurableSet.univ]
    exact hν.measure_univ
  · intro fs ε hε d₀
    have hev : ∀ f : C(∀ i, S i, ℝ), ∀ᶠ d in (𝒰 : Filter D), |∫ s, f s ∂(ν.trim pi_le_borel) - ∫ s, f s ∂(q d)| < ε := by
      intro f
      have := Metric.tendsto_nhds.1 (ha f) ε hε
      refine this.mono fun d hd => ?_
      rw [Real.dist_eq, abs_sub_comm] at hd
      rw [hint f]
      exact hd
    have hall : ∀ᶠ d in (𝒰 : Filter D), ∀ f ∈ fs, |∫ s, f s ∂(ν.trim pi_le_borel) - ∫ s, f s ∂(q d)| < ε :=
      (Filter.eventually_all_finset fs).2 fun f _ => hev f
    have hge : ∀ᶠ d in (𝒰 : Filter D), d₀ ≤ d := h𝒰 (Filter.eventually_ge_atTop d₀)
    obtain ⟨d, hd1, hd2⟩ := (hall.and hge).exists
    exact ⟨d, hd2, hd1⟩

end Cluster

end HartSchmeidler.FinStrat

open HartSchmeidler.FinStrat
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure (∀ i, S i)) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure (∀ i, S i), IsProbabilityMeasure p ∧
      ∀ (fs : Finset C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d : D, d₀ ≤ d ∧
          ∀ f ∈ fs, |∫ s, f s ∂p - ∫ s, f s ∂(q d)| < ε := by
  exact ecp_core q hq
