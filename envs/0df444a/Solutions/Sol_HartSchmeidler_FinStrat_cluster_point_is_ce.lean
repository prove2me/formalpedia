-- Prove2me | solution 1 for HartSchmeidler.FinStrat.cluster_point_is_ce
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:24:30.707773+00:00
-- url     : https://prove2.me/submissions/44095fa9-b93e-4307-935f-beaf66a71c35

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

/-- continuous test function for the equilibrium condition -/
lemma cont_test [DecidableEq ι] [∀ i, DecidableEq (S i)] (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (i : ι) (r t : S i) :
    Continuous (fun s : (∀ i, S i) => (if s i = r then (1:ℝ) else 0) * (h i s - h i (Function.update s i t))) := by
  have he : Continuous (fun s : (∀ i, S i) => if s i = r then (1:ℝ) else 0) :=
    (continuous_of_discreteTopology (f := fun a : S i => if a = r then (1:ℝ) else 0)).comp
          (continuous_apply i)
  exact he.mul ((hh i).sub ((hh i).comp (continuous_id.update i continuous_const)))

end Meas


section CP

variable {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]

theorem cp_core
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (anchor : ∀ i, S i)
    (F : (∀ i, Finset (S i)) → Finset (∀ i, S i))
    (w : (∀ i, Finset (S i)) → (∀ i, S i) → ℝ)
    (hFw : ∀ T, IsAnchoredFSet anchor T → IsFSetCE h T (F T) (w T))
    (p : Measure (∀ i, S i)) (hp : IsProbabilityMeasure p)
    (hcluster : ∀ (f : C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet anchor T₀ →
        ∃ T, IsAnchoredFSet anchor T ∧ FSetLE T₀ T ∧
          |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε) :
    IsCorrelatedEq h p := by
  refine ⟨hp, fun i r t => ?_⟩
  let fC : C(∀ i, S i, ℝ) := ⟨_, cont_test h hh i r t⟩
  have hfC : ∀ s, fC s = ({s : ∀ i, S i | s i = r}.indicator (fun s => h i s - h i (Function.update s i t))) s := by
    intro s
    by_cases hs : s i = r <;> simp [fC, hs]
  have hmeasE : MeasurableSet {s : ∀ i, S i | s i = r} :=
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hint : Integrable fC p := by
    obtain ⟨C, hC⟩ := (isCompact_range fC.continuous).isBounded.exists_norm_le
    exact Integrable.of_bound (meas_of_cont fC).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun s => hC _ ⟨s, rfl⟩)
  have hfeq : (fC : (∀ i, S i) → ℝ) = {s : ∀ i, S i | s i = r}.indicator (fun s => h i s - h i (Function.update s i t)) :=
    funext hfC
  have hI : IntegrableOn (fun s => h i s - h i (Function.update s i t)) {s | s i = r} p := by
    rw [← integrable_indicator_iff hmeasE, ← hfeq]; exact hint
  refine ⟨hI, ?_⟩
  have hsetint : ∫ s in {s : ∀ i, S i | s i = r}, (h i s - h i (Function.update s i t)) ∂p = ∫ s, fC s ∂p := by
    rw [hfeq, integral_indicator hmeasE]
  rw [hsetint]
  let T₀ : ∀ j, Finset (S j) := Function.update (fun j => {anchor j}) i {anchor i, r, t}
  have hT₀ : IsAnchoredFSet anchor T₀ := by
    refine ⟨⟨fun j => ?_, ?_⟩, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj; simp [T₀]
      · simp [T₀, Function.update_of_ne hj]
    · apply (Set.finite_singleton i).subset
      intro j hj
      by_contra hne
      have : j ≠ i := hne
      exact hj ⟨anchor j, by simp [T₀, Function.update_of_ne this]⟩
    · by_cases hj : j = i
      · subst hj; simp [T₀]
      · simp [T₀, Function.update_of_ne hj]
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, hT, hle, hab⟩ := hcluster fC ε hε T₀ hT₀
  have hr : r ∈ T i := hle i (by simp [T₀])
  have ht : t ∈ T i := hle i (by simp [T₀])
  have hnn := (hFw T hT).2.2.2 i r t hr ht
  have hsum : ∑ s ∈ F T, w T s * fC s =
      ∑ s ∈ (F T).filter (fun s => s i = r), w T s * (h i s - h i (Function.update s i t)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s i = r <;> simp [fC, hs]
  rw [hsum] at hab
  have := (abs_lt.1 hab).1
  linarith

end CP

end HartSchmeidler.FinStrat

open HartSchmeidler.FinStrat
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (anchor : ∀ i, S i)
    (F : (∀ i, Finset (S i)) → Finset (∀ i, S i))
    (w : (∀ i, Finset (S i)) → (∀ i, S i) → ℝ)
    (hFw : ∀ T, IsAnchoredFSet anchor T → IsFSetCE h T (F T) (w T))
    (p : Measure (∀ i, S i)) (hp : IsProbabilityMeasure p)
    (hcluster : ∀ (f : C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet anchor T₀ →
        ∃ T, IsAnchoredFSet anchor T ∧ FSetLE T₀ T ∧
          |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε) :
    IsCorrelatedEq h p := by
  exact cp_core h hh anchor F w hFw p hp hcluster
