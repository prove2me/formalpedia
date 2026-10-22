-- Prove2me | solution 1 for NatureSLT.Consistency.finite_class_lln
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:39:00.627402+00:00
-- url     : https://prove2.me/submissions/829568cf-9aa4-437a-83b7-51b0fe215a7d

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk
import Definitions.Def_NatureSLT_Consistency_uniformConvergence

open MeasureTheory Filter Topology
open NatureSLT.Consistency ProbabilityTheory

lemma g71m_wlln_meas {Z : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (g : Z → ℝ) (hg : Measurable g) (hint : Integrable g F) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | ε < |∫ x, g x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g (z i)|}) atTop (𝓝 0) := by
  set P : Measure (ℕ → Z) := Measure.infinitePi (fun _ : ℕ => F) with hP
  set X : ℕ → (ℕ → Z) → ℝ := fun i ω => g (ω i) with hX
  have hXm : ∀ i, Measurable (X i) := fun i => hg.comp (measurable_pi_apply i)
  have hind : iIndepFun X P := iIndepFun_infinitePi (P := fun _ : ℕ => F)
    (X := fun _ => g) (fun _ => hg)
  have hmapX : ∀ i, P.map (X i) = F.map g := by
    intro i
    have : X i = g ∘ (fun ω : ℕ → Z => ω i) := rfl
    rw [this, ← Measure.map_map hg (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hint0 : Integrable (X 0) P := by
    have hmp : MeasurePreserving (fun ω : ℕ → Z => ω 0) P F :=
      measurePreserving_eval_infinitePi _ 0
    exact hmp.integrable_comp_of_integrable hint
  have hE : ∫ ω, X 0 ω ∂P = ∫ x, g x ∂F := by
    have h0 : P.map (fun ω : ℕ → Z => ω 0) = F := Measure.infinitePi_map_eval _ 0
    conv_rhs => rw [← h0]
    rw [integral_map (measurable_pi_apply 0).aemeasurable]
    rw [h0]; exact hint.aestronglyMeasurable
  have hslln := ProbabilityTheory.strong_law_ae X hint0
    (fun i j hij => hind.indepFun hij)
    (fun i => ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hmapX, hmapX]⟩)
  have htm := tendstoInMeasure_of_tendsto_ae (μ := P)
    (f := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) (g := fun _ => ∫ ω, X 0 ω ∂P)
    (fun n => Measurable.aestronglyMeasurable (by
      have := (Finset.measurable_sum (Finset.range n) (fun i _ => hXm i))
      exact this.const_smul ((n : ℝ)⁻¹)))
    hslln
  have h1 := htm (ENNReal.ofReal ε) (by simpa using hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) ?_
  intro ℓ
  -- law of the first ℓ coordinates
  have hlaw : P.map (fun ω (i : Fin ℓ) => ω (i : ℕ)) = Measure.pi (fun _ : Fin ℓ => F) := by
    have hind' : iIndepFun (fun (i : Fin ℓ) (ω : ℕ → Z) => ω (i : ℕ)) P := by
      have := iIndepFun_infinitePi (P := fun _ : ℕ => F) (X := fun _ => (id : Z → Z))
        (fun _ => measurable_id)
      exact this.precomp Fin.val_injective
    rw [hind'.map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)]
    congr 1
    funext i
    exact Measure.infinitePi_map_eval _ _
  have hmeasE : MeasurableSet
      {z : Fin ℓ → Z | ε < |∫ x, g x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g (z i)|} := by
    refine measurableSet_lt measurable_const ?_
    refine (measurable_const.sub (measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))))).abs
  dsimp only
  rw [← hlaw, Measure.map_apply (measurable_pi_lambda _ (fun i => measurable_pi_apply _)) hmeasE]
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
  rw [hE, edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs : ∑ i : Fin ℓ, g (ω (i : ℕ)) = ∑ i ∈ Finset.range ℓ, X i ω :=
    Fin.sum_univ_eq_sum_range (fun i => g (ω i)) ℓ
  rw [hs, abs_sub_comm] at hω
  rw [smul_eq_mul, ← one_div]
  exact hω.le

lemma g71m_wlln {Z : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (g : Z → ℝ) (hint : Integrable g F) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun ℓ : ℕ => Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | ε < |∫ x, g x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g (z i)|}) atTop (𝓝 0) := by
  set g' := hint.aestronglyMeasurable.mk g with hg'
  have hg'm : Measurable g' := hint.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : g =ᵐ[F] g' := hint.aestronglyMeasurable.ae_eq_mk
  have hint' : Integrable g' F := hint.congr hae
  have hI : ∫ x, g x ∂F = ∫ x, g' x ∂F := integral_congr_ae hae
  have hlim := g71m_wlln_meas F g' hg'm hint' ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) ?_
  intro ℓ
  have hnull : Measure.pi (fun _ : Fin ℓ => F)
      (⋃ i : Fin ℓ, Function.eval i ⁻¹' {x | ¬ g x = g' x}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    exact Measure.pi_eval_preimage_null _ (ae_iff.mp hae)
  dsimp only
  calc Measure.pi (fun _ : Fin ℓ => F)
        {z : Fin ℓ → Z | ε < |∫ x, g x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g (z i)|}
      ≤ Measure.pi (fun _ : Fin ℓ => F)
        ({z : Fin ℓ → Z | ε < |∫ x, g' x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g' (z i)|} ∪
          ⋃ i : Fin ℓ, Function.eval i ⁻¹' {x | ¬ g x = g' x}) := by
        refine measure_mono ?_
        intro z hz
        by_cases h : ∀ i, g (z i) = g' (z i)
        · left
          simp only [Set.mem_ofPred_eq] at hz ⊢
          rw [← hI]
          simpa only [h] using hz
        · right
          push Not at h
          obtain ⟨i, hi⟩ := h
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
    _ ≤ _ := by
        refine (measure_union_le _ _).trans ?_
        rw [hnull, add_zero]

theorem solution {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hfin : (Set.range Q).Finite)
    (hint : ∀ α, Integrable (Q α) F) :
    UniformTwoSidedConvergence F Q := by
  intro ε hε
  classical
  set S := hfin.toFinset with hS
  have hSint : ∀ g ∈ S, Integrable g F := by
    intro g hg
    rw [hS, Set.Finite.mem_toFinset] at hg
    obtain ⟨α, rfl⟩ := hg
    exact hint α
  have hsum : Tendsto (fun ℓ : ℕ => ∑ g ∈ S, Measure.pi (fun _ : Fin ℓ => F)
      {z : Fin ℓ → Z | ε < |∫ x, g x ∂F - (1 / (ℓ : ℝ)) * ∑ i, g (z i)|}) atTop (𝓝 0) := by
    rw [show (0 : ENNReal) = ∑ g ∈ S, (0 : ENNReal) by simp]
    exact tendsto_finsetSum _ fun g hg => g71m_wlln F g (hSint g hg) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro ℓ
  refine (measure_mono ?_).trans (measure_biUnion_finset_le S _)
  intro z hz
  simp only [Set.mem_ofPred_eq, supTwoSidedDeviation] at hz
  obtain ⟨α, hα⟩ := lt_iSup_iff.mp hz
  rw [EReal.coe_lt_coe_iff] at hα
  refine Set.mem_iUnion₂.mpr ⟨Q α, ?_, ?_⟩
  · rw [hS, Set.Finite.mem_toFinset]; exact ⟨α, rfl⟩
  · simpa [risk, empiricalRisk] using hα
