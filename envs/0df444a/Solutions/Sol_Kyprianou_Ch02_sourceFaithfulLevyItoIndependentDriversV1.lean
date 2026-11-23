-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:02:11.553808+00:00
-- url     : https://prove2.me/submissions/bae07634-0f1d-411a-88c5-cb3981706f01

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace IndependentDriversHelpers

private lemma indep_comap_fst
    {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {n₁ n₂ : MeasurableSpace Ω₁} (h : Indep n₁ n₂ P₁) :
    Indep (n₁.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁))
      (n₂.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁)) (@Measure.prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂) := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  rcases hs with ⟨s', hs', rfl⟩
  rcases ht with ⟨t', ht', rfl⟩
  have h1 : (Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' s' = s' ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h2 : (Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' t' = t' ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h12 : ((Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' s') ∩ ((Prod.fst : Ω₁ × Ω₂ → Ω₁) ⁻¹' t') =
      (s' ∩ t') ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    measure_univ, mul_one, mul_one, mul_one, h s' t' hs' ht']

private lemma indep_comap_snd
    {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {n₁ n₂ : MeasurableSpace Ω₂} (h : Indep n₁ n₂ P₂) :
    Indep (n₁.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂))
      (n₂.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂)) (@Measure.prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂) := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  rcases hs with ⟨s', hs', rfl⟩
  rcases ht with ⟨t', ht', rfl⟩
  have h1 : (Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' s' = (Set.univ : Set Ω₁) ×ˢ s' := by
    ext ⟨a, b⟩; simp
  have h2 : (Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' t' = (Set.univ : Set Ω₁) ×ˢ t' := by
    ext ⟨a, b⟩; simp
  have h12 : ((Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' s') ∩ ((Prod.snd : Ω₁ × Ω₂ → Ω₂) ⁻¹' t') =
      (Set.univ : Set Ω₁) ×ˢ (s' ∩ t') := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    @Measure.prod_prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂ _,
    measure_univ, one_mul, one_mul, one_mul, h s' t' hs' ht']

private lemma indepFun_comp_fst_snd
    {Ω₁ Ω₂ β γ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace γ]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (f : Ω₁ → β) (g : Ω₂ → γ) :
    IndepFun (fun ω : Ω₁ × Ω₂ => f ω.1) (fun ω : Ω₁ × Ω₂ => g ω.2) (P₁.prod P₂) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have h1 : (fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' s = (f ⁻¹' s) ×ˢ (Set.univ : Set Ω₂) := by
    ext ⟨a, b⟩; simp
  have h2 : (fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' t = (Set.univ : Set Ω₁) ×ˢ (g ⁻¹' t) := by
    ext ⟨a, b⟩; simp
  have h12 : ((fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' s) ∩ ((fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' t) =
      (f ⁻¹' s) ×ˢ (g ⁻¹' t) := by
    ext ⟨a, b⟩; simp
  rw [h12, h1, h2, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

private lemma iIndepFun_comp_snd
    {Ω₁ Ω₂ ι : Type*} {β : ι → Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [(i : ι) → MeasurableSpace (β i)]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {f : (i : ι) → Ω₂ → β i} (hf : iIndepFun f P₂) :
    iIndepFun (fun i (ω : Ω₁ × Ω₂) => f i ω.2) (P₁.prod P₂) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hsets
  have hprod : (⋂ i ∈ S, (fun ω : Ω₁ × Ω₂ => f i ω.2) ⁻¹' sets i) =
      (Set.univ : Set Ω₁) ×ˢ (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext ⟨a, b⟩; simp
  have hsingle : ∀ i, (fun ω : Ω₁ × Ω₂ => f i ω.2) ⁻¹' sets i =
      (Set.univ : Set Ω₁) ×ˢ (f i ⁻¹' sets i) := fun _ => by
    ext ⟨a, b⟩; simp
  rw [hprod, Measure.prod_prod, measure_univ, one_mul, hf S hsets]
  congr 1; funext i
  rw [hsingle i, Measure.prod_prod, measure_univ, one_mul]

end IndependentDriversHelpers

theorem solution
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P := by
  obtain ⟨Ω₁, m₁, P₁, hP₁, ⟨B₁⟩⟩ :=
    LevyStochCalc.Brownian.BrownianMotion.exists_readable.{0}
  obtain ⟨Ω₂, m₂, P₂, hP₂, ⟨N₂⟩⟩ :=
    Kyprianou.poissonRandomMeasureExists levyMeasure
  let : MeasurableSpace Ω₁ := m₁
  let : MeasurableSpace Ω₂ := m₂
  have : IsProbabilityMeasure P₁ := hP₁
  have : IsProbabilityMeasure P₂ := hP₂
  let P : Measure (Ω₁ × Ω₂) := P₁.prod P₂
  have hP : IsProbabilityMeasure P := inferInstance
  have hmap_fst : P.map Prod.fst = P₁ := by
    simp [P, Measure.map_fst_prod]
  have hmap_snd : P.map Prod.snd = P₂ := by
    simp [P, Measure.map_snd_prod]
  let B : LevyStochCalc.Brownian.BrownianMotion P :=
    { W := fun t ω => B₁.W t ω.1
      measurable_eval := fun t => (B₁.measurable_eval t).comp measurable_fst
      joint_measurable := by
        have hcomp : Function.uncurry (fun (t : ℝ) (ω : Ω₁ × Ω₂) => B₁.W t ω.1) =
            (Function.uncurry B₁.W) ∘ (Prod.map id Prod.fst) := rfl
        rw [hcomp]
        exact B₁.joint_measurable.comp (measurable_id.prodMap measurable_fst)
      initial_zero := Measure.quasiMeasurePreserving_fst.ae B₁.initial_zero
      increment_gaussian := fun {s t} hs hst => by
        have hmeas : Measurable (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) :=
          (B₁.measurable_eval t).sub (B₁.measurable_eval s)
        have hcomp : (fun ω : Ω₁ × Ω₂ => B₁.W t ω.1 - B₁.W s ω.1) =
            (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) ∘ Prod.fst := rfl
        rw [hcomp, ← Measure.map_map hmeas measurable_fst, hmap_fst]
        exact B₁.increment_gaussian hs hst
      continuous_paths := Measure.quasiMeasurePreserving_fst.ae B₁.continuous_paths
      negative_zero := fun s hs => Measure.quasiMeasurePreserving_fst.ae (B₁.negative_zero s hs)
      joint_increment_independent := fun {s t} hs hst => by
        have hbase := IndependentDriversHelpers.indep_comap_fst P₁ P₂
          (B₁.joint_increment_independent hs hst)
        have hL : (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => B₁.W j ω.1) inferInstance) =
            (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (B₁.W j) inferInstance).comap Prod.fst := by
          simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
          rfl
        have hR : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => B₁.W t ω.1 - B₁.W s ω.1) inferInstance =
            (MeasurableSpace.comap (fun ω₁ : Ω₁ => B₁.W t ω₁ - B₁.W s ω₁) inferInstance).comap Prod.fst := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hL, hR]
        exact hbase }
  let N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure :=
    { N := fun ω => N₂.N ω.2
      measurable_eval := fun hS => (N₂.measurable_eval hS).comp measurable_snd
      integer_valued := fun hS hfin => Measure.quasiMeasurePreserving_snd.ae (N₂.integer_valued hS hfin)
      infinite_at_infinite_intensity := fun hS hinf =>
        Measure.quasiMeasurePreserving_snd.ae (N₂.infinite_at_infinite_intensity hS hinf)
      poisson_law := fun {S} hS hfin => by
        have hcomp : (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 S) = (fun ω₂ : Ω₂ => N₂.N ω₂ S) ∘ Prod.snd := rfl
        rw [hcomp, ← Measure.map_map (N₂.measurable_eval hS) measurable_snd, hmap_snd]
        exact N₂.poisson_law hS hfin
      independent_disjoint := fun B' hB' hdisj =>
        IndependentDriversHelpers.iIndepFun_comp_snd P₁ P₂ (N₂.independent_disjoint B' hB' hdisj)
      joint_past_future_independent := fun {s t} hs hst {A} hA hAfin => by
        have hbase := IndependentDriversHelpers.indep_comap_snd P₁ P₂
          (N₂.joint_past_future_independent hs hst hA hAfin)
        have hL : (⨆ C ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
              MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 C) inferInstance) =
            (⨆ C ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
              MeasurableSpace.comap (fun ω₂ : Ω₂ => N₂.N ω₂ C) inferInstance).comap Prod.snd := by
          simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
          rfl
        have hR : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => N₂.N ω.2 (Set.Ioc s t ×ˢ A)) inferInstance =
            (MeasurableSpace.comap (fun ω₂ : Ω₂ => N₂.N ω₂ (Set.Ioc s t ×ˢ A)) inferInstance).comap Prod.snd := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hL, hR]
        exact hbase }
  refine ⟨Ω₁ × Ω₂, inferInstance, P, hP, B, N, ?_⟩
  exact IndependentDriversHelpers.indepFun_comp_fst_snd P₁ P₂
    (fun ω₁ => fun t : ℝ => B₁.W t ω₁) (fun ω₂ => N₂.N ω₂)
