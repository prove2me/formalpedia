-- Prove2me | solution 1 for Kyprianou.Ch02.prmCompletedPastEventRawLaterV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:40:25.020951+00:00
-- url     : https://prove2.me/submissions/44d4e064-3c8f-4f71-b264-03b10a6c842b

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

section
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ν : Measure ℝ} [SigmaFinite ν]

private noncomputable def natMeasSpace
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (v : ℝ≥0) (_ : v ≤ r) (A : Set ℝ) (_ : MeasurableSet A),
    MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance

private lemma natMeasSpace_le
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : natMeasSpace N r ≤ mΩ := by
  refine iSup₂_le fun v _ => iSup₂_le fun A hA => ?_
  exact (N.measurable_eval (measurableSet_Ioc.prod hA)).comap_le

private lemma natMeasSpace_mono
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r₁ r₂ : ℝ≥0} (hr : r₁ ≤ r₂) : natMeasSpace N r₁ ≤ natMeasSpace N r₂ := by
  refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
  exact le_iSup₂_of_le v (hv.trans hr) (le_iSup₂_of_le A hA le_rfl)

private lemma natMeasSpace_count_measurable
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r v : ℝ≥0} (hv : v ≤ r) {A : Set ℝ} (hA : MeasurableSet A) :
    @Measurable Ω ℝ≥0∞ (natMeasSpace N r) inferInstance
      (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
  exact Measurable.mono (comap_measurable _)
    (le_iSup₂_of_le v hv (le_iSup₂_of_le A hA le_rfl)) le_rfl

end

private def completedMeasSpace
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' E :=
    @MeasurableSet Ω mΩ E ∧ ∃ A : Set Ω, @MeasurableSet Ω m A ∧ P (symmDiff E A) = 0
  measurableSet_empty :=
    ⟨@MeasurableSet.empty Ω mΩ, ∅, @MeasurableSet.empty Ω m, by simp⟩
  measurableSet_compl E hE := by
    rcases hE with ⟨hEm, A, hAm, hAE⟩
    refine ⟨MeasurableSet.compl (m := mΩ) hEm, Aᶜ, MeasurableSet.compl (m := m) hAm, ?_⟩
    have hsym : symmDiff Eᶜ Aᶜ = symmDiff E A := by
      ext x; simp only [Set.mem_symmDiff, Set.mem_compl_iff]; tauto
    rw [hsym]
    exact hAE
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion (m := mΩ) (fun n => (hf n).1), ?_⟩
    choose A hAm hAE using fun n => (hf n).2
    refine ⟨⋃ n, A n, MeasurableSet.iUnion (m := m) hAm, ?_⟩
    have hsub : symmDiff (⋃ n, f n) (⋃ n, A n) ⊆ ⋃ n, symmDiff (f n) (A n) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨⟨n, hfn⟩, hnot⟩ | ⟨⟨n, hAn⟩, hnot⟩
      · exact ⟨n, Or.inl ⟨hfn, fun h => hnot ⟨n, h⟩⟩⟩
      · exact ⟨n, Or.inr ⟨hAn, fun h => hnot ⟨n, h⟩⟩⟩
    exact measure_mono_null hsub (measure_iUnion_null hAE)

private noncomputable def completedNatFiltration
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq r := completedMeasSpace P (natMeasSpace N r)
  mono' r₁ r₂ hr E hE :=
    ⟨hE.1, let ⟨A, hAm, hAE⟩ := hE.2; ⟨A, natMeasSpace_mono N hr A hAm, hAE⟩⟩
  le' _ _ hE := hE.1

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (s u : ℝ≥0) (hsu : s < u) (E : Set Ω) (hE : @MeasurableSet Ω (ℱ s) E) :
    ∃ A : Set Ω, @MeasurableSet Ω (⨆ (v : ℝ≥0) (_ : v ≤ u) (A : Set ℝ) (_ : MeasurableSet A),
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance) A ∧ E =ᵐ[P] A := by
  let 𝒞 := completedNatFiltration P N
  have h1 : ∀ t v : ℝ≥0, v ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (𝒞.rightCont t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
    intro t v hv A hA
    have hbase : @Measurable Ω ℝ≥0∞ (𝒞 t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
      intro S hS
      have hm_nat : @MeasurableSet Ω (natMeasSpace N t)
          ((fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) ⁻¹' S) :=
        natMeasSpace_count_measurable N hv hA hS
      exact ⟨natMeasSpace_le N t _ hm_nat, _, hm_nat, by simp⟩
    exact hbase.mono (𝒞.le_rightCont t) le_rfl
  have h2 : ∀ t (S : Set Ω), MeasurableSet S → P S = 0 →
      @MeasurableSet Ω (𝒞.rightCont t) S := by
    intro t S hS hPS
    have hbase : @MeasurableSet Ω (𝒞 t) S :=
      ⟨hS, ∅, @MeasurableSet.empty Ω (natMeasSpace N t), by simpa using hPS⟩
    exact 𝒞.le_rightCont t S hbase
  have h3 : 𝒞.rightCont.IsRightContinuous := ⟨le_of_eq 𝒞.rightCont_self⟩
  have hle : ℱ ≤ 𝒞.rightCont := hℱ.2.2.2 𝒞.rightCont h1 h2 h3
  have hrc : 𝒞.rightCont s = ⨅ (j : ℝ≥0) (_ : j > s), 𝒞 j := by
    rw [Filtration.rightCont_apply]
    simp [nhdsWithin_Ioi_neBot (le_refl s)]
  have hbound : ℱ s ≤ 𝒞 u := by
    refine (hle s).trans ?_
    rw [hrc]
    exact iInf₂_le u hsu
  obtain ⟨A, hA, hEA⟩ := (hbound E hE).2
  exact ⟨A, hA, measure_symmDiff_eq_zero_iff.mp hEA⟩
