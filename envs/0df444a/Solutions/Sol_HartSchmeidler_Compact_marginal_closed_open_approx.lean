-- Prove2me | solution 1 for HartSchmeidler.Compact.marginal_closed_open_approx
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:28:27.390272+00:00
-- url     : https://prove2.me/submissions/5f49190a-e312-465d-acea-d37f16c1a9fe

import Definitions.Def_HartSchmeidler_Compact_Game



namespace HartSchmeidler.Compact

open MeasureTheory

theorem mco_core {ι : Type*} {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (i : ι) (R : Set (S i)) (hR : MeasurableSet R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set (S i), IsClosed F ∧ IsOpen G ∧ F ⊆ R ∧ R ⊆ G ∧
      p ((fun s : Profile S => s i) ⁻¹' (G \ F)) < ENNReal.ofReal ε := by
  have hπc : Continuous (fun s : Profile S => s i) := continuous_apply i
  set π : Profile S → S i := fun s => s i with hπ
  have hA : MeasurableSet (π ⁻¹' R) := hπc.measurable hR
  have hδ : (ENNReal.ofReal ε / 2) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, hε]
  obtain ⟨C, hCA, hCc, hC⟩ := hA.exists_isCompact_sdiff_lt (μ := p) (measure_ne_top _ _) hδ
  obtain ⟨C', hCA', hCc', hC'⟩ := hA.compl.exists_isCompact_sdiff_lt (μ := p) (measure_ne_top _ _) hδ
  refine ⟨π '' C, (π '' C')ᶜ, (hCc.image hπc).isClosed, (hCc'.image hπc).isClosed.isOpen_compl, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩; exact hCA hc
  · intro r hr ⟨c', hc', hcr⟩
    exact hCA' hc' (show π c' ∈ R from by rw [hcr]; exact hr)
  · calc p (π ⁻¹' ((π '' C')ᶜ \ π '' C)) ≤ p ((π ⁻¹' R \ C) ∪ ((π ⁻¹' R)ᶜ \ C')) := by
          apply measure_mono
          intro s hs
          have h1 : s ∉ C' := fun h => hs.1 ⟨s, h, rfl⟩
          have h2 : s ∉ C := fun h => hs.2 ⟨s, h, rfl⟩
          by_cases hsA : s ∈ π ⁻¹' R
          · exact Or.inl ⟨hsA, h2⟩
          · exact Or.inr ⟨hsA, h1⟩
      _ ≤ p (π ⁻¹' R \ C) + p ((π ⁻¹' R)ᶜ \ C') := measure_union_le _ _
      _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := ENNReal.add_lt_add hC hC'
      _ = ENNReal.ofReal ε := ENNReal.add_halves _

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {ι : Type*} {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (i : ι) (R : Set (S i)) (hR : MeasurableSet R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set (S i), IsClosed F ∧ IsOpen G ∧ F ⊆ R ∧ R ⊆ G ∧
      p ((fun s : Profile S => s i) ⁻¹' (G \ F)) < ENNReal.ofReal ε := by
  exact mco_core p hp i R hR ε hε
