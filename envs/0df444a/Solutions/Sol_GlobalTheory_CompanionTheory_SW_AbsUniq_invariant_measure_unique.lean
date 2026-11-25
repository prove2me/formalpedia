-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:10.840297+00:00
-- url     : https://prove2.me/submissions/552a1189-d7ea-4eb8-a674-83db85fe9b5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_range_orbitQuot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_continuous_orbitQuot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_measurableEmbedding_orbitQuot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_comap_orbitQuot_invariant
import Theorems.Thm_PI_wqUnique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsUniq
namespace GlobalTheory.CompanionTheory.SW.AbsUniq
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V),
      (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) →
      (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z →
      (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) →
      ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 →
      ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 →
      ∃ c : ℝ≥0, μ = c • ν := by
  intro G _ _ _ _ _ _ _ _ V _ _ _ _ _ _ act hc h1 hm Z hZ hinv htr μ ν hμf hνf hμZ hνZ hμ hν hν0

  have hne : Z.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hν0
    rw [← Measure.measure_univ_eq_zero]
    simpa [hemp] using hνZ
  obtain ⟨x₀, hx⟩ := hne
  set H := stabilizerOf act h1 hm x₀ with hH
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  have hHc : IsClosed (H : Set G) := by
    have : (H : Set G) = (fun g : G => act g x₀) ⁻¹' {x₀} := rfl
    rw [this]
    exact isClosed_singleton.preimage hcont
  set φ := orbitQuot act h1 hm x₀ with hφdef
  have hφc : Continuous φ := continuous_orbitQuot act hc h1 hm x₀
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_orbitQuot act hc h1 hm x₀ Z hZ hx hinv htr
  have hr : Set.range φ = Z := range_orbitQuot act h1 hm x₀ Z hx hinv htr
  have hfin : ∀ (m : Measure V), IsLocallyFiniteMeasure m → ∀ K : Set (G ⧸ H), IsCompact K →
      m.comap φ K < ⊤ := by
    intro m _ K hK
    rw [hφ.comap_apply]
    exact (hK.image hφc).measure_lt_top
  have hrec : ∀ (m : Measure V), m Zᶜ = 0 → (m.comap φ).map φ = m := by
    intro m hm0
    rw [hφ.map_comap, hr]
    exact Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact hm0)
  have hρ0 : ν.comap φ ≠ 0 := by
    intro h0
    apply hν0
    rw [← hrec ν hνZ, h0, Measure.map_zero]
  obtain ⟨c, hcc⟩ := PI.wqUnique G H hHc (ν.comap φ) (μ.comap φ) hρ0 (hfin ν hνf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ ν hν) (hfin μ hμf)
    (comap_orbitQuot_invariant act hc h1 hm x₀ hφ μ hμ)
  have hμν : μ = c • ν := by
    rw [← hrec μ hμZ, hcc, Measure.map_smul, hrec ν hνZ]

  have hct : c ≠ ⊤ := by
    rintro rfl
    have hK : ∃ K : Set V, IsCompact K ∧ ν K ≠ 0 := by
      by_contra hno
      push_neg at hno
      apply hν0
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering V]
      exact measure_iUnion_null fun n => hno _ (isCompact_compactCovering V n)
    obtain ⟨K, hKc, hK0⟩ := hK
    have h := hKc.measure_lt_top (μ := μ)
    rw [hμν, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hK0] at h
    exact lt_irrefl _ h
  refine ⟨c.toNNReal, ?_⟩
  rw [hμν]
  ext s hs
  simp [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_toNNReal hct]
end GlobalTheory.CompanionTheory.SW.AbsUniq
