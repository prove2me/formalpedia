-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.measurableEmbedding_orbitQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:44:13.162143+00:00
-- url     : https://prove2.me/submissions/f8c469f2-189e-46bd-a7ba-b489f6a1d1de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_orbitQuot_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_range_orbitQuot
import Theorems.Thm_PI_AprimeInfA_polish_of_lcsc


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
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hZ : IsClosed Z)
    (hx : x₀ ∈ Z) (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z)
    (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    MeasurableEmbedding (orbitQuot act h1 hm x₀) := by
  have hcont : Continuous fun g : G => act g x₀ :=
    hc.comp (continuous_id.prodMk continuous_const)
  refine ⟨orbitQuot_injective act h1 hm x₀, ?_, ?_⟩
  · intro A hA
    rw [measurableSet_quotient]
    exact hcont.measurable hA
  · intro S hS
    have hS' : MeasurableSet ((fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S) :=
      measurableSet_quotient.1 hS
    let o : G → Z := fun g => ⟨act g x₀, hinv g x₀ hx⟩
    have hoc : Continuous o := hcont.subtype_mk _
    have hos : Function.Surjective o := by
      rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := htr x₀ hx y hy
      exact ⟨g, rfl⟩
    haveI : PolishSpace G := PI.AprimeInfA.polish_of_lcsc G
    have hb := hoc.map_eq_borel hos
    let T : Set Z := Subtype.val ⁻¹' (orbitQuot act h1 hm x₀ '' S)
    have hT : MeasurableSet T := by
      have hpre : o ⁻¹' T = (fun g : G => (g : G ⧸ stabilizerOf act h1 hm x₀)) ⁻¹' S := by
        ext g
        constructor
        · rintro ⟨y, hy, hyg⟩
          have : y = (g : G ⧸ stabilizerOf act h1 hm x₀) :=
            orbitQuot_injective act h1 hm x₀ hyg
          simpa [this] using hy
        · intro hg
          exact ⟨_, hg, rfl⟩
      have hm' : MeasurableSet[MeasurableSpace.map o ‹MeasurableSpace G›] T := by
        show MeasurableSet (o ⁻¹' T)
        rw [hpre]
        exact hS'
      rw [hb, ← BorelSpace.measurable_eq] at hm'
      exact hm'
    have himg : orbitQuot act h1 hm x₀ '' S = Subtype.val '' T := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2]
      rintro _ ⟨y, -, rfl⟩
      rw [← range_orbitQuot act h1 hm x₀ Z hx hinv htr]
      exact ⟨y, rfl⟩
    rw [himg]
    exact (MeasurableEmbedding.subtype_coe hZ.measurableSet).measurableSet_image.2 hT
end GlobalTheory.CompanionTheory.SW.AbsUniq
