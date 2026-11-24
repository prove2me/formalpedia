-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsUniq.comap_orbitQuot_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:43.448136+00:00
-- url     : https://prove2.me/submissions/0b31f31a-c65c-4b6d-8aef-7e312f3ead67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_orbitQuot_smul

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
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V)
    (hφ : MeasurableEmbedding (orbitQuot act h1 hm x₀)) (μ : Measure V)
    (hμ : ∀ g, μ.map (act g) = μ) (g : G) (s : Set (G ⧸ stabilizerOf act h1 hm x₀))
    (hs : MeasurableSet s) :
    μ.comap (orbitQuot act h1 hm x₀) ((fun y => g • y) ⁻¹' s) =
      μ.comap (orbitQuot act h1 hm x₀) s := by
  have hact : Measurable (act g) :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  rw [hφ.comap_apply, hφ.comap_apply]
  have himg : orbitQuot act h1 hm x₀ '' ((fun y => g • y) ⁻¹' s) =
      act g ⁻¹' (orbitQuot act h1 hm x₀ '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g • y, hy, orbitQuot_smul act h1 hm x₀ g y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨g⁻¹ • y, ?_, ?_⟩
      · show g • g⁻¹ • y ∈ s
        simpa using hy
      · rw [orbitQuot_smul, hyx, ← hm, inv_mul_cancel, h1]
  rw [himg]
  conv_rhs => rw [← hμ g]
  rw [Measure.map_apply hact (hφ.measurableSet_image.2 hs)]
end GlobalTheory.CompanionTheory.SW.AbsUniq
