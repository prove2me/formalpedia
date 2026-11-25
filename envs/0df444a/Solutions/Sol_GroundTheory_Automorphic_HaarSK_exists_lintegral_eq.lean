-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.exists_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:12.340365+00:00
-- url     : https://prove2.me/submissions/dea47715-963e-44d7-b0bf-6a190a25257e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_exists_eq_smul_map_mulMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S K : Subgroup G}
variable (hSK : Surjective (mulMap S K))
variable {hSK}
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
    (μS : Measure S) [μS.IsHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ s, ∫⁻ k, f ((s : G) * k) ∂μK ∂μS := by
  obtain ⟨c, hc⟩ := exists_eq_smul_map_mulMap μ hS hK hSK μS μK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hform : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = c * ∫⁻ s, ∫⁻ k, f ((s : G) * k) ∂μK ∂μS := by
    intro f hf
    rw [hc, lintegral_smul_measure, lintegral_map hf continuous_mulMap.measurable,
      lintegral_prod (fun p : S × K => f (mulMap S K p))
        (hf.comp continuous_mulMap.measurable).aemeasurable, ENNReal.smul_def,
      smul_eq_mul]
    rfl
  refine ⟨c, fun h0 => ?_, hform⟩
  have h1 := hform 1 measurable_const
  rw [h0, ENNReal.coe_zero, zero_mul] at h1
  simp only [Pi.one_apply, lintegral_const, one_mul] at h1
  exact (IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty) h1
end GroundTheory.Automorphic.HaarSK
