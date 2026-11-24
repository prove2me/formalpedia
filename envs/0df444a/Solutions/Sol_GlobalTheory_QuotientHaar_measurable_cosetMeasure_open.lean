-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.measurable_cosetMeasure_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:52.801696+00:00
-- url     : https://prove2.me/submissions/11d2ae43-2818-4e88-a81c-17494cd9d3fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_apply
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
namespace GlobalTheory.QuotientHaar
theorem _root_.solution (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {U : Set G}
    (hU : IsOpen U) : Measurable (fun q : G ⧸ H => cosetMeasure H ν q U) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : ν.Regular := inferInstance
  refine measurable_of_Ioi fun c => IsOpen.measurableSet ?_
  rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage, isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν g hU.measurableSet] at hg
  have hO : IsOpen ((fun h : H => g * (h : G)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKU, hK, hc⟩ := hO.exists_lt_isCompact hg
  have hev : ∀ᶠ x in nhds g, ∀ h ∈ K, x * (h : G) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous (fun p : G × H => p.1 * (p.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hKU hh))
  filter_upwards [hev] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν x hU.measurableSet]
  exact hc.trans_le (measure_mono fun h hh => hx h hh)
end GlobalTheory.QuotientHaar
