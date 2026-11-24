-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.isHaarMeasure_bind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:43.437111+00:00
-- url     : https://prove2.me/submissions/122dbc87-c153-4dc9-8200-9492b490293c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_apply
import Theorems.Thm_GlobalTheory_QuotientHaar_measurable_cosetMeasure
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
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) : (μ.bind (cosetMeasure H ν)).IsHaarMeasure := by
  haveI := hμ.finiteOnCompacts
  haveI := hμ.invariant
  have hm := measurable_cosetMeasure H hH ν
  haveI hfin : IsFiniteMeasureOnCompacts (μ.bind (cosetMeasure H ν)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.bind_apply hK.measurableSet hm.aemeasurable]
    have hC : ν (Subtype.val ⁻¹' (K⁻¹ * K)) < ⊤ :=
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)).measure_lt_top
    have hπ : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K) :=
      hK.image QuotientGroup.continuous_mk
    have hle : ∀ q, cosetMeasure H ν q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν (Subtype.val ⁻¹' (K⁻¹ * K))) q := by
      intro q
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        rw [cosetMeasure_apply H ν k hK.measurableSet]
        refine measure_mono fun h hh => ?_
        exact ⟨k⁻¹, Set.inv_mem_inv.mpr hk, k * h, hh, by simp⟩
      · induction q using QuotientGroup.induction_on with
        | H g =>
          rw [cosetMeasure_apply H ν g hK.measurableSet]
          have : (fun h : H => g * (h : G)) ⁻¹' K = ∅ :=
            Set.eq_empty_of_forall_notMem fun h hh => hq ⟨g * h, hh, by simp⟩
          simp [this]
    refine (lintegral_mono hle).trans_lt ((lintegral_indicator_const_le _ _).trans_lt ?_)
    exact ENNReal.mul_lt_top hC hπ.measure_lt_top
  haveI hinv : (μ.bind (cosetMeasure H ν)).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).mp fun a s hs => ?_
    rw [Measure.bind_apply hs hm.aemeasurable,
      Measure.bind_apply (measurable_const_mul a hs) hm.aemeasurable]
    have h1 : Measurable fun q => cosetMeasure H ν q s := (Measure.measurable_coe hs).comp hm
    have h2 := (measurePreserving_smul a μ).lintegral_comp h1
    rw [← h2]
    refine lintegral_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      change _ = cosetMeasure H ν ((a * g : G) : G ⧸ H) s
      rw [cosetMeasure_apply H ν g (measurable_const_mul a hs), cosetMeasure_apply H ν _ hs]
      congr 1
      ext h
      simp [mul_assoc]
  have hne : μ.bind (cosetMeasure H ν) ≠ 0 := by
    intro h0
    have h1 : μ.bind (cosetMeasure H ν) Set.univ = ν Set.univ * μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable, ← lintegral_const]
      refine lintegral_congr fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rw [cosetMeasure_apply H ν g MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    exact mul_ne_zero (isOpen_univ.measure_ne_zero ν Set.univ_nonempty)
      (Measure.measure_univ_ne_zero.mpr hμ.ne_zero) h1.symm
  haveI : IsLocallyFiniteMeasure (μ.bind (cosetMeasure H ν)) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : NeZero (μ.bind (cosetMeasure H ν)) := ⟨hne⟩
  haveI : (μ.bind (cosetMeasure H ν)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_regular
  exact {}
end GlobalTheory.QuotientHaar
