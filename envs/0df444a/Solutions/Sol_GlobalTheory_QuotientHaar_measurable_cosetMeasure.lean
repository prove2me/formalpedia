-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.measurable_cosetMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:13.057091+00:00
-- url     : https://prove2.me/submissions/191ef1a7-eb34-4a68-bbbf-c9b2b341e47a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_lt_top
import Theorems.Thm_GlobalTheory_QuotientHaar_measurable_cosetMeasure_open
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
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    Measurable (cosetMeasure H ν) := by
  let K := CompactExhaustion.choice G
  have hres : ∀ n, Measurable (fun q => (cosetMeasure H ν q).restrict (interior (K n))) := by
    intro n
    haveI : ∀ q, IsFiniteMeasure ((cosetMeasure H ν q).restrict (interior (K n))) := fun q =>
      isFiniteMeasure_restrict.mpr ((measure_mono interior_subset).trans_lt
        (cosetMeasure_lt_top H hH ν q (K.isCompact n))).ne
    have key : ∀ s : Set G, IsOpen s →
        Measurable fun q => (cosetMeasure H ν q).restrict (interior (K n)) s := by
      intro s hs
      simp only [Measure.restrict_apply hs.measurableSet]
      exact measurable_cosetMeasure_open H hH ν (hs.inter isOpen_interior)
    exact Measurable.measure_of_isPiSystem (S := {s : Set G | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen key (key _ isOpen_univ)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone fun n => s ∩ interior (K n) := fun a b hab =>
    Set.inter_subset_inter_right _ (interior_mono (K.subset hab))
  have hun : ⋃ n, s ∩ interior (K n) = s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, h, K.subset_interior_succ n hn⟩
  have : (fun q => cosetMeasure H ν q s) =
      fun q => ⨆ n, (cosetMeasure H ν q).restrict (interior (K n)) s := by
    funext q
    simp only [Measure.restrict_apply hs]
    rw [← hmono.measure_iUnion, hun]
  rw [this]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hres n)
end GlobalTheory.QuotientHaar
