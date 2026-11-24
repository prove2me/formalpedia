-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.finiteOnCompacts_of_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:31.603139+00:00
-- url     : https://prove2.me/submissions/7652ca6e-e2bc-4532-a134-31b4f152fea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution (S : Subgroup G) (ν : Measure G) (h : ν (S : Set G)ᶜ = 0)
    (hS : IsClosed (S : Set G)) (hi : ∀ s ∈ S, ν.map (fun g => s * g) = ν) (B : Set G) (hBm : MeasurableSet B)
    (hB : B ∈ nhds (1 : G)) (hf : ν B ≠ ⊤) : IsFiniteMeasureOnCompacts ν := by
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    by_cases hx : x ∈ S
    · refine ⟨(fun g => x⁻¹ * g) ⁻¹' B, ?_, ?_⟩
      · exact (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hB)
      · rw [← Measure.map_apply (measurable_const_mul _) hBm, hi _ (S.inv_mem hx)]; exact hf.lt_top
    · exact ⟨_, hS.isOpen_compl.mem_nhds hx, by rw [h]; exact ENNReal.zero_lt_top⟩
  infer_instance
end GlobalTheory.IwasawaShape
