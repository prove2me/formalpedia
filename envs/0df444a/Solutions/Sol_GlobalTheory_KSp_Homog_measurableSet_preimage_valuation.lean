-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.measurableSet_preimage_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:15.558394+00:00
-- url     : https://prove2.me/submissions/4ac06e7d-463c-4a75-b379-0116f56d9a3d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_KSp_Homog_isOpen_sphere
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution (S : Set (ValueGroupWithZero F)) :
    MeasurableSet (valuation F ⁻¹' S) := by
  haveI := GlobalTheory.SplitWeil.t2Space F
  have e : valuation F ⁻¹' S = valuation F ⁻¹' (S \ {0}) ∪ valuation F ⁻¹' (S ∩ {0}) := by
    rw [← Set.preimage_union, Set.diff_union_inter]
  rw [e]
  refine MeasurableSet.union (IsOpen.measurableSet ?_) ?_
  · have : valuation F ⁻¹' (S \ {0}) = ⋃ γ ∈ S \ {0}, {y : F | valuation F y = γ} := by
      ext y; simp
    rw [this]
    exact isOpen_biUnion fun γ hγ ↦ isOpen_sphere hγ.2
  · by_cases h0 : (0 : ValueGroupWithZero F) ∈ S
    · have : valuation F ⁻¹' (S ∩ {0}) = {0} := by
        ext y; simp [h0]
      rw [this]; exact measurableSet_singleton 0
    · have : valuation F ⁻¹' (S ∩ {0}) = ∅ := by
        ext y; simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hy h'; exact h0 (h' ▸ hy)
      rw [this]; exact MeasurableSet.empty
end GlobalTheory.KSp.Homog
