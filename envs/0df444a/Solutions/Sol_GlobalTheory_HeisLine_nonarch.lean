-- Prove2me | solution 1 for GlobalTheory.HeisLine.nonarch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:25:03.481888+00:00
-- url     : https://prove2.me/submissions/ea8e7462-f4d8-4751-8720-138869870b4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
namespace GlobalTheory.HeisLine
theorem _root_.solution : NonarchimedeanAddGroup (n → k) where
  toIsTopologicalAddGroup := inferInstance
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub s, hs⟩
end GlobalTheory.HeisLine
