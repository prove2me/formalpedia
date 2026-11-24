-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.isOpen_vle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:35:03.868815+00:00
-- url     : https://prove2.me/submissions/d2129b67-41e7-4ecf-8407-90814e4ccfbc

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet.TestNearE
theorem _root_.solution {δ : ValueGroupWithZero k} (hδ : δ ≠ 0) :
    IsOpen {z : k | valuation k z ≤ δ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 δ hδ, fun z hz => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hx ⊢
  calc valuation k z = valuation k ((z - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (z - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ δ := max_le hz.le hx
end GlobalTheory.GodementJacquet.TestNearE
