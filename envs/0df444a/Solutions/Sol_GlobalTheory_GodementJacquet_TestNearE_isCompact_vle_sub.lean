-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.isCompact_vle_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:35:01.936798+00:00
-- url     : https://prove2.me/submissions/b37c8cbe-7bc8-4979-8d0b-be38bae77656

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
theorem _root_.solution (δ : ValueGroupWithZero k) (c : k) :
    IsCompact {z : k | valuation k (z - c) ≤ δ} := by
  have h := (IsNonarchimedeanLocalField.isCompact_closedBall k δ).image (continuous_add_right c)
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨z - c, hz, sub_add_cancel z c⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
end GlobalTheory.GodementJacquet.TestNearE
