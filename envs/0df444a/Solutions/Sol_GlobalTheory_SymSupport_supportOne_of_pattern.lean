-- Prove2me | solution 1 for GlobalTheory.SymSupport.supportOne_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:21:58.757338+00:00
-- url     : https://prove2.me/submissions/1411099f-e107-40f3-9ee0-6ce04be20ee6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_supportOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
namespace GlobalTheory.SymSupport
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportOne t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportOne s κ S t hP
end GlobalTheory.SymSupport
