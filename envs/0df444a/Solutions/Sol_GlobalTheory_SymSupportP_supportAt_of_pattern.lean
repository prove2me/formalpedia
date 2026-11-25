-- Prove2me | solution 1 for GlobalTheory.SymSupportP.supportAt_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:44.224804+00:00
-- url     : https://prove2.me/submissions/0c3693d8-4371-436e-b0a9-f6e838d75035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruencStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
import Theorems.Thm_GlobalTheory_SymSupportP_supportAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport
noncomputable section
open GlobalTheory GlobalTheory.SymSupportP
namespace GlobalTheory.SymSupportP
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportAt t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportAt s κ S t hP
end GlobalTheory.SymSupportP
