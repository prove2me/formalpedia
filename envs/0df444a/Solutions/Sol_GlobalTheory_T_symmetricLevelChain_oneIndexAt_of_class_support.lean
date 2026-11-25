-- Prove2me | solution 1 for GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:40.942832+00:00
-- url     : https://prove2.me/submissions/5db2e385-e311-43e5-91fa-404ccef73075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainOneIndexAtOfClassSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainOneIndexAtOfClassSupportStatement
import Theorems.Thm_GlobalTheory_SymChain_oneIndexAt_of_classAt_supportAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  first | exact @GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | exact GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | (intros; apply GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt <;> assumption)
end _root_.GlobalTheory.T
