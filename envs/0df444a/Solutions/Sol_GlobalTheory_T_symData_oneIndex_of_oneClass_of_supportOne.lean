-- Prove2me | solution 1 for GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:22.791832+00:00
-- url     : https://prove2.me/submissions/d5092b65-c672-48f8-9d54-6039ab5fe32b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOneStatement
import Theorems.Thm_GlobalTheory_SymChain_oneIndex_of_oneClass_of_supportOne


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  first | exact @GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | exact GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | (intros; apply GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne <;> assumption)
end _root_.GlobalTheory.T
