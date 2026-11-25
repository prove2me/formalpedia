-- Prove2me | solution 1 for GlobalTheory.T.flatColumnIndicator_pure_at_symmetricPosition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:05.045972+00:00
-- url     : https://prove2.me/submissions/3c904e1c-fa39-4e95-bd57-0c1cb7e1d8ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPositionStatement
import Theorems.Thm_GlobalTheory_LocFlat_pureCol_of_pattern


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureCol S t ν := by
  first | exact @GlobalTheory.LocFlat.pureCol_of_pattern | exact GlobalTheory.LocFlat.pureCol_of_pattern | (intros; apply GlobalTheory.LocFlat.pureCol_of_pattern <;> assumption)
end _root_.GlobalTheory.T
