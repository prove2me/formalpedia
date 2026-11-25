-- Prove2me | solution 1 for GlobalTheory.T.flatRowIndicator_of_symLevelExchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:17.494358+00:00
-- url     : https://prove2.me/submissions/dc86e9ec-8dba-4c47-a9f9-851d08ea0dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchangeStatement
import Theorems.Thm_GlobalTheory_LocFlat_pureRow_of_exchange


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  first | exact @GlobalTheory.LocFlat.pureRow_of_exchange | exact GlobalTheory.LocFlat.pureRow_of_exchange | (intros; apply GlobalTheory.LocFlat.pureRow_of_exchange <;> assumption)
end _root_.GlobalTheory.T
