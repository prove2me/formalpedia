-- Prove2me | solution 1 for GlobalTheory.T.symLevel_doubleStep_of_flatColumn_flatRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:43.711543+00:00
-- url     : https://prove2.me/submissions/4a46ec15-fdfe-42cb-b973-bd1727a26b28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRowStatement
import Theorems.Thm_GlobalTheory_LocFlat_doubleStep_of_pureCol_pureRow


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneIndexAt t ν → GlobalTheory.LocFlat.PureCol S t ν → GlobalTheory.LocFlat.PureRow S t ν → GlobalTheory.LocFlat.DoubleStep S t ν := by
  first | exact @GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | exact GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | (intros; apply GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow <;> assumption)
end _root_.GlobalTheory.T
