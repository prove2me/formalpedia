-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.measurableSet_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:53.576795+00:00
-- url     : https://prove2.me/submissions/307c9deb-cd13-48bc-b828-cbdc17d6621a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_box_eq_pi
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution (c : kˣ) : MeasurableSet (box n c : Set (n → k)) := by
  rw [box_eq_pi]; exact MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet
end GlobalTheory.LocFlat.DoubleStepProof
