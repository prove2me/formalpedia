-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.vol_box_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:15.393005+00:00
-- url     : https://prove2.me/submissions/41e30124-8be4-437a-9452-5addbbf233d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_box_eq_pi
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


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
theorem _root_.solution (ν : Measure k) [ν.IsAddHaarMeasure] (c : kˣ) :
    0 < ((Measure.pi fun _ : n => ν) (box n c : Set (n → k))).toReal := by
  have := secondCountable k
  rw [box_eq_pi, Measure.pi_pi]
  refine ENNReal.toReal_pos (Finset.prod_ne_zero_iff.2 fun i _ => ?_) (ENNReal.prod_ne_top fun i _ => ?_)
  · exact ((isOpen_cball c).measure_pos ν ⟨0, by simp [cball]⟩).ne'
  · exact (isCompact_cball c).measure_lt_top.ne
end GlobalTheory.LocFlat.DoubleStepProof
