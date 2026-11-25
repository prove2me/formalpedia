-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.integral_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:54.537448+00:00
-- url     : https://prove2.me/submissions/dc9a65c8-27b5-4308-84b8-c0263ae2981e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_measurableSet_box

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
open Classical
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution (ν : Measure k) (c : kˣ) :
    ∫ u, (if u ∈ box n c then (1 : ℂ) else 0) ∂(Measure.pi fun _ : n => ν) =
      (((Measure.pi fun _ : n => ν) (box n c : Set (n → k))).toReal : ℂ) := by
  have e : (fun u : n → k => if u ∈ box n c then (1 : ℂ) else 0) = Set.indicator (box n c : Set (n → k)) fun _ => 1 := by
    funext u; simp [Set.indicator_apply]
  rw [e, integral_indicator_const _ (measurableSet_box c)]
  simp [Measure.real]
end GlobalTheory.LocFlat.DoubleStepProof
