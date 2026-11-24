-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.ind_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:30.802825+00:00
-- url     : https://prove2.me/submissions/c4bc2cfb-762f-414e-8b3c-945afd29f6fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
open Classical
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {m m' : Type} (x : Matrix m m' k) :
    Set.indicator {x : Matrix m m' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) x = if IntM x then 1 else 0 := by
  rw [Set.indicator_apply]
  exact if_congr Iff.rfl rfl rfl
end GlobalTheory.LocFlat.UnramFlat
