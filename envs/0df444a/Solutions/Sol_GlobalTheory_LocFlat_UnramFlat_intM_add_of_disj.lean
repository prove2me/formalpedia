-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.intM_add_of_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:47.268751+00:00
-- url     : https://prove2.me/submissions/340b599d-649e-4a44-9f6f-af8b999fb74e

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {m m' : Type} {A B : Matrix m m' k} (h : ∀ r s, B r s = 0 ∨ A r s = 0) :
    IntM (A + B) ↔ IntM A ∧ IntM B := by
  constructor
  · intro hAB
    refine ⟨fun r s => ?_, fun r s => ?_⟩ <;> rcases h r s with h0 | h0
    · simpa [h0] using hAB r s
    · rw [h0]; exact zero_mem _
    · rw [h0]; exact zero_mem _
    · simpa [h0] using hAB r s
  · rintro ⟨hA, hB⟩ r s
    exact add_mem (hA r s) (hB r s)
end GlobalTheory.LocFlat.UnramFlat
