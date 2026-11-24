-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.coe_psi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:24.917979+00:00
-- url     : https://prove2.me/submissions/ab013edb-adbd-433f-9ee8-bd9af385edc7

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
theorem _root_.solution {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, Circle.coe_mul, ih]
end GlobalTheory.LocFlat.UnramFlat
