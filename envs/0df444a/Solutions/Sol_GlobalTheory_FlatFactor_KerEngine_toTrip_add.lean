-- Prove2me | solution 1 for GlobalTheory.FlatFactor.KerEngine.toTrip_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:36.845083+00:00
-- url     : https://prove2.me/submissions/67a272cf-7d0d-4960-a87c-5be696cf3e38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLaws
import Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_sum_single_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
namespace GlobalTheory.FlatFactor.KerEngine
theorem _root_.solution (ev it : Finset (m × m')) (hd : Disjoint ev it) (β t : Matrix m m' k) (a : {e // e ∈ it} → k) :
    toTrip ev it β (t + ∑ e ∈ it, Matrix.single e.1 e.2 (if h : e ∈ it then a ⟨e, h⟩ else 0)) =
      toTrip ev it β t + (0, 0, a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
  · have h := i.2
    simp [toTrip, sum_single_apply, h.1]
  · have h : i.1 ∉ it := Finset.disjoint_left.mp hd i.2
    simp [toTrip, sum_single_apply, h]
  · simp [toTrip, sum_single_apply, i.2]
end GlobalTheory.FlatFactor.KerEngine
