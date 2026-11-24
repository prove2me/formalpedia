-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.fill_add_single_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:21.582964+00:00
-- url     : https://prove2.me/submissions/3b5364c0-68c4-4967-88c5-715dc3fc60d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
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
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k)
    (r₀ : m) (q₀ : m') (h1 : (r₀, q₀) ∉ ev) (h2 : (r₀, q₀) ∉ it) (a : k) :
    fill ev it β t x + Matrix.single r₀ q₀ a = fill ev it β (t + Matrix.single r₀ q₀ a) x := by
  ext r q
  by_cases hrq : r₀ = r ∧ q₀ = q
  · obtain ⟨rfl, rfl⟩ := hrq
    simp [fill, Matrix.single_apply, h1, h2]
  · simp [fill, Matrix.single_apply, hrq]
end GlobalTheory.FlatFactor.UpStage
