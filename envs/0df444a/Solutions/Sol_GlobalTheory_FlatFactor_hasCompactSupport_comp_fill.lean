-- Prove2me | solution 1 for GlobalTheory.FlatFactor.hasCompactSupport_comp_fill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:08.628638+00:00
-- url     : https://prove2.me/submissions/60f7c3ba-0a15-41a8-9eb9-4b3931a59180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isCompact
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
open GlobalTheory GlobalTheory.FlatFactor
namespace GlobalTheory.FlatFactor
theorem _root_.solution {k : Type} [Field k] [TopologicalSpace k] [T2Space k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (hΘ : HasCompactSupport Θ) :
    HasCompactSupport (fun x => Θ (fill ev it β t x)) := by
  let pr : Matrix m m' k → ({e : m × m' // e ∈ it} → k) := fun T i => T i.1.1 i.1.2
  have hpr : Continuous pr := continuous_pi fun i => (continuous_apply i.1.2).comp (continuous_apply i.1.1)
  have hK : IsCompact (pr '' tsupport Θ) := hΘ.isCompact.image hpr
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨fill ev it β t x, subset_tsupport _ h, ?_⟩
  funext i
  simp [pr, fill, i.2]
end GlobalTheory.FlatFactor
