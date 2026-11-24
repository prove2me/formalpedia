-- Prove2me | solution 1 for GlobalTheory.StepData.isOpen_isCompact_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:29.955233+00:00
-- url     : https://prove2.me/submissions/6e32d308-5a90-43a1-b2a5-c651610ce607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution (g : GL Y k) {J : Subgroup (GL Y k)} (ho : IsOpen (J : Set (GL Y k)))
    (hc : IsCompact (J : Set (GL Y k))) :
    IsOpen (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) ∧
      IsCompact (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL Y k)) := by
  let e : GL Y k ≃ₜ GL Y k := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g⁻¹⁻¹)
  exact ⟨ho.preimage e.continuous, e.isCompact_preimage.2 hc⟩
end GlobalTheory.StepData
