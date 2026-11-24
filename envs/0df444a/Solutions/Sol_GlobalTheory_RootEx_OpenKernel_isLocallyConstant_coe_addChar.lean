-- Prove2me | solution 1 for GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:24:30.004024+00:00
-- url     : https://prove2.me/submissions/0bee4cee-41ee-4115-934b-45e02d4010fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpenKernel
open MeasureTheory ValuativeRel Matrix
open Filter Topology
namespace GlobalTheory.RootEx.OpenKernel
namespace _root_.GlobalTheory.RootEx.OpenKernel
theorem _root_.solution {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by
  by_cases h : ψ = 1
  · subst h
    simp only [AddChar.one_apply, Circle.coe_one]
    exact IsLocallyConstant.const 1
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.SplitWeil.exists_hasConductor_of_continuous ψ hψ h
    exact (_root_.GlobalTheory.SplitWeil.HasConductor.isLocallyConstant hc).comp _
end _root_.GlobalTheory.RootEx.OpenKernel
end GlobalTheory.RootEx.OpenKernel
