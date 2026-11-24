-- Prove2me | solution 1 for GlobalTheory.RootEx.OpenKernel.characters_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:04.719493+00:00
-- url     : https://prove2.me/submissions/34b576cf-c037-4d86-8af5-0bb83d3e60af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Theorems.Thm_GlobalTheory_RootEx_OpenKernel_isLocallyConstant_coe_addChar
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_isOpen_ker_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpenKernel
open MeasureTheory ValuativeRel Matrix
open Filter Topology
namespace GlobalTheory.RootEx.OpenKernel
namespace _root_.GlobalTheory.RootEx.OpenKernel
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) :=
  fun _ _ _ _ _ => ⟨fun μ hμ => _root_.GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous μ hμ,
    fun ψ hψ => _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ⟩
end _root_.GlobalTheory.RootEx.OpenKernel
end GlobalTheory.RootEx.OpenKernel
