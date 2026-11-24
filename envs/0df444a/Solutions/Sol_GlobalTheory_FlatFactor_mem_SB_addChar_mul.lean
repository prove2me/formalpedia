-- Prove2me | solution 1 for GlobalTheory.FlatFactor.mem_SB_addChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:24.227121+00:00
-- url     : https://prove2.me/submissions/816b6763-a0f5-45ad-9418-6ad100ef5a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlat
import Theorems.Thm_GlobalTheory_RootEx_OpenKernel_isLocallyConstant_coe_addChar
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
namespace GlobalTheory.FlatFactor
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) {X : Type} [TopologicalSpace X]
    (f : X → k) (hf : Continuous f) (Θ : X → ℂ) (hΘ : Θ ∈ SB X) :
    (fun t => (ψ (f t) : ℂ) * Θ t) ∈ SB X :=
  ⟨((GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous hf).mul hΘ.1,
    hΘ.2.mul_left⟩
end GlobalTheory.FlatFactor
