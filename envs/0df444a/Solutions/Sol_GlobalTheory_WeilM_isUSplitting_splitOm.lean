-- Prove2me | solution 1 for GlobalTheory.WeilM.isUSplitting_splitOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:00.59229+00:00
-- url     : https://prove2.me/submissions/4deb9109-cb8d-498f-aa18-c88feb6647d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_splitOm
import Theorems.Thm_GlobalTheory_WeilM_isUnitaryOn_splitOm
import Theorems.Thm_GlobalTheory_WeilM_IsContOn_of_isLocallyConstant
import Theorems.Thm_GlobalTheory_WeilM_isSplitting_splitOm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}
namespace GlobalTheory.WeilM
theorem _root_.solution (ψ : AddChar F ℂ) (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) :
    IsUSplitting (sbClass F) ψ (splitDarboux hA hB σ) (actB (swapA F)) (splitOm (distribHaarChar F) χ JB σ) :=
  ⟨isSplitting_splitOm _ χ hA hB σ ψ, isUnitaryOn_splitOm χ JB σ,
    .of_isLocallyConstant fun _ hφ => isLocallyConstant_splitOm χ hχ JB σ hφ⟩
end GlobalTheory.WeilM
