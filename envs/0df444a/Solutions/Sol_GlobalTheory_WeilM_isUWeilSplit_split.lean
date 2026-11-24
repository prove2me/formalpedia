-- Prove2me | solution 1 for GlobalTheory.WeilM.isUWeilSplit_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:52.001401+00:00
-- url     : https://prove2.me/submissions/15e2803f-b059-41be-845d-a46ccd2e5e88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
import Theorems.Thm_GlobalTheory_WeilM_isUSplitting_splitOm
import Theorems.Thm_GlobalTheory_WeilM_isLagr_diagCols
import Theorems.Thm_GlobalTheory_WeilM_resEtaPow_split_iff
import Theorems.Thm_GlobalTheory_WeilM_siegelRule_split


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
theorem _root_.solution (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hA : IsHerm (swapA F) JA)
    (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β) (χ : (F × F)ˣ →* Circle) (hc : Continuous χ)
    (hχ : ResEtaPow (⊥ : Subgroup Fˣ) χ (Fintype.card α)) :
    IsUWeilSplit (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) :=
  ⟨isLagr_diagCols _ JB, isUSplitting_splitOm ψ hA hB.dbl _ χ hc,
    siegelRule_split ψ hψ hψ1 hA hB σ χ ((resEtaPow_split_iff _ _).mp hχ)⟩
end GlobalTheory.WeilM
