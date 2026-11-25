-- Prove2me | solution 1 for GlobalTheory.ConjSize.Sz.sum_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:49.06749+00:00
-- url     : https://prove2.me/submissions/de121d84-edd9-4015-bc43-b371794f939e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_ConjSize_Sz_sum
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
variable {ι τ}
namespace GlobalTheory.ConjSize
namespace Sz
theorem _root_.solution {α : Type*} (s : Finset α) {f : α → ℂ} {B : ℝ} (h : ∀ i ∈ s, Sz ι τ (f i) B) :
    Sz ι τ (∑ i ∈ s, f i) (s.card * B) := by
  simpa using Sz.sum s h
end Sz
end GlobalTheory.ConjSize
