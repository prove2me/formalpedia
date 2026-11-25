-- Prove2me | solution 1 for GlobalTheory.ConjSize.sz_apow_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:41.442364+00:00
-- url     : https://prove2.me/submissions/9dfab11a-d7e1-48f7-9428-78a477504f0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_ConjSize_sz_apow_nat_half
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_le_one
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.ConjSize
theorem _root_.solution (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) (hu : valuation k (u : k) ≤ 1) :
    Sz ι τ (apow u ((n : ℂ) / 2)) 1 := by
  borelize k
  simpa using sz_apow_nat_half (τ := τ) u h n le_rfl (GlobalTheory.SplitWeil.Model.nabs_le_one u hu)
end GlobalTheory.ConjSize
