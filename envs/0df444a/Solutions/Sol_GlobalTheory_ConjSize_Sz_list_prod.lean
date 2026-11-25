-- Prove2me | solution 1 for GlobalTheory.ConjSize.Sz.list_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:38.313954+00:00
-- url     : https://prove2.me/submissions/ace485bd-8141-4da8-8d79-ac2eb9c7b8c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_ConjSize_Sz_one
import Theorems.Thm_GlobalTheory_ConjSize_Sz_mul
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
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
theorem _root_.solution {l : List ℂ} (h : ∀ z ∈ l, Sz ι τ z 1) : Sz ι τ l.prod 1 := by
  induction l with
  | nil => exact Sz.one
  | cons a l ih =>
    simpa using (h a List.mem_cons_self).mul (ih fun z hz => h z (List.mem_cons_of_mem _ hz))
end Sz
end GlobalTheory.ConjSize
