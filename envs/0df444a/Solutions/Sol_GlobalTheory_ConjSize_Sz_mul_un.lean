-- Prove2me | solution 1 for GlobalTheory.ConjSize.Sz.mul_un
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:43.548726+00:00
-- url     : https://prove2.me/submissions/187896e7-7cf9-45dc-b754-20a1388755e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_ConjSize_Sz_mul
import Theorems.Thm_GlobalTheory_ConjSize_Un_sz
import Theorems.Thm_GlobalTheory_ConjSize_Un_mul
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
theorem _root_.solution {z z' : ℂ} {B : ℝ} (h : Sz ι τ z B) (h' : Un ι τ z') : Sz ι τ (z * z') B := by
  simpa using h.mul h'.sz
end Sz
end GlobalTheory.ConjSize
