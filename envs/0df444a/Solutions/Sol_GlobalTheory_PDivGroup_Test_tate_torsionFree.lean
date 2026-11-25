-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.tate_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:04:25.630427+00:00
-- url     : https://prove2.me/submissions/601da41f-c21d-4927-85f2-13253fd2bad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_succ_pow
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT



set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] (G : PDivGroup p O) {B : Type} [CommRing B] [Algebra O B]
    (x : G.TateOver B) (h : (p : ℤ_[p]) • x = 0) : x = 0 := TateOver.ext_conv fun n => by
  have h1 := congrArg (fun y => TateOver.conv y (n + 1)) h
  simp only [TateOver.smul_conv, TateOver.zero_conv] at h1
  rw [pow_digit_natCast (G.pts_pow_self _ _), TateOver.conv_succ_pow] at h1
  refine ofConv_injective (AlgHom.ext fun a => ?_)
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  have h3 := DFunLike.congr_fun (congrArg ofConv h1) b
  refine h3.trans ?_
  change algebraMap O B (counit b) = algebraMap O B (counit (G.res n b))
  rw [CoalgHomClass.counit_comp_apply]
end GlobalTheory.PDivGroup.Test
