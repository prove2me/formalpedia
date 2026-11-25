-- Prove2me | solution 1 for GlobalTheory.PDivGroup.toSpanSingleton_constGen_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:50.491059+00:00
-- url     : https://prove2.me/submissions/06e269c0-811c-4404-85da-906305da9822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_smul_constGen_pt
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
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
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (p O) [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution [Nontrivial O] :
    Function.Injective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := fun a b h => by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  have h1 := congrArg (fun t : (const p O).Tate =>
    t.pt n ((constFun p O n).symm (Pi.single (PadicInt.toZModPow n b) 1))) h
  simp only [LinearMap.toSpanSingleton_apply] at h1
  rw [smul_constGen_pt, smul_constGen_pt, AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h1
  by_contra hne
  rw [Pi.single_eq_of_ne hne] at h1
  exact zero_ne_one h1
end GlobalTheory.PDivGroup
