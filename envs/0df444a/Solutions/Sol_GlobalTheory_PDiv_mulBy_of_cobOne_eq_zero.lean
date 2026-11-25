-- Prove2me | solution 1 for GlobalTheory.PDiv.mulBy_of_cobOne_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:34.089886+00:00
-- url     : https://prove2.me/submissions/d9b3c159-90dc-4012-8e88-9ee4861599e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsPrimitiveElem_counit_eq_zero
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts
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
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDiv
variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]
namespace GlobalTheory.PDiv
theorem _root_.solution [IsCocomm O A] {b : A} (hb : cobOne O A b = 0) (k : ℕ) :
    mulBy O A k b = k • b ∧ counit (R := O) b = 0 := by
  have hp : IsPrimitiveElem O b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨?_, hp.counit_eq_zero⟩
  have key : ∀ k : ℕ, (WithConv.toConv (AlgHom.id O A) ^ k) b = k • b := fun k => by
    induction k with
    | zero => simp [hp.counit_eq_zero]
    | succ k ih =>
      rw [pow_succ, AlgHom.convMul_apply, show comul b = _ from hp, succ_nsmul, ← ih]
      simp
  exact (DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O A) k) b).trans (key k)
end GlobalTheory.PDiv
