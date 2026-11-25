-- Prove2me | solution 1 for GlobalTheory.PDivGroup.exact_rigOfOmega_rigToExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:59.177872+00:00
-- url     : https://prove2.me/submissions/0e461b14-4b41-4c94-9713-07c7e2d4029c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
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
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution : Function.Exact G.rigOfOmega G.rigToExt := fun x => by
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro h
    obtain ⟨b, rfl⟩ : c ∈ LinearMap.range G.cob := (Submodule.Quotient.mk_eq_zero _).1 h
    refine ⟨w - G.dFun b, Eq.symm ((Submodule.Quotient.eq _).2 (LinearMap.mem_range.2 ⟨b, ?_⟩))⟩
    simp
  · rintro ⟨w', h⟩
    rw [← h]
    exact (Submodule.Quotient.mk_eq_zero _).2 (zero_mem _)
end GlobalTheory.PDivGroup
