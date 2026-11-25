-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constFun_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:04:29.299602+00:00
-- url     : https://prove2.me/submissions/3223f80a-50d7-4545-a432-81d7d257b271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
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
theorem _root_.solution (n : ℕ) (φ : (const p O).A (n + 1)) (k : ℕ) :
    constFun p O n ((const p O).res n φ) k = constFun p O (n + 1) φ (p * k : ℕ) := by
  simp only [constFun, CartierDual.addMonoidAlgebraEquiv_apply, ← muT_pow]
  change φ.ofConv ((mu p O).mulP n (muT O (p ^ n) ^ k)) = _
  rw [map_pow, mu_mulP_muT, pow_mul]
end GlobalTheory.PDivGroup
