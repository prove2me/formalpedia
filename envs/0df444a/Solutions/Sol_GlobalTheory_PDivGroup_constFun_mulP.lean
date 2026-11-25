-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constFun_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:08.506947+00:00
-- url     : https://prove2.me/submissions/18e502df-4edb-4cf9-abf9-8dd49adbfc3d

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
theorem _root_.solution (n : ℕ) (φ : (const p O).A n) (k : ℕ) :
    constFun p O (n + 1) ((const p O).mulP n φ) k = constFun p O n φ k := by
  simp only [constFun, CartierDual.addMonoidAlgebraEquiv_apply, ← muT_pow, dual_mulP]
  change φ.ofConv (muRes p O n (muT O (p ^ (n + 1)) ^ k)) = _
  rw [map_pow, muRes_muT]
end GlobalTheory.PDivGroup
