-- Prove2me | solution 1 for GlobalTheory.PDiv.pow_digit_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:19.968808+00:00
-- url     : https://prove2.me/submissions/7cb8ec49-45e6-4a12-bd44-a048075e28a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_eq
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
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


attribute [local simp] GlobalTheory.PDiv.muChar_muT

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {p : ℕ} [Fact p.Prime] {M : Type*} [Monoid M]
namespace GlobalTheory.PDiv
theorem _root_.solution {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) : x ^ digit n (1 : ℤ_[p]) = x :=
  (pow_digit_eq hx (k := 1) (by simp)).trans (pow_one x)
end GlobalTheory.PDiv
