-- Prove2me | solution 1 for GlobalTheory.QFam.isobaric_monomial_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:32.639279+00:00
-- url     : https://prove2.me/submissions/d4e15eaa-98c7-438e-9ae7-5fe9281169e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConjEisensteinPolynomialLevelOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]
end GlobalTheory.QFam
