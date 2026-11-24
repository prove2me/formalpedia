-- Prove2me | solution 1 for GlobalTheory.QFam.sum_eval_eq_of_sum_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:34.1057+00:00
-- url     : https://prove2.me/submissions/27c5b9cd-1e2f-48e6-b010-3cb9303de32b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMvPolynomialPickPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEq

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
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h d]
end GlobalTheory.QFam
