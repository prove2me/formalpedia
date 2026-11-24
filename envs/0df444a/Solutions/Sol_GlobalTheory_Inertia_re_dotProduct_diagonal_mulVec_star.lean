-- Prove2me | solution 1 for GlobalTheory.Inertia.re_dotProduct_diagonal_mulVec_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:58.832797+00:00
-- url     : https://prove2.me/submissions/e0f33dc5-07e1-4b45-97fe-ca1b686123d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (d x : n → ℂ) :
    (x ⬝ᵥ diagonal d *ᵥ star x).re = ∑ k, (d k).re * Complex.normSq (x k) := by
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.mul_conj, Complex.re_mul_ofReal]
end GlobalTheory.Inertia
