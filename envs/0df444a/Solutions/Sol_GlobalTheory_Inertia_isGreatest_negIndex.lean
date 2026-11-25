-- Prove2me | solution 1 for GlobalTheory.Inertia.isGreatest_negIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:48.394173+00:00
-- url     : https://prove2.me/submissions/899c3dd3-2942-4cdf-b53e-f1c400f03b65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
namespace GlobalTheory.Inertia
theorem _root_.solution (G : Matrix n n ℂ) :
    IsGreatest {d | ∃ W : Submodule ℂ (n → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ G *ᵥ star x).re < 0} (negIndex G) := by
  have h := isGreatest_posIndex (-G)
  simpa only [negIndex, posDims, neg_mulVec, dotProduct_neg, Complex.neg_re, Left.neg_pos_iff] using h
end GlobalTheory.Inertia
