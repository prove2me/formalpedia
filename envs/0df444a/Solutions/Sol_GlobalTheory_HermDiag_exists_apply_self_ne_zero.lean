-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_apply_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:46.144724+00:00
-- url     : https://prove2.me/submissions/2eb49513-d57e-4ee6-8cb7-14e059e13a88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_eq_zero_of_apply_self_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E}
namespace GlobalTheory.HermDiag
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module E V]
    (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hne : B ≠ 0) : ∃ x, B x x ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (eq_zero_of_apply_self_eq_zero h2 hB h)
end GlobalTheory.HermDiag
