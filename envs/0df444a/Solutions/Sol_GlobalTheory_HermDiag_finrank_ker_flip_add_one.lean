-- Prove2me | solution 1 for GlobalTheory.HermDiag.finrank_ker_flip_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:31.775831+00:00
-- url     : https://prove2.me/submissions/524ae89f-f435-42a1-960f-b624c4fc5c1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} {x : V} (hx : B x x ≠ 0) :
    finrank E (LinearMap.ker (B.flip x)) + 1 = finrank E V := by
  have hr : LinearMap.range (B.flip x) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨(t / B x x) • x, ?_⟩
    simp [div_mul_cancel₀ _ hx]
  have := LinearMap.finrank_range_add_finrank_ker (B.flip x)
  rw [hr, finrank_top, finrank_self] at this
  omega
end GlobalTheory.HermDiag
