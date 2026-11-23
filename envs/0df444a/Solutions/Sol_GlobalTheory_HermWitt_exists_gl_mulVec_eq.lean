-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:58.005025+00:00
-- url     : https://prove2.me/submissions/74f9c03a-41d4-4332-b6be-c96282c9b311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution (γ : (n → E) ≃ₗ[E] (n → E)) :
    ∃ g : GL n E, ∀ x, (g : Matrix n n E) *ᵥ x = γ x :=
  ⟨⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩,
    fun x => by simp [← Matrix.toLin'_apply]⟩
end GlobalTheory.HermWitt
