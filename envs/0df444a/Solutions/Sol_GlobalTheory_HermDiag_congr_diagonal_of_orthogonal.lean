-- Prove2me | solution 1 for GlobalTheory.HermDiag.congr_diagonal_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.655335+00:00
-- url     : https://prove2.me/submissions/6494f412-46b6-4fe1-b725-6ef73ad4462f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_transpose_mul_mul_map_apply

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
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.HermDiag
theorem _root_.solution {G : Matrix n n E} (c : E → E) (v : n → n → E)
    (hv : ∀ i j, i ≠ j → v i ⬝ᵥ G *ᵥ (c ∘ v j) = 0) :
    (Matrix.of fun k i => v i k)ᵀ * G * (Matrix.of fun k i => v i k).map c =
      Matrix.diagonal fun i => v i ⬝ᵥ G *ᵥ (c ∘ v i) := by
  ext i j
  rw [transpose_mul_mul_map_apply]
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq]
    rfl
  · rw [diagonal_apply_ne _ hij]
    exact hv i j hij
end GlobalTheory.HermDiag
