-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.det_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:48.260004+00:00
-- url     : https://prove2.me/submissions/0fd2a663-2005-460a-93d9-4b82ab137b61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I R) (b : I → α)
    (hM : M.BlockTriangular b) (T : α → Type) [∀ a, Fintype (T a)] [∀ a, DecidableEq (T a)]
    (A : ∀ a, Matrix (m a) (m a) R) (φ : ∀ a, m a × T a ≃ {p // b p = a})
    (h : ∀ a x y, M (φ a x) (φ a y) = if x.2 = y.2 then A a x.1 y.1 else 0) :
    M.det = ∏ a, (A a).det ^ Fintype.card (T a) := by
  rw [hM.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← det_submatrix_equiv_self (φ a)]
  have : (M.toSquareBlock b a).submatrix (φ a) (φ a) = A a ⊗ₖ (1 : Matrix (T a) (T a) R) := by
    ext x y
    refine (h a x y).trans ?_
    simp [kroneckerMap_apply, one_apply]
  rw [this, det_kronecker]
  simp
end GlobalTheory.SmGL.UnipHaar
