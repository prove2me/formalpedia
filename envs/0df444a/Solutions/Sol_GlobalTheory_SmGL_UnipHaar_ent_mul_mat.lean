-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.ent_mul_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:29.701323+00:00
-- url     : https://prove2.me/submissions/4bae0a62-504d-4e1c-a2f8-0c669d94c8c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_sum_idx
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
variable (e : (Σ a, m a) ≃ n)
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (A : Matrix n n R) (x : Idx e → R) :
    ent e (A * mat e x) = (lmat e A).mulVec x := by
  funext p
  refine Eq.trans ?_ (sum_idx e (fun i j => if p.1.2 = j then A p.1.1 i else 0) x).symm
  simp [ent, mul_apply]
end GlobalTheory.SmGL.UnipHaar
