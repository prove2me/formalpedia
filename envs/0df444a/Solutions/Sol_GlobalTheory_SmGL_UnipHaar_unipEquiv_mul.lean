-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.unipEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:20.038949+00:00
-- url     : https://prove2.me/submissions/fa669817-22a6-463d-ac7b-edfbb57a1274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_ent_mul_mat

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
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e (u * (unipEquiv e).symm x) =
      unipEquiv e u + (lmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mul_mat]
  show ent e (((u : GL n R) : Matrix n n R) * (1 + mat e x)) = _
  rw [mul_add, mul_one]
  rfl
end GlobalTheory.SmGL.UnipHaar
