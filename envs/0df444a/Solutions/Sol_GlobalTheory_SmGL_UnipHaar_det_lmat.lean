-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.det_lmat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:35.760738+00:00
-- url     : https://prove2.me/submissions/78c6491c-289f-426b-b1ed-ed87f460516a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_of_blocks
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_card_blk

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
theorem _root_.solution {A : Matrix n n R} (hA : A.BlockTriangular (blk e)) (D : ∀ a, Matrix (m a) (m a) R)
    (hD : ∀ a i j, A (e ⟨a, i⟩) (e ⟨a, j⟩) = D a i j) :
    (lmat e A).det = ∏ a, (D a).det ^ ∑ b with a < b, Fintype.card (m b) := by
  rw [det_of_blocks (lmat e A) (fun p => blk e p.1.1) ?_ (fun a => {j : n // a < blk e j}) D
    (rowEquiv e) ?_]
  · simp only [card_blk]
  · intro p q h
    simp [lmat, hA h]
  · intro a x y
    exact if_congr Subtype.ext_iff.symm (hD a x.1 y.1) rfl
end GlobalTheory.SmGL.UnipHaar
