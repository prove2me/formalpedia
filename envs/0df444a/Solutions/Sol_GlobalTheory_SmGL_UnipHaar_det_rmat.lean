-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.det_rmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:27.264831+00:00
-- url     : https://prove2.me/submissions/70773960-6cd5-4c2e-bf1d-b8beaf8a203b

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
theorem _root_.solution (g : Levi R m) :
    (rmat e (leviEmb R e g : Matrix n n R)).det =
      ∏ a, (g a : Matrix (m a) (m a) R).det ^ ∑ b with b < a, Fintype.card (m b) := by
  rw [det_of_blocks (rmat e _) (fun p => blk e p.1.2) ?_ (fun a => {j : n // blk e j < a})
    (fun a => (g a : Matrix (m a) (m a) R)ᵀ) (colEquiv e) ?_]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [card_blk e (· < a), det_transpose]
  · rintro ⟨⟨i, j⟩, _⟩ ⟨⟨i', j'⟩, _⟩ h
    obtain ⟨⟨a, j⟩, rfl⟩ := e.surjective j
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j'
    have : b < a := by simpa using h
    simp [rmat, leviEmb_apply_ne R e g this.ne]
  · intro a x y
    exact if_congr Subtype.ext_iff.symm (leviEmb_apply_same R e g a y.1 x.1) rfl
end GlobalTheory.SmGL.UnipHaar
