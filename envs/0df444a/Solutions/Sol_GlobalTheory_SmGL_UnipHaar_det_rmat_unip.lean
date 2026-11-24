-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.det_rmat_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:04.880805+00:00
-- url     : https://prove2.me/submissions/207fa207-2ec1-4a3f-a8b5-e57f40140748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarIsMulRightInvariant
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_of_blocks
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (u : unipRad R e) : (rmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 u.2
  rw [← det_transpose, det_of_blocks (rmat e _)ᵀ (fun p => blk e p.1.2) ?_
    (fun a => {j : n // blk e j < a}) (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    have h3 : ((u : GL n R) : Matrix n n R).BlockTriangular (blk e) := h1
    simp [rmat, h3 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) (h2 a x.1 y.1) rfl
end GlobalTheory.SmGL.UnipHaar
