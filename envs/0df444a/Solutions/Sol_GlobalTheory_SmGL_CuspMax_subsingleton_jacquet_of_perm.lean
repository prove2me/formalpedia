-- Prove2me | solution 1 for GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:47.483403+00:00
-- url     : https://prove2.me/submissions/069273d2-c5ec-432f-ba15-13c642df78e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_subsingleton_jacquet_of_conj
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_mem_unipRad_iff_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.CuspMax
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by
  let g : GL n R := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN
  refine mem_unipRad_iff_entries.2 fun i j hij => ?_
  show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id, Equiv.symm_symm]
  rw [mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]
  simp [Matrix.one_apply]
end GlobalTheory.SmGL.CuspMax
