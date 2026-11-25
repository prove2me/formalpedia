-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:03:34.939648+00:00
-- url     : https://prove2.me/submissions/994c85ff-5f64-48a1-b2fc-09fe2d698126

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_er_emb
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_exists_emb
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_jW_er
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_laplace
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeEmb
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.WedgeEmb
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) : jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m := by
  ext ⟨J, t⟩ I
  by_cases ht : t ∈ J.1
  · have hL : (jW n m * cmp (m + 1) g) (J, t) I = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro I'' _
      simp only [jW, ht, not_true_eq_false, false_and, if_false, zero_mul]
    have hl := laplace g (Fin.cons t ⇑(J.1.orderEmbOfFin J.2)) 0 J (by
      funext a
      simp only [Fin.succAbove_zero, Fin.cons_succ]) I
    rw [Fin.cons_zero] at hl
    rw [hL, hl]
    have hr : t ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact ht
    obtain ⟨a, ha⟩ := hr
    rw [Matrix.det_zero_of_row_eq (i := (0 : Fin (m + 1))) (j := a.succ) (Fin.succ_ne_zero a).symm ?_, mul_zero]
    funext c
    simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ, ha]
  · let K : BranchingSupport.Sub n (m + 1) := ⟨insert t J.1, by simp [ht, J.2]⟩
    obtain ⟨i, hi⟩ := exists_emb K (Finset.mem_insert_self t J.1)
    have hJK : er K i = J := by
      apply Subtype.ext
      show K.1.erase (K.1.orderEmbOfFin K.2 i) = J.1
      rw [hi]
      exact Finset.erase_insert ht
    have hl := laplace g ⇑(K.1.orderEmbOfFin K.2) i J (by rw [← hJK]; exact er_emb K i) I
    rw [hi] at hl
    rw [hl, Matrix.mul_apply, Finset.sum_eq_single K]
    · have hp : ((J, t) : BranchingSupport.Sub n m × Fin n) = (er K i, K.1.orderEmbOfFin K.2 i) := by
        rw [hJK, hi]
      rw [hp, jW_er, if_pos rfl]
      rfl
    · intro I'' _ hne
      simp only [jW]
      rw [if_neg (fun h => hne (Subtype.ext h.2)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ K) h
end GlobalTheory.CompanionTheory.WedgeEmb
