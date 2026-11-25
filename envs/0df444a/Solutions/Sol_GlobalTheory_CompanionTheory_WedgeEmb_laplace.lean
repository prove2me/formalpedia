-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.laplace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:29:40.988826+00:00
-- url     : https://prove2.me/submissions/7ea6d71d-b7bb-43c2-a0eb-a52490ec0a45

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_er_emb
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_sum_jW

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) (r : Fin (m + 1) → Fin n) (i : Fin (m + 1))
    (J : BranchingSupport.Sub n m) (hJ : ⇑(J.1.orderEmbOfFin J.2) = fun a => r (i.succAbove a)) (I : BranchingSupport.Sub n (m + 1)) :
    ((cmp m g ⊗ₖ g) * jW n m) (J, r i) I =
      (-1) ^ (i : ℕ) * (g.submatrix r (I.1.orderEmbOfFin I.2)).det := by
  rw [Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply]
  have hs := sum_jW (fun p => cmp m g J p.1 * g (r i) p.2) I
  simp only at hs
  rw [hs, Matrix.det_succ_row _ i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd : cmp m g J (er I j) =
      ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det := by
    unfold BranchingSupport.cmp
    rw [hJ, er_emb]
    rfl
  have h2 : ((-1 : ℂ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hd, Matrix.submatrix_apply, pow_add]
  generalize ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det = d
  generalize g (r i) (I.1.orderEmbOfFin I.2 j) = x
  linear_combination (-(-1 : ℂ) ^ (j : ℕ) * d * x) * h2
end GlobalTheory.CompanionTheory.WedgeEmb
