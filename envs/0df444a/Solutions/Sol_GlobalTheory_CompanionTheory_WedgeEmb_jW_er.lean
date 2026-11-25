-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.jW_er
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:25.662671+00:00
-- url     : https://prove2.me/submissions/48e59150-d0f8-4b1d-9cea-18aff4da892a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_er_card

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
theorem _root_.solution (I I' : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    jW n m (er I j, I.1.orderEmbOfFin I.2 j) I' = if I' = I then (-1) ^ (j : ℕ) else 0 := by
  have h1 : I.1.orderEmbOfFin I.2 j ∉ (er I j).1 := by simp [er]
  have h2 : insert (I.1.orderEmbOfFin I.2 j) (er I j).1 = I.1 :=
    Finset.insert_erase (Finset.orderEmbOfFin_mem _ _ _)
  simp only [jW, h1, not_false_eq_true, true_and, h2, er_card]
  by_cases hI : I' = I
  · subst hI
    simp
  · rw [if_neg (fun h => hI (Subtype.ext h)), if_neg hI]
end GlobalTheory.CompanionTheory.WedgeEmb
