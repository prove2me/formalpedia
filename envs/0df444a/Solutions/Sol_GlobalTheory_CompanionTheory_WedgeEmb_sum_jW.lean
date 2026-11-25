-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.sum_jW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:50.57183+00:00
-- url     : https://prove2.me/submissions/129925dd-48d7-4b30-b0fa-9c956ba1a38e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_jW_er
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_jW_ne

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
theorem _root_.solution (F : BranchingSupport.Sub n m × Fin n → ℂ) (I : BranchingSupport.Sub n (m + 1)) :
    ∑ p, F p * jW n m p I = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * F (er I j, I.1.orderEmbOfFin I.2 j) := by
  have hq : Function.Injective (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)) :=
    fun a b hab => (I.1.orderEmbOfFin I.2).injective (congrArg Prod.snd hab)
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)))) ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => hq hab)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [jW_er, if_pos rfl, mul_comm]
  · intro p _ hp
    by_contra hne
    obtain ⟨j, hj⟩ := jW_ne p I (right_ne_zero_of_mul hne)
    exact hp (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
end GlobalTheory.CompanionTheory.WedgeEmb
