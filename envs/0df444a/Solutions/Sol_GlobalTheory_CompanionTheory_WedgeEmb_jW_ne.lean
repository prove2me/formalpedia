-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.jW_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:31:08.974866+00:00
-- url     : https://prove2.me/submissions/9cbb5df5-bb89-4fd5-9f9d-15b4f19013d5

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_exists_emb
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
theorem _root_.solution (p : BranchingSupport.Sub n m × Fin n) (I : BranchingSupport.Sub n (m + 1)) (h : jW n m p I ≠ 0) :
    ∃ j, (er I j, I.1.orderEmbOfFin I.2 j) = p := by
  obtain ⟨J, t⟩ := p
  simp only [jW] at h
  by_cases hc : t ∉ J.1 ∧ I.1 = insert t J.1
  · have htI : t ∈ I.1 := by
      rw [hc.2]
      exact Finset.mem_insert_self t J.1
    obtain ⟨j, hj⟩ := exists_emb I htI
    refine ⟨j, ?_⟩
    rw [hj]
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    show I.1.erase (I.1.orderEmbOfFin I.2 j) = J.1
    rw [hj, hc.2, Finset.erase_insert hc.1]
  · exact (h (if_neg hc)).elim
end GlobalTheory.CompanionTheory.WedgeEmb
