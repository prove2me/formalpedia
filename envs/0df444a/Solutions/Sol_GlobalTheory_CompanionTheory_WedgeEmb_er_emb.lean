-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.er_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:02.636153+00:00
-- url     : https://prove2.me/submissions/d1507dc3-e3a0-4d76-a524-80af59ab9239

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
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
theorem _root_.solution (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ⇑((er I j).1.orderEmbOfFin (er I j).2) = fun a => I.1.orderEmbOfFin I.2 (j.succAbove a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    show _ ∈ I.1.erase _
    rw [Finset.mem_erase]
    exact ⟨fun h => Fin.succAbove_ne j a ((I.1.orderEmbOfFin I.2).injective h), Finset.orderEmbOfFin_mem _ _ _⟩
  · exact (I.1.orderEmbOfFin I.2).strictMono.comp (Fin.strictMono_succAbove j)
end GlobalTheory.CompanionTheory.WedgeEmb
