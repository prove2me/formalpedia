-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.exists_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:39.882253+00:00
-- url     : https://prove2.me/submissions/bb80995c-9a19-45c0-8632-1571be2deb34

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality

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
theorem _root_.solution (I : BranchingSupport.Sub n (m + 1)) {t : Fin n} (ht : t ∈ I.1) : ∃ j, I.1.orderEmbOfFin I.2 j = t := by
  have h : t ∈ Set.range (I.1.orderEmbOfFin I.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact ht
  exact h
end GlobalTheory.CompanionTheory.WedgeEmb
