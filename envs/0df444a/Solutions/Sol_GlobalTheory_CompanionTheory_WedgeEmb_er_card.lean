-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.er_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:26:44.457439+00:00
-- url     : https://prove2.me/submissions/71b89613-024f-4fcf-b924-34527d4e7ca6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_exists_emb

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
    ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j).card = j := by
  have key : ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j) =
      (Finset.Iio j).map (I.1.orderEmbOfFin I.2).toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ha, hlt⟩
      have ha' : a ∈ I.1 := Finset.mem_of_mem_erase ha
      obtain ⟨i, rfl⟩ := exists_emb I ha'
      exact ⟨i, (I.1.orderEmbOfFin I.2).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hlt := (I.1.orderEmbOfFin I.2).lt_iff_lt.mpr hi
      exact ⟨Finset.mem_erase.mpr ⟨hlt.ne, Finset.orderEmbOfFin_mem _ _ _⟩, hlt⟩
  rw [key, Finset.card_map, Fin.card_Iio]
end GlobalTheory.CompanionTheory.WedgeEmb
