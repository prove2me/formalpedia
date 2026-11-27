-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_tateCohomology_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:07.96193+00:00
-- url     : https://prove2.me/submissions/4f859169-5e82-4ff3-9a29-25aa7c2f252d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_GroundTheory_GroupCoh_coinvariantsKer_le_ker_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) :
    IsZero (tateCohomology M (-1)) ↔ LinearMap.ker M.ρ.norm = Coinvariants.ker M.ρ := by
  rw [((tateCohomologyNegOneIso R G).app M).isZero_iff, ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (LinearMap.ker M.ρ.norm ⧸ augmentationKerNorm M) ↔ _
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h
    refine le_antisymm (fun x hx => ?_) (coinvariantsKer_le_ker_norm M)
    have : (⟨x, hx⟩ : LinearMap.ker M.ρ.norm) ∈ augmentationKerNorm M := h ▸ Submodule.mem_top
    exact this
  · intro h
    refine eq_top_iff.2 (fun x _ => ?_)
    show x.1 ∈ Coinvariants.ker M.ρ
    rw [← h]
    exact x.2
end GroundTheory.GroupCoh
