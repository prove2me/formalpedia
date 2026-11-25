-- Prove2me | solution 1 for GroundTheory.GroupCoh.card_smul_tateCohomology_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:40.862478+00:00
-- url     : https://prove2.me/submissions/83a19068-da47-45f8-b574-615f570f798c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Theorems.Thm_GroundTheory_GroupCoh_norm_apply_of_mem_invariants
import Theorems.Thm_GroundTheory_GroupCoh_mem_normRangeInvariants_iff


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
open CategoryTheory Limits Rep
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} R G) (x : tateCohomology A 0) :
    Fintype.card G • x = 0 := by
  let e := ((tateCohomologyZeroIso R G).app A).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (normRangeInvariants A) (e x)
  rw [← hy]
  have h : (Submodule.Quotient.mk (Fintype.card G • y) :
      A.ρ.invariants ⧸ normRangeInvariants A) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_normRangeInvariants_iff]
    exact ⟨y, by rw [norm_apply_of_mem_invariants A y.2]; rfl⟩
  rw [Submodule.Quotient.mk_smul] at h
  exact h
end GroundTheory.GroupCoh
