-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_H1_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:52.079507+00:00
-- url     : https://prove2.me/submissions/b8db87d0-e096-4b10-92c9-cb1594bcd3b6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
import Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_iso
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
namespace GroundTheory.GroupCoh
theorem _root_.solution {H : Type} [Group H] [Finite H] :
    IsZero (groupCohomology (Rep.trivial ℤ H ℤ) 1) := by
  have : Subsingleton (Additive H →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    have key : ∀ φ : Additive H →+ ℤ, φ x = 0 := fun φ => by
      have h : addOrderOf x • φ x = 0 := by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
      exact (smul_eq_zero.1 h).resolve_left (addOrderOf_pos x).ne'
    rw [key f, key g]⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (H1IsoOfIsTrivial _)
end GroundTheory.GroupCoh
