-- Prove2me | solution 1 for GroundTheory.GroupCoh.isZero_groupHomology_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:38.723701+00:00
-- url     : https://prove2.me/submissions/725ba601-2ea6-43b2-9ed0-831562b4d8ad

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt

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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) :
    IsZero (groupHomology A 1) ↔ ∀ y : G →₀ A, d₁₀ A y = 0 → ∃ c : G × G →₀ A, d₂₁ A c = y := by
  constructor
  · intro h y hy
    have h0 : H1π A ⟨y, LinearMap.mem_ker.mpr hy⟩ = 0 :=
      @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h) _ _
    exact LinearMap.mem_range.mp ((H1π_eq_zero_iff _).mp h0)
  · intro h
    have : Subsingleton (groupHomology A 1) := by
      suffices hz : ∀ z : groupHomology A 1, z = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
      intro z
      induction z using H1_induction_on with
      | h z =>
        apply (H1π_eq_zero_iff z).mpr
        exact LinearMap.mem_range.mpr (h z.1 (LinearMap.mem_ker.mp z.2))
    exact ModuleCat.isZero_of_subsingleton _
end GroundTheory.GroupCoh
