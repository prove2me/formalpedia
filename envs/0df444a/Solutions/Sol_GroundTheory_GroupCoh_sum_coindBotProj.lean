-- Prove2me | solution 1 for GroundTheory.GroupCoh.sum_coindBotProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:33.893039+00:00
-- url     : https://prove2.me/submissions/f74bfd5b-c06b-4b02-8fb2-9a9a0f771c2a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced

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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k (⊥ : Subgroup G))
open scoped Classical
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)
end GroundTheory.GroupCoh
