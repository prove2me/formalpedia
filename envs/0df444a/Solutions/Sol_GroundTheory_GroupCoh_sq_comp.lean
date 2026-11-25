-- Prove2me | solution 1 for GroundTheory.GroupCoh.sq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:38.348504+00:00
-- url     : https://prove2.me/submissions/ca60cbc3-7267-40cc-aefb-fd97340ed7fe

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps

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
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C} {δ₁ : a₁ ⟶ b₁} {δ₂ : a₂ ⟶ b₂}
    {δ₃ : a₃ ⟶ b₃} {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} {g : b₂ ⟶ b₃} {g' : a₂ ⟶ a₃}
    (h₁ : δ₁ ≫ f = f' ≫ δ₂) (h₂ : δ₂ ≫ g = g' ≫ δ₃) : δ₁ ≫ (f ≫ g) = (f' ≫ g') ≫ δ₃ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
end GroundTheory.GroupCoh
