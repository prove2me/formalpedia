-- Prove2me | solution 1 for GroundTheory.GroupCoh.sq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:49.184809+00:00
-- url     : https://prove2.me/submissions/60c67177-bec3-48fb-853d-fd3df0c0229e

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
theorem _root_.solution {C : Type*} [Category C] [Preadditive C] {a₁ a₂ b₁ b₂ : C} {δ₁ : a₁ ⟶ b₁}
    {δ₂ : a₂ ⟶ b₂} (m : ℕ) {f : b₁ ⟶ b₂} {f' : a₁ ⟶ a₂} (h : δ₁ ≫ f = f' ≫ δ₂) :
    δ₁ ≫ (m • f) = (m • f') ≫ δ₂ := by
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, h]
end GroundTheory.GroupCoh
