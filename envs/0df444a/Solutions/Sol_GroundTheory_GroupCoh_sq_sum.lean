-- Prove2me | solution 1 for GroundTheory.GroupCoh.sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:52.793376+00:00
-- url     : https://prove2.me/submissions/7b200fdb-b8a7-450f-8e79-aee95df05ff2

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
    {δ₂ : a₂ ⟶ b₂} {ι : Type*} (s : Finset ι) {f : ι → (b₁ ⟶ b₂)} {f' : ι → (a₁ ⟶ a₂)}
    (h : ∀ i ∈ s, δ₁ ≫ f i = f' i ≫ δ₂) : δ₁ ≫ ∑ i ∈ s, f i = (∑ i ∈ s, f' i) ≫ δ₂ := by
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl h
end GroundTheory.GroupCoh
