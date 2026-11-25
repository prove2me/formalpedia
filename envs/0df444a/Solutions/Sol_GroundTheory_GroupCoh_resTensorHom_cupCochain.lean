-- Prove2me | solution 1 for GroundTheory.GroupCoh.resTensorHom_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:56.436095+00:00
-- url     : https://prove2.me/submissions/d1c4c4b9-944a-41a6-a7f8-bfaaf5185f6b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupFunctorial
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_comp
import Theorems.Thm_GroundTheory_GroupCoh_resTensorHom_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)
end GroundTheory.GroupCoh
