-- Prove2me | solution 1 for GroundTheory.GroupCoh.resTensorHom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:58.734164+00:00
-- url     : https://prove2.me/submissions/2eadcf51-9ac8-4829-908e-11cb592000d8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupFunctorial

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
theorem _root_.solution (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl
end GroundTheory.GroupCoh
