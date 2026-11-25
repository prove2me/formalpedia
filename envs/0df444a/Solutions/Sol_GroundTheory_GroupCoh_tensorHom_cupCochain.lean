-- Prove2me | solution 1 for GroundTheory.GroupCoh.tensorHom_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:35.019799+00:00
-- url     : https://prove2.me/submissions/6e0dc217-009c-434b-9cdd-54372eb3773b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains

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
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ⊗ₘ ψ).hom (cupCochain h f g x) =
      cupCochain h (fun y => φ.hom (f y)) (fun y => ψ.hom (g y)) x := by
  change φ.hom _ ⊗ₜ[k] ψ.hom _ = _
  rw [Rep.hom_comm_apply]
  rfl
end GroundTheory.GroupCoh
