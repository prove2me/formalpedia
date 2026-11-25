-- Prove2me | solution 1 for GroundTheory.GroupCoh.natCard_kerModRange_eq_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:41.646197+00:00
-- url     : https://prove2.me/submissions/9b7d2c2d-a0df-495a-b26f-3ddfca7af861

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_natCard_eq_ker_mul_range
import Theorems.Thm_GroundTheory_GroupCoh_natCard_ker_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : Nat.card (KerModRange f g) = Nat.card (KerModRange g f) := by
  have h1 := natCard_ker_eq hfg
  have h2 := natCard_ker_eq hgf
  have h3 := natCard_eq_ker_mul_range f
  have h4 := natCard_eq_ker_mul_range g
  have hf : 0 < Nat.card f.range := Nat.card_pos
  have hg : 0 < Nat.card g.range := Nat.card_pos
  have key : Nat.card (KerModRange f g) * (Nat.card g.range * Nat.card f.range) =
      Nat.card (KerModRange g f) * (Nat.card g.range * Nat.card f.range) := by
    calc _ = Nat.card f.ker * Nat.card f.range := by rw [h1]; ring
      _ = Nat.card g.ker * Nat.card g.range := by rw [← h3, ← h4]
      _ = _ := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg hf) key
end GroundTheory.GroupCoh
