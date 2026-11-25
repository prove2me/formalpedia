-- Prove2me | solution 1 for GroundTheory.GroupCoh.herbrandQuotient_eq_one_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:18.295797+00:00
-- url     : https://prove2.me/submissions/499eee9e-b61b-4efe-bc17-62e9f7ce9ed2

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_natCard_kerModRange_eq_of_finite

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
    (hgf : ∀ x, g (f x) = 0) : herbrandQuotient f g = 1 := by
  have hq : 0 < Nat.card (KerModRange g f) := Nat.card_pos
  rw [herbrandQuotient, natCard_kerModRange_eq_of_finite hfg hgf, div_self]
  exact_mod_cast hq.ne'
end GroundTheory.GroupCoh
