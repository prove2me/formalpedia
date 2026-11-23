-- Prove2me | solution 1 for GroundTheory.GroupCoh.finite_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:01.896552+00:00
-- url     : https://prove2.me/submissions/5508f6f9-cf9a-4f53-b67e-f67378002e44

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_natCard_eq_ker_mul_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
namespace GroundTheory.GroupCoh
theorem _root_.solution {X Y Z : Type*} [AddGroup X] [AddGroup Y] [AddGroup Z]
    (d : X →+ Y) (e : Y →+ Z) (h : e.ker = d.range) [Finite X] [Finite Z] : Finite Y := by
  have h1 : Finite d.range := Finite.of_surjective _ d.rangeRestrict_surjective
  have h2 : Finite e.ker := by rw [h]; exact h1
  apply Nat.finite_of_card_ne_zero
  rw [natCard_eq_ker_mul_range e]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
end GroundTheory.GroupCoh
