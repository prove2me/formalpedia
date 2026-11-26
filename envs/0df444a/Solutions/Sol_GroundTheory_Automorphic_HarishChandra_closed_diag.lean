-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.closed_diag
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:24:52.018132+00:00
-- url     : https://prove2.me/submissions/3d5434e3-6630-461e-a74a-40e26b2e534d

import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
theorem _root_.solution : Closed (IsDiag (n := n)) := by
  first
    | (intros; simp [Closed, IsDiag])
    | (intros; unfold Closed IsDiag; simp)
    | (intros; simp [Closed, IsDiag]; done)
    | (intros; ext; simp [Closed, IsDiag])
    | (intros; simp only [Closed, IsDiag]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Closed, IsDiag])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Closed, IsDiag])
    | (intros; unfold Closed IsDiag; split_ifs <;> simp_all)
    | (intros; unfold Closed IsDiag; positivity)
    | (intros; unfold Closed IsDiag; ring)
    | (intros; unfold Closed IsDiag; exact?)
    | (intros; aesop (add norm simp [Closed, IsDiag]))
    | (intros; simp [Closed, IsDiag] <;> aesop)
    | (intros; exact Closed.symm ..)
    | (intros; exact Closed.comm ..)
    | (intros; exact IsDiag.symm ..)
    | (intros; exact IsDiag.comm ..)
  trace "HIT_45_0"

