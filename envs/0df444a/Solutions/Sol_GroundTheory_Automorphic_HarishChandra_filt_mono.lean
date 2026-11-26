-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.filt_mono
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:50:00.025135+00:00
-- url     : https://prove2.me/submissions/716ff122-01b1-428e-9050-3b6837510ec6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
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
theorem _root_.solution {d d' : ℕ} (h : d ≤ d') : filt (n := n) d ≤ filt d' := by
  first
    | (unfold GroundTheory.Automorphic.HarishChandra.filt
       exact Submodule.span_mono (by
         rintro x ⟨l, hl, rfl⟩
         exact ⟨l, le_trans hl h, rfl⟩))
    | (unfold GroundTheory.Automorphic.HarishChandra.filt
       refine Submodule.span_mono fun x hx => ?_
       obtain ⟨l, hl, e⟩ := hx
       exact ⟨l, le_trans hl h, e⟩)
    | (exact monotone_nat_of_le_succ (fun n => by unfold GroundTheory.Automorphic.HarishChandra.filt; exact le_sup_left) h)

