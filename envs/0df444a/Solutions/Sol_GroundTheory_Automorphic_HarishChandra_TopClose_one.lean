-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.TopClose.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:44.86056+00:00
-- url     : https://prove2.me/submissions/7aa6300a-4b36-44c8-9dd2-50a724a82a4d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
namespace TopClose
theorem _root_.solution : TopClose (n := n) 0 1 1 := by
  refine ⟨by simp, by simp, Or.inl rfl⟩
end TopClose
end GroundTheory.Automorphic.HarishChandra
