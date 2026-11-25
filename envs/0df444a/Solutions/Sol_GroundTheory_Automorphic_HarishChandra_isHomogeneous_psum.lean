-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.isHomogeneous_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:43.848729+00:00
-- url     : https://prove2.me/submissions/7791e26a-1572-477c-9ea4-8c64a5afc7c8

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
theorem _root_.solution (k : ℕ) : (psum (Fin n) ℂ k).IsHomogeneous k := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i k
end GroundTheory.Automorphic.HarishChandra
