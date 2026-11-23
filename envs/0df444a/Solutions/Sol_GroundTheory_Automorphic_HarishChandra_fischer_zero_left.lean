-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:35.048139+00:00
-- url     : https://prove2.me/submissions/705feef0-0946-4396-b6e0-9396fb8265d4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (g : MvPolynomial σ ℂ) : fischer 0 g = 0 := by simp [fischer]
end GroundTheory.Automorphic.HarishChandra
