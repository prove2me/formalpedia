-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:36.041167+00:00
-- url     : https://prove2.me/submissions/25a0ead7-d91d-4101-b024-2f790656d71b

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
theorem _root_.solution (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by
  simp only [fischer, coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]
end GroundTheory.Automorphic.HarishChandra
