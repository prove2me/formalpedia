-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:41.80286+00:00
-- url     : https://prove2.me/submissions/a05a33f6-3f12-424d-b57a-269939e53763

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
theorem _root_.solution (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by
  simp only [fischer, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
end GroundTheory.Automorphic.HarishChandra
