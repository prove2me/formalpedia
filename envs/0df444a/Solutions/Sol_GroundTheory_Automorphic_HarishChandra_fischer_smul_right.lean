-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:42.498517+00:00
-- url     : https://prove2.me/submissions/e15433d1-396a-4dc4-9dda-6711e5dd023d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_eq_sum

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
    fischer f (c • g) = c * fischer f g := by
  rw [fischer_eq_sum f (c • g) g.support (MvPolynomial.support_smul), fischer, Finset.mul_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring
end GroundTheory.Automorphic.HarishChandra
