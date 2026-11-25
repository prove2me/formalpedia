-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.coeff_rowOp_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:52.666998+00:00
-- url     : https://prove2.me/submissions/3b077fee-e041-4122-81dc-bf5aa34028e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_self_monomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (i : Fin n) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (rowOp i i f) = (rowWt m i : ℂ) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial s c =>
    rw [rowOp_self_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m
    · subst h; simp [mul_comm]
    · simp [h]
end GroundTheory.Automorphic.HarishChandra
