-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:40.432857+00:00
-- url     : https://prove2.me/submissions/54f4e71b-efcd-4534-8b39-35f8ff6219ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_eq_sum
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
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution [DecidableEq σ] (s t : σ →₀ ℕ) (c d : ℂ) :
    fischer (monomial s c) (monomial t d) = if s = t then (mfact s : ℂ) * star c * d else 0 := by
  rw [fischer_eq_sum _ _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton]
  simp only [coeff_monomial]
  by_cases h : s = t
  · subst h; simp
  · simp [h]
end GroundTheory.Automorphic.HarishChandra
