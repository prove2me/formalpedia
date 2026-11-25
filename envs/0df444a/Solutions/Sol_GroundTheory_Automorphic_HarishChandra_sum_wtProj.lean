-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.sum_wtProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:09.602049+00:00
-- url     : https://prove2.me/submissions/b4609877-abdc-403a-acc0-eed0f874eef7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj
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
theorem _root_.solution (f : Poly n) : ∑ ν ∈ f.support.image rowWt, wtProj ν f = f := by
  classical
  ext m
  rw [coeff_sum]
  simp only [coeff_wtProj, Finset.sum_ite_eq, Finset.mem_image]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h ⟨m, MvPolynomial.mem_support_iff.2 (Ne.symm hc), rfl⟩
end GroundTheory.Automorphic.HarishChandra
