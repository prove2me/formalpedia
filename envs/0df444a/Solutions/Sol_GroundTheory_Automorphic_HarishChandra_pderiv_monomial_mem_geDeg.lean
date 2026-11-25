-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.pderiv_monomial_mem_geDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:39.36641+00:00
-- url     : https://prove2.me/submissions/c7f83f52-2221-4412-b432-32701f05276c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_sub_single

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
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {t : ℕ} (a : Fin n × Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : pderiv a (monomial s c : Poly n) ∈ geDeg (t - 1) := by
  rw [pderiv_monomial]
  by_cases hs : s a = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · apply monomial_mem_geDeg
    have := degree_sub_single hs
    omega
end GroundTheory.Automorphic.HarishChandra
