-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_monomial_term_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:43.406804+00:00
-- url     : https://prove2.me/submissions/003cc6c3-1735-4795-905c-9c13a223b421

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero

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
theorem _root_.solution {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (c : ℂ)
    (P : Submodule ℂ (Poly n))
    (h : s (j, k) ≠ 0 → (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1))
        (c * s (j, k)) : Poly n) ∈ P) :
    (monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) : Poly n)
      ∈ P := by
  by_cases hs : s (j, k) = 0
  · rw [hs, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
  · exact h hs
end GroundTheory.Automorphic.HarishChandra
