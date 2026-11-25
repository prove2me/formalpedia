-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.orbitSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:51.186155+00:00
-- url     : https://prove2.me/submissions/5918d884-cd5a-4b86-8f08-28a8f9b53516

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (ν : Fin n → ℤ) : orbitSum ν ∈ symmetricLaurent n := by
  intro τ
  rw [orbitSum, map_sum]
  simp only [permAct_single]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by congr 1
end GroundTheory.Automorphic.Spherical
