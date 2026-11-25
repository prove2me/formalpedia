-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.monomial_const_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:43.983492+00:00
-- url     : https://prove2.me/submissions/769e5ccc-b872-4cf7-84e2-bf41b2f52099

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
theorem _root_.solution (c : ℤ) : monomial (fun _ : Fin n => c) ∈ symmetricLaurent n := by
  intro σ
  rw [permAct_single]
  rfl
end GroundTheory.Automorphic.Spherical
