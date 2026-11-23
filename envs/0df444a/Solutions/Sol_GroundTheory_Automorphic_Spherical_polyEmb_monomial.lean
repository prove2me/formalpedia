-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.polyEmb_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:55.81523+00:00
-- url     : https://prove2.me/submissions/1e2c155e-05f4-4113-b449-85f0a3524162

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric

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
theorem _root_.solution (s : Fin n →₀ ℕ) (c : ℂ) :
    polyEmb n (MvPolynomial.monomial s c) = single (natToInt s) c := by
  simp [polyEmb, mapDomainAlgHom, MvPolynomial.monomial, mapDomain_single]
end GroundTheory.Automorphic.Spherical
