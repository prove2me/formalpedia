-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.mem_symmetricLaurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:40.670797+00:00
-- url     : https://prove2.me/submissions/0d13c371-e36d-44c3-8b10-f253575d9f4c

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
theorem _root_.solution {p : LaurentRing n} :
    p ∈ symmetricLaurent n ↔ ∀ σ, permAct σ p = p :=
  Iff.rfl
end GroundTheory.Automorphic.Spherical
