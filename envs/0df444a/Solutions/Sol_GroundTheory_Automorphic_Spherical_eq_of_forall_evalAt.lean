-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.eq_of_forall_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:18.488871+00:00
-- url     : https://prove2.me/submissions/f9db3470-d6b1-4b6d-a175-d3fed6aac7a2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Theorems.Thm_GroundTheory_Automorphic_Spherical_eq_zero_of_forall_evalAt

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
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {p q : LaurentRing n} (h : ∀ w, evalAt w p = evalAt w q) : p = q :=
  sub_eq_zero.1 (eq_zero_of_forall_evalAt fun w => by rw [map_sub, h, sub_self])
end GroundTheory.Automorphic.Spherical
