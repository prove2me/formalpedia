-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.natToInt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:27.226263+00:00
-- url     : https://prove2.me/submissions/f2f2a9c1-70b6-4e24-b0a9-31d4aab83277

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
theorem _root_.solution : Function.Injective (natToInt (n := n)) := fun s t h => by
  ext i
  exact Int.ofNat_inj.1 (congrFun h i)
end GroundTheory.Automorphic.Spherical
