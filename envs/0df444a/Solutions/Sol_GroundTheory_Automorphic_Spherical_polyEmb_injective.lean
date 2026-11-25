-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.polyEmb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:37.885681+00:00
-- url     : https://prove2.me/submissions/3523aac5-4a19-49cc-a92c-ec0d9168c0a8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_natToInt_injective

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
theorem _root_.solution : Function.Injective (polyEmb n) :=
  mapDomain_injective natToInt_injective
end GroundTheory.Automorphic.Spherical
