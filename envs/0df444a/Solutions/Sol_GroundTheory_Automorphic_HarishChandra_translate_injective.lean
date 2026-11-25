-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.translate_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:35.620303+00:00
-- url     : https://prove2.me/submissions/8a36aa01-f818-42ab-b4c7-0137fdd578c5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_neg_translate

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
theorem _root_.solution (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) :=
  Function.LeftInverse.injective (translate_neg_translate c)
end GroundTheory.Automorphic.HarishChandra
