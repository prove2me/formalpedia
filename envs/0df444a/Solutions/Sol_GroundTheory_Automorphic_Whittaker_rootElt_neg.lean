-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rootElt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:06.955733+00:00
-- url     : https://prove2.me/submissions/36e59adf-e503-4eb2-8305-7991fc59b5dc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (i j : Fin n) (a : F) : rootElt i j (-a) = (rootElt i j a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rootElt_add, neg_add_cancel, rootElt_zero])
end GroundTheory.Automorphic.Whittaker
