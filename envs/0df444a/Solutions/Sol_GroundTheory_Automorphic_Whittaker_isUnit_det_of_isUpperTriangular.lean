-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isUnit_det_of_isUpperTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:48.947854+00:00
-- url     : https://prove2.me/submissions/eae9d6c4-dbb5-431e-a387-578227dea8ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells

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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {X : Matrix (Fin n) (Fin n) F} (hX : X.IsUpperTriangular)
    (hd : ∀ r, X r r ≠ 0) : IsUnit X.det := by
  rw [det_of_isUpperTriangular hX, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun r _ => hd r
end GroundTheory.Automorphic.Whittaker
