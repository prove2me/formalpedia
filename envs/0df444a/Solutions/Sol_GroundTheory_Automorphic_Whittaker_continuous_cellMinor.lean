-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.continuous_cellMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:39.257805+00:00
-- url     : https://prove2.me/submissions/733b0340-27c2-4aee-97c1-3b0326b2660c

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
theorem _root_.solution [TopologicalSpace F] [IsTopologicalRing F]
    (w : Equiv.Perm (Fin n)) : Continuous (cellMinor (F := F) w) :=
  continuous_pi fun _ => (Units.continuous_val.matrix_submatrix _ _).matrix_det
end GroundTheory.Automorphic.Whittaker
