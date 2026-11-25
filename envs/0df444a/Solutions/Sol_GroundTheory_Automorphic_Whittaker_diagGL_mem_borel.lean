-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.diagGL_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:47.122292+00:00
-- url     : https://prove2.me/submissions/7e6a1c17-ddd3-4512-a05c-a4f21768d984

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
theorem _root_.solution (t : Fin n → Fˣ) : Iwasawa.diagGL F n t ∈ borel n F := by
  show ((Iwasawa.diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsUpperTriangular
  rw [Iwasawa.coe_diagGL]
  exact blockTriangular_diagonal _
end GroundTheory.Automorphic.Whittaker
