-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.llRank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:33.155641+00:00
-- url     : https://prove2.me/submissions/db56aba2-a686-4e08-84df-287afdc7ae91

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
theorem _root_.solution (i j : Fin n) (g : GL (Fin n) F) : llRank i j g ≤ n := by
  have := rank_le_card_width (rowsFrom i * (g : Matrix (Fin n) (Fin n) F) * colsTo j)
  rwa [Fintype.card_fin] at this
end GroundTheory.Automorphic.Whittaker
