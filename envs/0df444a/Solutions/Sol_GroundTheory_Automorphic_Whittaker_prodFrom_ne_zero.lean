-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.prodFrom_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:59.256054+00:00
-- url     : https://prove2.me/submissions/70ea8345-4746-4013-bd3a-58cad703492b

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
theorem _root_.solution (t : Fin n → Fˣ) (s : ℕ) : prodFrom t s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun x _ => (t x).ne_zero
end GroundTheory.Automorphic.Whittaker
