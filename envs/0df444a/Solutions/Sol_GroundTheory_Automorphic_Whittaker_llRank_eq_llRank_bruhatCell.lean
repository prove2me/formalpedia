-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.llRank_eq_llRank_bruhatCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:19.421388+00:00
-- url     : https://prove2.me/submissions/48a5f82e-0f09-499c-8074-405cbdf68cea

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_mul_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_bruhatCell

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
theorem _root_.solution (i j : Fin n) (g : GL (Fin n) F) :
    llRank i j g = llRank i j (permGL F (bruhatCell g)) := by
  obtain ⟨x, hx, y, hy, hg⟩ := mem_doubleCoset.1 (mem_doubleCoset_bruhatCell g)
  conv_lhs => rw [hg]
  exact llRank_mul_mul hx hy i j _
end GroundTheory.Automorphic.Whittaker
