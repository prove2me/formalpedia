-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:09.706123+00:00
-- url     : https://prove2.me/submissions/279f3eed-a5d4-426c-8f07-70c25730e3d3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_bruhatCell
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff

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
theorem _root_.solution {a b : GL (Fin n) F} (ha : a ∈ borel n F) (hb : b ∈ borel n F)
    (g : GL (Fin n) F) : bruhatCell (a * g * b) = bruhatCell g := by
  rw [bruhatCell_eq_iff]
  obtain ⟨x, hx, y, hy, hg⟩ := mem_doubleCoset.1 (mem_doubleCoset_bruhatCell g)
  refine mem_doubleCoset.2 ⟨a * x, (borel n F).mul_mem ha hx, y * b, (borel n F).mul_mem hy hb, ?_⟩
  calc a * g * b = a * (x * permGL F (bruhatCell g) * y) * b := by rw [← hg]
    _ = a * x * permGL F (bruhatCell g) * (y * b) := by group
end GroundTheory.Automorphic.Whittaker
