-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rowsFrom_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:43.566959+00:00
-- url     : https://prove2.me/submissions/569a92fb-20a1-4767-bce3-96909b32f6ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (i : Fin n) :
    rowsFrom i * rowsFrom i = (rowsFrom i : Matrix (Fin n) (Fin n) F) := by
  simp only [rowsFrom, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp
end GroundTheory.Automorphic.Whittaker
