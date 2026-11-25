-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.colsTo_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:30.137887+00:00
-- url     : https://prove2.me/submissions/1c8e2e32-e05f-4920-9aae-248389a4fbd6

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
theorem _root_.solution (j : Fin n) :
    colsTo j * colsTo j = (colsTo j : Matrix (Fin n) (Fin n) F) := by
  simp only [colsTo, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp
end GroundTheory.Automorphic.Whittaker
