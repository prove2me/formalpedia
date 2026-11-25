-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.colsTo_mul_mul_colsTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:43.137892+00:00
-- url     : https://prove2.me/submissions/7357c436-64e2-4203-91e6-59ba7e72fe58

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
theorem _root_.solution {b : Matrix (Fin n) (Fin n) F} (hb : b.IsUpperTriangular)
    (j : Fin n) : colsTo j * b * colsTo j = b * colsTo j := by
  ext r c
  simp only [colsTo, diagonal_mul, mul_diagonal]
  by_cases h1 : r ≤ j <;> by_cases h2 : c ≤ j
  · simp [h1, h2]
  · simp [h2]
  · rw [hb (show id c < id r from lt_of_le_of_lt h2 (not_le.1 h1))]
    simp
  · simp [h2]
end GroundTheory.Automorphic.Whittaker
