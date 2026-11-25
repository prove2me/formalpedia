-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rowsFrom_mul_mul_rowsFrom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:23.497261+00:00
-- url     : https://prove2.me/submissions/6091801c-c3a4-470d-970e-e4abd6ec0dc3

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
    (i : Fin n) : rowsFrom i * b * rowsFrom i = rowsFrom i * b := by
  ext r c
  simp only [rowsFrom, diagonal_mul, mul_diagonal]
  by_cases h1 : i ≤ r <;> by_cases h2 : i ≤ c
  · simp [h1, h2]
  · rw [hb (show id c < id r from lt_of_lt_of_le (not_le.1 h2) h1)]
    simp
  · simp [h1]
  · simp [h1]
end GroundTheory.Automorphic.Whittaker
