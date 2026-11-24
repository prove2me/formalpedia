-- Prove2me | solution 1 for GlobalTheory.DetFactor.conj_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:25.352357+00:00
-- url     : https://prove2.me/submissions/6cc51abe-88f8-494b-956d-e9fcb15cbcf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Theorems.Thm_GlobalTheory_DetFactor_toGL_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DetFactor.toGL_val

set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>
    simp_all [single, one_apply, eq_comm] <;> ring
end GlobalTheory.DetFactor
