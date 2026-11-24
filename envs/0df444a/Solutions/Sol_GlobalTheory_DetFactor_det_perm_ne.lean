-- Prove2me | solution 1 for GlobalTheory.DetFactor.det_perm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:27.15888+00:00
-- url     : https://prove2.me/submissions/bbb7d0b8-831d-4ef6-818c-e3cf4d614175

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
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
  have := det_permutation (R := k) σ
  simp only [Equiv.Perm.permMatrix] at this
  rw [this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
end GlobalTheory.DetFactor
