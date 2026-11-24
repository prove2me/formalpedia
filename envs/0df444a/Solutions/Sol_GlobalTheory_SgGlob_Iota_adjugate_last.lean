-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.adjugate_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:12.479385+00:00
-- url     : https://prove2.me/submissions/e129e5fd-9637-4ca4-9a33-53a71cf7632b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = lead Z r (Nat.le_succ r) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Even.neg_one_pow ⟨_, rfl⟩, one_mul, Fin.succAbove_last]
  rfl
end GlobalTheory.SgGlob.Iota
