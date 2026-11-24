-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.abs_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:40.351454+00:00
-- url     : https://prove2.me/submissions/4708b878-03ca-4a76-a3d5-b72f23fc895c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {C : ℝ} (hs : Y.IsSymm)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ Y.mulVec x) (h1 : ∀ x, x ⬝ᵥ Y.mulVec x ≤ C * (x ⬝ᵥ x)) (j k : Fin g) :
    |Y j k| ≤ |C| := by
  have a := h1 (Pi.single j 1)
  have b := h1 (Pi.single k 1)
  have p := h0 (Pi.single j 1 + Pi.single k 1)
  have q := h0 (Pi.single j 1 - Pi.single k 1)
  have s : Y k j = Y j k := hs.apply j k
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, Matrix.mulVec_single_one, one_mul,
    Matrix.col_apply, Pi.single_eq_same, mul_one] at a b p q
  have := le_abs_self C
  rw [abs_le]
  constructor <;> linarith
end GlobalTheory.WeightedInverseBound
