-- Prove2me | solution 1 for GlobalTheory.IsoIdem.pow_add_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:13.752827+00:00
-- url     : https://prove2.me/submissions/86be8955-8cc6-4868-bc15-9368094c2e79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem
namespace GlobalTheory.IsoIdem
theorem _root_.solution {R : Type} [Ring R] (z w : R) (m : ℕ) (h : z ^ (m + 1) * w = z ^ m) :
    ∀ j : ℕ, z ^ (m + j) * w ^ j = z ^ m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc z ^ (m + (j + 1)) * w ^ (j + 1) = z ^ j * (z ^ (m + 1) * w) * w ^ j := by
          rw [pow_succ' w j, show m + (j + 1) = j + (m + 1) by omega, pow_add]
          simp only [mul_assoc]
      _ = z ^ (m + j) * w ^ j := by rw [h, ← pow_add, show j + m = m + j by omega]
      _ = z ^ m := ih
end GlobalTheory.IsoIdem
