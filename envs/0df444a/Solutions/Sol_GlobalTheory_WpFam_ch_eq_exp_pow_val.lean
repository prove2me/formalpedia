-- Prove2me | solution 1 for GlobalTheory.WpFam.ch_eq_exp_pow_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:45.0027+00:00
-- url     : https://prove2.me/submissions/fa1cee58-709a-41c8-bec7-9034560b2ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitZetaAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring
end GlobalTheory.WpFam
