-- Prove2me | solution 1 for GlobalTheory.MultSieve.reduced_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.741797+00:00
-- url     : https://prove2.me/submissions/08d511ce-0399-4186-b98f-423198a0e146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.MultSieve
namespace GlobalTheory.MultSieve
theorem _root_.solution {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by
  have := Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq)
    (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc)
    (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)
  omega
end GlobalTheory.MultSieve
