-- Prove2me | solution 1 for GlobalTheory.WpFam.ExpansionB.val_div_ne_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:56.83895+00:00
-- url     : https://prove2.me/submissions/9fa1ad60-931d-48cb-83b5-cc300c67cceb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansion

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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.ExpansionB
namespace GlobalTheory.WpFam.ExpansionB
theorem _root_.solution (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2
end GlobalTheory.WpFam.ExpansionB
