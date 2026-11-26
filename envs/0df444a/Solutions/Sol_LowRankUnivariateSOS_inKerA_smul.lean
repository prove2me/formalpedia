-- Prove2me | solution 1 for LowRankUnivariateSOS.inKerA_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:43.52626+00:00
-- url     : https://prove2.me/submissions/c2dbf891-dd8a-4de1-9dc8-909fbd90895e

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
attribute [local simp] LowRankUnivariateSOS.A_smul_right

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u w : UPair} (a : ℝ) (hw : InKerA u w) :
    InKerA u (a • w) := by
  rw [InKerA] at hw ⊢
  rw [A_smul_right, hw, smul_zero]
end LowRankUnivariateSOS
