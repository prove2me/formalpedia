-- Prove2me | solution 1 for LowRankUnivariateSOS.A_scalePair_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:20.451549+00:00
-- url     : https://prove2.me/submissions/766ad468-3edd-4f2a-942a-984977fb286c

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution (g : Poly) (u v : UPair) :
    A (scalePair g u) v = g * A u v := by
  simp [scalePair, A]
  ring
end LowRankUnivariateSOS
