-- Prove2me | solution 1 for LowRankUnivariateSOS.smul_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:34.341481+00:00
-- url     : https://prove2.me/submissions/0277aa3e-dfa9-4772-ac00-19975181b827

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution (a : ℝ) (u : UPair) :
    (a • u).fst = a • u.fst :=
  rfl
end LowRankUnivariateSOS
