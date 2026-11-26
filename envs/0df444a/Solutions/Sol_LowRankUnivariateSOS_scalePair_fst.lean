-- Prove2me | solution 1 for LowRankUnivariateSOS.scalePair_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:22.830033+00:00
-- url     : https://prove2.me/submissions/4846f2a4-67a1-479f-a424-aa9cd1f1a47e

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
theorem _root_.solution (g : Poly) (u : UPair) :
    (scalePair g u).fst = g * u.fst :=
  rfl
end LowRankUnivariateSOS
