-- Prove2me | solution 1 for LowRankUnivariateSOS.perpPair_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:33.742218+00:00
-- url     : https://prove2.me/submissions/03b97a3e-4f17-44ac-9e1b-932e41c24c66

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
theorem _root_.solution (t : Poly) (u : UPair) :
    (perpPair t u).snd = t * u.fst :=
  rfl
end LowRankUnivariateSOS
