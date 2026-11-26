-- Prove2me | solution 1 for LowRankUnivariateSOS.perpPair_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:23.535795+00:00
-- url     : https://prove2.me/submissions/ef57105f-90f4-4dbe-904b-4381933077da

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
    (perpPair t u).fst = -t * u.snd :=
  rfl
end LowRankUnivariateSOS
