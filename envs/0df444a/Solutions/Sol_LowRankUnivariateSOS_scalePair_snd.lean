-- Prove2me | solution 1 for LowRankUnivariateSOS.scalePair_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:33.285268+00:00
-- url     : https://prove2.me/submissions/27001265-eab2-42fe-befb-358b57fc654f

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
    (scalePair g u).snd = g * u.snd :=
  rfl
end LowRankUnivariateSOS
