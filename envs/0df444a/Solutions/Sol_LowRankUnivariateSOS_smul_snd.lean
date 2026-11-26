-- Prove2me | solution 1 for LowRankUnivariateSOS.smul_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:24.031238+00:00
-- url     : https://prove2.me/submissions/5bcf9d22-8cb4-4935-b980-08646f70890d

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
    (a • u).snd = a • u.snd :=
  rfl
end LowRankUnivariateSOS
