-- Prove2me | solution 1 for LowRankUnivariateSOS.image_orthogonal_of_peeling_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:52.792468+00:00
-- url     : https://prove2.me/submissions/3673d36e-6a96-490d-86a1-d95f3bde3fbf

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Theorems.Thm_LowRankUnivariateSOS_dot_eq_zero_of_peeling_step

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution {p : Poly} {u uImgPrev uImgNext : UPair}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : HasPeelingWitness u uImgPrev uImgNext) :
    ImageOrthogonalResidual B p u uImgNext := by
  intro q hq
  classical
  exact dot_eq_zero_of_peeling_step (B := B) hsocp hprev (Classical.choice (hstep q hq))
end LowRankUnivariateSOS
