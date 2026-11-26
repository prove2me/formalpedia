-- Prove2me | solution 1 for LowRankUnivariateSOS.PeelingSchedule.toPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:04.805507+00:00
-- url     : https://prove2.me/submissions/0d6a2dca-7ee0-43d8-bb42-24ce5c54f2c3

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Theorems.Thm_LowRankUnivariateSOS_PeelingPath_trans

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
namespace PeelingSchedule
theorem _root_.solution {u u0 : UPair} {gStart gEnd : Poly}
    (hsched : PeelingSchedule u u0 gStart gEnd) :
    PeelingPath u (scalePair gStart u0) (scalePair gEnd u0) := by
  induction hsched with
  | done g =>
      exact PeelingPath.refl _
  | peel hstep hsched ih =>
      have hfirst := PeelingPath.step (PeelingPath.refl _) hstep
      exact hfirst.trans ih
end PeelingSchedule
end LowRankUnivariateSOS
