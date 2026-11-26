-- Prove2me | solution 1 for LowRankUnivariateSOS.hasPeelingWitness_of_rotated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:02.515047+00:00
-- url     : https://prove2.me/submissions/f5787ef8-c007-4647-975e-46fa6d67d22d

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u uImgPrev uImgNext : UPair}
    (hdata :
      ∀ q : Poly, InImageA uImgNext q → Nonempty (RotatedPeelingData u uImgPrev q)) :
    HasPeelingWitness u uImgPrev uImgNext := by
  intro q hq
  rcases hdata q hq with ⟨hqData⟩
  exact ⟨hqData.toWitness⟩
end LowRankUnivariateSOS
