-- Prove2me | solution 1 for LowRankUnivariateSOS.image_orthogonal_self_of_focp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:47.141076+00:00
-- url     : https://prove2.me/submissions/96032953-2159-40de-a141-a3a5a62cc35d

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution {p : Poly} {u : UPair} (hfocp : IsFOCP B p u) :
    ImageOrthogonalResidual B p u u := by
  intro q hq
  rcases hq with ⟨v, rfl⟩
  exact hfocp v
end LowRankUnivariateSOS
