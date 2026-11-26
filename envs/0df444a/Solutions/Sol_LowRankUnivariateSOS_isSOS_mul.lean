-- Prove2me | solution 1 for LowRankUnivariateSOS.isSOS_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:36.445733+00:00
-- url     : https://prove2.me/submissions/d40ebf9d-aacf-437f-86c5-9ad2829e4770

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {p q : Poly}
    (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p * q) := by
  rcases hp with ⟨a, b, rfl⟩
  rcases hq with ⟨c, d, rfl⟩
  refine ⟨a * c - b * d, a * d + b * c, ?_⟩
  ring
end LowRankUnivariateSOS
