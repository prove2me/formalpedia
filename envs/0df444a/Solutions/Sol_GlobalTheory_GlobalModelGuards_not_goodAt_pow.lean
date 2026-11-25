-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.not_goodAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:58.967349+00:00
-- url     : https://prove2.me/submissions/c387e0ed-e67d-444b-8d40-6b4fdebf76ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution (l : Level H) (p k : ℕ) (hp : p.Prime) (hM : l.M = p ^ k) : ¬ l.GoodAt p := by
  unfold Level.GoodAt
  rw [hM, Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one,
    Nat.div_self (pow_pos hp.pos k)]
  omega
end GlobalTheory.GlobalModelGuards
