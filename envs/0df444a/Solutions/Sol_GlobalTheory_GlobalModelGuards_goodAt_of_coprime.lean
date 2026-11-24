-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.goodAt_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:02.942564+00:00
-- url     : https://prove2.me/submissions/4e33cfdc-2484-443d-af4b-d454198a9e4f

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
theorem _root_.solution (l : Level H) (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a.Coprime b)
    (hM : l.M = a * b) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes hab h h'
  · exact key a ha (hM ▸ dvd_mul_right _ _) h
end GlobalTheory.GlobalModelGuards
