-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by580_600
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:13:54.066934+00:00
-- url     : https://prove2.me/submissions/e080e110-6fa1-4961-bf29-55a02047ebf0

import Mathlib
import Definitions.Def_OAIQ026G002

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

lemma byRun (p:ℕ→Bool) (n m k:ℕ) (he:n+m=k) (h:runB p n m=true): By p n k := by
  subst k
  induction m with
  | zero=> intro i h1 h2; omega
  | succ m ih=>
    simp only [runB,Bool.and_eq_true] at h
    intro i h1 h2; by_cases H:i=n+m
    · exact H.symm ▸ h.1
    apply ih h.2 _ h1; omega
lemma byJoin {p:ℕ→Bool} {x y z:ℕ} (h:By p x y) (hh:By p y z):
    By p x z := by intro i he hz; rcases lt_or_ge i y with h'|h'; exact h i he h'; exact hh i h' hz
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run580
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by580_582 : By passesAt 580 582 := by
  apply byRun passesAt 580 2 582
  · rfl
  decide +kernel
lemma by582_585 : By passesAt 582 585 := by
  apply byRun passesAt 582 3 585
  · rfl
  decide +kernel
lemma by580_585 : By passesAt 580 585 := byJoin by580_582 by582_585
lemma by585_587 : By passesAt 585 587 := by
  apply byRun passesAt 585 2 587
  · rfl
  decide +kernel
lemma by587_590 : By passesAt 587 590 := by
  apply byRun passesAt 587 3 590
  · rfl
  decide +kernel
lemma by585_590 : By passesAt 585 590 := byJoin by585_587 by587_590
lemma by580_590 : By passesAt 580 590 := byJoin by580_585 by585_590
lemma by590_592 : By passesAt 590 592 := by
  apply byRun passesAt 590 2 592
  · rfl
  decide +kernel
lemma by592_595 : By passesAt 592 595 := by
  apply byRun passesAt 592 3 595
  · rfl
  decide +kernel
lemma by590_595 : By passesAt 590 595 := byJoin by590_592 by592_595
lemma by595_597 : By passesAt 595 597 := by
  apply byRun passesAt 595 2 597
  · rfl
  decide +kernel
lemma by597_600 : By passesAt 597 600 := by
  apply byRun passesAt 597 3 600
  · rfl
  decide +kernel
lemma by595_600 : By passesAt 595 600 := byJoin by595_597 by597_600
lemma by590_600 : By passesAt 590 600 := byJoin by590_595 by595_600
lemma by580_600_oai : By passesAt 580 600 := byJoin by580_590 by590_600
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by580_600_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by580_600_oai
