-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by600_620
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:17:30.858004+00:00
-- url     : https://prove2.me/submissions/c7e30dd8-fdb5-4313-bd6e-cdc84259aae3

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run600
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by600_602 : By passesAt 600 602 := by
  apply byRun passesAt 600 2 602
  · rfl
  decide +kernel
lemma by602_605 : By passesAt 602 605 := by
  apply byRun passesAt 602 3 605
  · rfl
  decide +kernel
lemma by600_605 : By passesAt 600 605 := byJoin by600_602 by602_605
lemma by605_607 : By passesAt 605 607 := by
  apply byRun passesAt 605 2 607
  · rfl
  decide +kernel
lemma by607_610 : By passesAt 607 610 := by
  apply byRun passesAt 607 3 610
  · rfl
  decide +kernel
lemma by605_610 : By passesAt 605 610 := byJoin by605_607 by607_610
lemma by600_610 : By passesAt 600 610 := byJoin by600_605 by605_610
lemma by610_612 : By passesAt 610 612 := by
  apply byRun passesAt 610 2 612
  · rfl
  decide +kernel
lemma by612_615 : By passesAt 612 615 := by
  apply byRun passesAt 612 3 615
  · rfl
  decide +kernel
lemma by610_615 : By passesAt 610 615 := byJoin by610_612 by612_615
lemma by615_617 : By passesAt 615 617 := by
  apply byRun passesAt 615 2 617
  · rfl
  decide +kernel
lemma by617_620 : By passesAt 617 620 := by
  apply byRun passesAt 617 3 620
  · rfl
  decide +kernel
lemma by615_620 : By passesAt 615 620 := byJoin by615_617 by617_620
lemma by610_620 : By passesAt 610 620 := byJoin by610_615 by615_620
lemma by600_620_oai : By passesAt 600 620 := byJoin by600_610 by610_620
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by600_620_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by600_620_oai
