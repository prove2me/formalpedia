-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by680_700
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:21:54.596432+00:00
-- url     : https://prove2.me/submissions/0d89342a-db70-4651-b180-4fe344499a6e

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run680
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by680_682 : By passesAt 680 682 := by
  apply byRun passesAt 680 2 682
  · rfl
  decide +kernel
lemma by682_685 : By passesAt 682 685 := by
  apply byRun passesAt 682 3 685
  · rfl
  decide +kernel
lemma by680_685 : By passesAt 680 685 := byJoin by680_682 by682_685
lemma by685_687 : By passesAt 685 687 := by
  apply byRun passesAt 685 2 687
  · rfl
  decide +kernel
lemma by687_690 : By passesAt 687 690 := by
  apply byRun passesAt 687 3 690
  · rfl
  decide +kernel
lemma by685_690 : By passesAt 685 690 := byJoin by685_687 by687_690
lemma by680_690 : By passesAt 680 690 := byJoin by680_685 by685_690
lemma by690_692 : By passesAt 690 692 := by
  apply byRun passesAt 690 2 692
  · rfl
  decide +kernel
lemma by692_695 : By passesAt 692 695 := by
  apply byRun passesAt 692 3 695
  · rfl
  decide +kernel
lemma by690_695 : By passesAt 690 695 := byJoin by690_692 by692_695
lemma by695_697 : By passesAt 695 697 := by
  apply byRun passesAt 695 2 697
  · rfl
  decide +kernel
lemma by697_700 : By passesAt 697 700 := by
  apply byRun passesAt 697 3 700
  · rfl
  decide +kernel
lemma by695_700 : By passesAt 695 700 := byJoin by695_697 by697_700
lemma by690_700 : By passesAt 690 700 := byJoin by690_695 by695_700
lemma by680_700_oai : By passesAt 680 700 := byJoin by680_690 by690_700
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by680_700_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by680_700_oai
