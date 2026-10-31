-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by640_660
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:18:38.291926+00:00
-- url     : https://prove2.me/submissions/349e7231-59ab-4f26-b716-bd2a9d60b190

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run640
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by640_642 : By passesAt 640 642 := by
  apply byRun passesAt 640 2 642
  · rfl
  decide +kernel
lemma by642_645 : By passesAt 642 645 := by
  apply byRun passesAt 642 3 645
  · rfl
  decide +kernel
lemma by640_645 : By passesAt 640 645 := byJoin by640_642 by642_645
lemma by645_647 : By passesAt 645 647 := by
  apply byRun passesAt 645 2 647
  · rfl
  decide +kernel
lemma by647_650 : By passesAt 647 650 := by
  apply byRun passesAt 647 3 650
  · rfl
  decide +kernel
lemma by645_650 : By passesAt 645 650 := byJoin by645_647 by647_650
lemma by640_650 : By passesAt 640 650 := byJoin by640_645 by645_650
lemma by650_652 : By passesAt 650 652 := by
  apply byRun passesAt 650 2 652
  · rfl
  decide +kernel
lemma by652_655 : By passesAt 652 655 := by
  apply byRun passesAt 652 3 655
  · rfl
  decide +kernel
lemma by650_655 : By passesAt 650 655 := byJoin by650_652 by652_655
lemma by655_657 : By passesAt 655 657 := by
  apply byRun passesAt 655 2 657
  · rfl
  decide +kernel
lemma by657_660 : By passesAt 657 660 := by
  apply byRun passesAt 657 3 660
  · rfl
  decide +kernel
lemma by655_660 : By passesAt 655 660 := byJoin by655_657 by657_660
lemma by650_660 : By passesAt 650 660 := byJoin by650_655 by655_660
lemma by640_660_oai : By passesAt 640 660 := byJoin by640_650 by650_660
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by640_660_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by640_660_oai
