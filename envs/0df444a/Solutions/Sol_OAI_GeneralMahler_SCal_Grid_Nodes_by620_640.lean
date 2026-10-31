-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by620_640
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:18:15.799902+00:00
-- url     : https://prove2.me/submissions/a21394c3-609b-4c02-b929-57f41f7bf005

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run620
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by620_622 : By passesAt 620 622 := by
  apply byRun passesAt 620 2 622
  · rfl
  decide +kernel
lemma by622_625 : By passesAt 622 625 := by
  apply byRun passesAt 622 3 625
  · rfl
  decide +kernel
lemma by620_625 : By passesAt 620 625 := byJoin by620_622 by622_625
lemma by625_627 : By passesAt 625 627 := by
  apply byRun passesAt 625 2 627
  · rfl
  decide +kernel
lemma by627_630 : By passesAt 627 630 := by
  apply byRun passesAt 627 3 630
  · rfl
  decide +kernel
lemma by625_630 : By passesAt 625 630 := byJoin by625_627 by627_630
lemma by620_630 : By passesAt 620 630 := byJoin by620_625 by625_630
lemma by630_632 : By passesAt 630 632 := by
  apply byRun passesAt 630 2 632
  · rfl
  decide +kernel
lemma by632_635 : By passesAt 632 635 := by
  apply byRun passesAt 632 3 635
  · rfl
  decide +kernel
lemma by630_635 : By passesAt 630 635 := byJoin by630_632 by632_635
lemma by635_637 : By passesAt 635 637 := by
  apply byRun passesAt 635 2 637
  · rfl
  decide +kernel
lemma by637_640 : By passesAt 637 640 := by
  apply byRun passesAt 637 3 640
  · rfl
  decide +kernel
lemma by635_640 : By passesAt 635 640 := byJoin by635_637 by637_640
lemma by630_640 : By passesAt 630 640 := byJoin by630_635 by635_640
lemma by620_640_oai : By passesAt 620 640 := byJoin by620_630 by630_640
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by620_640_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by620_640_oai
