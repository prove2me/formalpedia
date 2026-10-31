-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by40_60
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:05:05.797137+00:00
-- url     : https://prove2.me/submissions/f5ba6f39-f7ae-403d-b949-0a0f610759b6

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run40
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by40_42 : By passesAt 40 42 := by
  apply byRun passesAt 40 2 42
  · rfl
  decide +kernel
lemma by42_45 : By passesAt 42 45 := by
  apply byRun passesAt 42 3 45
  · rfl
  decide +kernel
lemma by40_45 : By passesAt 40 45 := byJoin by40_42 by42_45
lemma by45_47 : By passesAt 45 47 := by
  apply byRun passesAt 45 2 47
  · rfl
  decide +kernel
lemma by47_50 : By passesAt 47 50 := by
  apply byRun passesAt 47 3 50
  · rfl
  decide +kernel
lemma by45_50 : By passesAt 45 50 := byJoin by45_47 by47_50
lemma by40_50 : By passesAt 40 50 := byJoin by40_45 by45_50
lemma by50_52 : By passesAt 50 52 := by
  apply byRun passesAt 50 2 52
  · rfl
  decide +kernel
lemma by52_55 : By passesAt 52 55 := by
  apply byRun passesAt 52 3 55
  · rfl
  decide +kernel
lemma by50_55 : By passesAt 50 55 := byJoin by50_52 by52_55
lemma by55_57 : By passesAt 55 57 := by
  apply byRun passesAt 55 2 57
  · rfl
  decide +kernel
lemma by57_60 : By passesAt 57 60 := by
  apply byRun passesAt 57 3 60
  · rfl
  decide +kernel
lemma by55_60 : By passesAt 55 60 := byJoin by55_57 by57_60
lemma by50_60 : By passesAt 50 60 := byJoin by50_55 by55_60
lemma by40_60_oai : By passesAt 40 60 := byJoin by40_50 by50_60
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by40_60_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by40_60_oai
