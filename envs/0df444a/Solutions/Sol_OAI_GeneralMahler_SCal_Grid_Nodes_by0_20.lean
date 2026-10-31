-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by0_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:46:47.66086+00:00
-- url     : https://prove2.me/submissions/a96e766e-bdaa-4303-a8fa-a77033c375f2

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run0
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by0_2 : By passesAt 0 2 := by
  apply byRun passesAt 0 2 2
  · rfl
  decide +kernel
lemma by2_5 : By passesAt 2 5 := by
  apply byRun passesAt 2 3 5
  · rfl
  decide +kernel
lemma by0_5 : By passesAt 0 5 := byJoin by0_2 by2_5
lemma by5_7 : By passesAt 5 7 := by
  apply byRun passesAt 5 2 7
  · rfl
  decide +kernel
lemma by7_10 : By passesAt 7 10 := by
  apply byRun passesAt 7 3 10
  · rfl
  decide +kernel
lemma by5_10 : By passesAt 5 10 := byJoin by5_7 by7_10
lemma by0_10 : By passesAt 0 10 := byJoin by0_5 by5_10
lemma by10_12 : By passesAt 10 12 := by
  apply byRun passesAt 10 2 12
  · rfl
  decide +kernel
lemma by12_15 : By passesAt 12 15 := by
  apply byRun passesAt 12 3 15
  · rfl
  decide +kernel
lemma by10_15 : By passesAt 10 15 := byJoin by10_12 by12_15
lemma by15_17 : By passesAt 15 17 := by
  apply byRun passesAt 15 2 17
  · rfl
  decide +kernel
lemma by17_20 : By passesAt 17 20 := by
  apply byRun passesAt 17 3 20
  · rfl
  decide +kernel
lemma by15_20 : By passesAt 15 20 := byJoin by15_17 by17_20
lemma by10_20 : By passesAt 10 20 := byJoin by10_15 by15_20
lemma by0_20_oai : By passesAt 0 20 := byJoin by0_10 by10_20
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by0_20_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by0_20_oai
