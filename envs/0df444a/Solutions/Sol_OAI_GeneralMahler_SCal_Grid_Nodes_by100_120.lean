-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by100_120
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:47:31.785544+00:00
-- url     : https://prove2.me/submissions/b49e23e6-ab70-4581-8065-7ed0b1ab1ed3

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run100
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by100_102 : By passesAt 100 102 := by
  apply byRun passesAt 100 2 102
  · rfl
  decide +kernel
lemma by102_105 : By passesAt 102 105 := by
  apply byRun passesAt 102 3 105
  · rfl
  decide +kernel
lemma by100_105 : By passesAt 100 105 := byJoin by100_102 by102_105
lemma by105_107 : By passesAt 105 107 := by
  apply byRun passesAt 105 2 107
  · rfl
  decide +kernel
lemma by107_110 : By passesAt 107 110 := by
  apply byRun passesAt 107 3 110
  · rfl
  decide +kernel
lemma by105_110 : By passesAt 105 110 := byJoin by105_107 by107_110
lemma by100_110 : By passesAt 100 110 := byJoin by100_105 by105_110
lemma by110_112 : By passesAt 110 112 := by
  apply byRun passesAt 110 2 112
  · rfl
  decide +kernel
lemma by112_115 : By passesAt 112 115 := by
  apply byRun passesAt 112 3 115
  · rfl
  decide +kernel
lemma by110_115 : By passesAt 110 115 := byJoin by110_112 by112_115
lemma by115_117 : By passesAt 115 117 := by
  apply byRun passesAt 115 2 117
  · rfl
  decide +kernel
lemma by117_120 : By passesAt 117 120 := by
  apply byRun passesAt 117 3 120
  · rfl
  decide +kernel
lemma by115_120 : By passesAt 115 120 := byJoin by115_117 by117_120
lemma by110_120 : By passesAt 110 120 := byJoin by110_115 by115_120
lemma by100_120_oai : By passesAt 100 120 := byJoin by100_110 by110_120
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by100_120_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by100_120_oai
