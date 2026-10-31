-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by160_180
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:51:32.735526+00:00
-- url     : https://prove2.me/submissions/f1667e61-4747-491b-8298-4bca9e631e84

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run160
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by160_162 : By passesAt 160 162 := by
  apply byRun passesAt 160 2 162
  · rfl
  decide +kernel
lemma by162_165 : By passesAt 162 165 := by
  apply byRun passesAt 162 3 165
  · rfl
  decide +kernel
lemma by160_165 : By passesAt 160 165 := byJoin by160_162 by162_165
lemma by165_167 : By passesAt 165 167 := by
  apply byRun passesAt 165 2 167
  · rfl
  decide +kernel
lemma by167_170 : By passesAt 167 170 := by
  apply byRun passesAt 167 3 170
  · rfl
  decide +kernel
lemma by165_170 : By passesAt 165 170 := byJoin by165_167 by167_170
lemma by160_170 : By passesAt 160 170 := byJoin by160_165 by165_170
lemma by170_172 : By passesAt 170 172 := by
  apply byRun passesAt 170 2 172
  · rfl
  decide +kernel
lemma by172_175 : By passesAt 172 175 := by
  apply byRun passesAt 172 3 175
  · rfl
  decide +kernel
lemma by170_175 : By passesAt 170 175 := byJoin by170_172 by172_175
lemma by175_177 : By passesAt 175 177 := by
  apply byRun passesAt 175 2 177
  · rfl
  decide +kernel
lemma by177_180 : By passesAt 177 180 := by
  apply byRun passesAt 177 3 180
  · rfl
  decide +kernel
lemma by175_180 : By passesAt 175 180 := byJoin by175_177 by177_180
lemma by170_180 : By passesAt 170 180 := byJoin by170_175 by175_180
lemma by160_180_oai : By passesAt 160 180 := byJoin by160_170 by170_180
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by160_180_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by160_180_oai
