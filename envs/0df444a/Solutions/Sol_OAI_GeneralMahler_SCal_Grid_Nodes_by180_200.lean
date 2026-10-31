-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by180_200
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:52:38.290335+00:00
-- url     : https://prove2.me/submissions/83e0b704-e5e2-440d-adff-5c15f4d6c833

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run180
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by180_182 : By passesAt 180 182 := by
  apply byRun passesAt 180 2 182
  · rfl
  decide +kernel
lemma by182_185 : By passesAt 182 185 := by
  apply byRun passesAt 182 3 185
  · rfl
  decide +kernel
lemma by180_185 : By passesAt 180 185 := byJoin by180_182 by182_185
lemma by185_187 : By passesAt 185 187 := by
  apply byRun passesAt 185 2 187
  · rfl
  decide +kernel
lemma by187_190 : By passesAt 187 190 := by
  apply byRun passesAt 187 3 190
  · rfl
  decide +kernel
lemma by185_190 : By passesAt 185 190 := byJoin by185_187 by187_190
lemma by180_190 : By passesAt 180 190 := byJoin by180_185 by185_190
lemma by190_192 : By passesAt 190 192 := by
  apply byRun passesAt 190 2 192
  · rfl
  decide +kernel
lemma by192_195 : By passesAt 192 195 := by
  apply byRun passesAt 192 3 195
  · rfl
  decide +kernel
lemma by190_195 : By passesAt 190 195 := byJoin by190_192 by192_195
lemma by195_197 : By passesAt 195 197 := by
  apply byRun passesAt 195 2 197
  · rfl
  decide +kernel
lemma by197_200 : By passesAt 197 200 := by
  apply byRun passesAt 197 3 200
  · rfl
  decide +kernel
lemma by195_200 : By passesAt 195 200 := byJoin by195_197 by197_200
lemma by190_200 : By passesAt 190 200 := byJoin by190_195 by195_200
lemma by180_200_oai : By passesAt 180 200 := byJoin by180_190 by190_200
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by180_200_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by180_200_oai
