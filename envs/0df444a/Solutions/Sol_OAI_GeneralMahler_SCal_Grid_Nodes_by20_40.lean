-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by20_40
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:55:55.20709+00:00
-- url     : https://prove2.me/submissions/6319d128-ff96-4875-b41c-3aaa47b06805

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run20
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by20_22 : By passesAt 20 22 := by
  apply byRun passesAt 20 2 22
  · rfl
  decide +kernel
lemma by22_25 : By passesAt 22 25 := by
  apply byRun passesAt 22 3 25
  · rfl
  decide +kernel
lemma by20_25 : By passesAt 20 25 := byJoin by20_22 by22_25
lemma by25_27 : By passesAt 25 27 := by
  apply byRun passesAt 25 2 27
  · rfl
  decide +kernel
lemma by27_30 : By passesAt 27 30 := by
  apply byRun passesAt 27 3 30
  · rfl
  decide +kernel
lemma by25_30 : By passesAt 25 30 := byJoin by25_27 by27_30
lemma by20_30 : By passesAt 20 30 := byJoin by20_25 by25_30
lemma by30_32 : By passesAt 30 32 := by
  apply byRun passesAt 30 2 32
  · rfl
  decide +kernel
lemma by32_35 : By passesAt 32 35 := by
  apply byRun passesAt 32 3 35
  · rfl
  decide +kernel
lemma by30_35 : By passesAt 30 35 := byJoin by30_32 by32_35
lemma by35_37 : By passesAt 35 37 := by
  apply byRun passesAt 35 2 37
  · rfl
  decide +kernel
lemma by37_40 : By passesAt 37 40 := by
  apply byRun passesAt 37 3 40
  · rfl
  decide +kernel
lemma by35_40 : By passesAt 35 40 := byJoin by35_37 by37_40
lemma by30_40 : By passesAt 30 40 := byJoin by30_35 by35_40
lemma by20_40_oai : By passesAt 20 40 := byJoin by20_30 by30_40
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by20_40_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by20_40_oai
