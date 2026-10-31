-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by80_100
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:22:39.340898+00:00
-- url     : https://prove2.me/submissions/23b55e94-a281-4a51-9a7e-569017e2d015

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run80
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by80_82 : By passesAt 80 82 := by
  apply byRun passesAt 80 2 82
  · rfl
  decide +kernel
lemma by82_85 : By passesAt 82 85 := by
  apply byRun passesAt 82 3 85
  · rfl
  decide +kernel
lemma by80_85 : By passesAt 80 85 := byJoin by80_82 by82_85
lemma by85_87 : By passesAt 85 87 := by
  apply byRun passesAt 85 2 87
  · rfl
  decide +kernel
lemma by87_90 : By passesAt 87 90 := by
  apply byRun passesAt 87 3 90
  · rfl
  decide +kernel
lemma by85_90 : By passesAt 85 90 := byJoin by85_87 by87_90
lemma by80_90 : By passesAt 80 90 := byJoin by80_85 by85_90
lemma by90_92 : By passesAt 90 92 := by
  apply byRun passesAt 90 2 92
  · rfl
  decide +kernel
lemma by92_95 : By passesAt 92 95 := by
  apply byRun passesAt 92 3 95
  · rfl
  decide +kernel
lemma by90_95 : By passesAt 90 95 := byJoin by90_92 by92_95
lemma by95_97 : By passesAt 95 97 := by
  apply byRun passesAt 95 2 97
  · rfl
  decide +kernel
lemma by97_100 : By passesAt 97 100 := by
  apply byRun passesAt 97 3 100
  · rfl
  decide +kernel
lemma by95_100 : By passesAt 95 100 := byJoin by95_97 by97_100
lemma by90_100 : By passesAt 90 100 := byJoin by90_95 by95_100
lemma by80_100_oai : By passesAt 80 100 := byJoin by80_90 by90_100
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by80_100_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by80_100_oai
