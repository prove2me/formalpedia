-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by340_360
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:01:05.164696+00:00
-- url     : https://prove2.me/submissions/f549c2a5-e255-489e-9422-022d1f01c59e

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run340
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by340_342 : By passesAt 340 342 := by
  apply byRun passesAt 340 2 342
  · rfl
  decide +kernel
lemma by342_345 : By passesAt 342 345 := by
  apply byRun passesAt 342 3 345
  · rfl
  decide +kernel
lemma by340_345 : By passesAt 340 345 := byJoin by340_342 by342_345
lemma by345_347 : By passesAt 345 347 := by
  apply byRun passesAt 345 2 347
  · rfl
  decide +kernel
lemma by347_350 : By passesAt 347 350 := by
  apply byRun passesAt 347 3 350
  · rfl
  decide +kernel
lemma by345_350 : By passesAt 345 350 := byJoin by345_347 by347_350
lemma by340_350 : By passesAt 340 350 := byJoin by340_345 by345_350
lemma by350_352 : By passesAt 350 352 := by
  apply byRun passesAt 350 2 352
  · rfl
  decide +kernel
lemma by352_355 : By passesAt 352 355 := by
  apply byRun passesAt 352 3 355
  · rfl
  decide +kernel
lemma by350_355 : By passesAt 350 355 := byJoin by350_352 by352_355
lemma by355_357 : By passesAt 355 357 := by
  apply byRun passesAt 355 2 357
  · rfl
  decide +kernel
lemma by357_360 : By passesAt 357 360 := by
  apply byRun passesAt 357 3 360
  · rfl
  decide +kernel
lemma by355_360 : By passesAt 355 360 := byJoin by355_357 by357_360
lemma by350_360 : By passesAt 350 360 := byJoin by350_355 by355_360
lemma by340_360_oai : By passesAt 340 360 := byJoin by340_350 by350_360
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by340_360_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by340_360_oai
