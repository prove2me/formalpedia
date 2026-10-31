-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by440_460
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:08:43.958322+00:00
-- url     : https://prove2.me/submissions/290bf7ff-9dbc-4ea5-87d8-b54847da3854

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run440
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by440_442 : By passesAt 440 442 := by
  apply byRun passesAt 440 2 442
  · rfl
  decide +kernel
lemma by442_445 : By passesAt 442 445 := by
  apply byRun passesAt 442 3 445
  · rfl
  decide +kernel
lemma by440_445 : By passesAt 440 445 := byJoin by440_442 by442_445
lemma by445_447 : By passesAt 445 447 := by
  apply byRun passesAt 445 2 447
  · rfl
  decide +kernel
lemma by447_450 : By passesAt 447 450 := by
  apply byRun passesAt 447 3 450
  · rfl
  decide +kernel
lemma by445_450 : By passesAt 445 450 := byJoin by445_447 by447_450
lemma by440_450 : By passesAt 440 450 := byJoin by440_445 by445_450
lemma by450_452 : By passesAt 450 452 := by
  apply byRun passesAt 450 2 452
  · rfl
  decide +kernel
lemma by452_455 : By passesAt 452 455 := by
  apply byRun passesAt 452 3 455
  · rfl
  decide +kernel
lemma by450_455 : By passesAt 450 455 := byJoin by450_452 by452_455
lemma by455_457 : By passesAt 455 457 := by
  apply byRun passesAt 455 2 457
  · rfl
  decide +kernel
lemma by457_460 : By passesAt 457 460 := by
  apply byRun passesAt 457 3 460
  · rfl
  decide +kernel
lemma by455_460 : By passesAt 455 460 := byJoin by455_457 by457_460
lemma by450_460 : By passesAt 450 460 := byJoin by450_455 by455_460
lemma by440_460_oai : By passesAt 440 460 := byJoin by440_450 by450_460
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by440_460_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by440_460_oai
