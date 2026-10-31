-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by520_540
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:12:45.382986+00:00
-- url     : https://prove2.me/submissions/45d00fbf-5378-46ef-8a7d-9b38cf15c113

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run520
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by520_522 : By passesAt 520 522 := by
  apply byRun passesAt 520 2 522
  · rfl
  decide +kernel
lemma by522_525 : By passesAt 522 525 := by
  apply byRun passesAt 522 3 525
  · rfl
  decide +kernel
lemma by520_525 : By passesAt 520 525 := byJoin by520_522 by522_525
lemma by525_527 : By passesAt 525 527 := by
  apply byRun passesAt 525 2 527
  · rfl
  decide +kernel
lemma by527_530 : By passesAt 527 530 := by
  apply byRun passesAt 527 3 530
  · rfl
  decide +kernel
lemma by525_530 : By passesAt 525 530 := byJoin by525_527 by527_530
lemma by520_530 : By passesAt 520 530 := byJoin by520_525 by525_530
lemma by530_532 : By passesAt 530 532 := by
  apply byRun passesAt 530 2 532
  · rfl
  decide +kernel
lemma by532_535 : By passesAt 532 535 := by
  apply byRun passesAt 532 3 535
  · rfl
  decide +kernel
lemma by530_535 : By passesAt 530 535 := byJoin by530_532 by532_535
lemma by535_537 : By passesAt 535 537 := by
  apply byRun passesAt 535 2 537
  · rfl
  decide +kernel
lemma by537_540 : By passesAt 537 540 := by
  apply byRun passesAt 537 3 540
  · rfl
  decide +kernel
lemma by535_540 : By passesAt 535 540 := byJoin by535_537 by537_540
lemma by530_540 : By passesAt 530 540 := byJoin by530_535 by535_540
lemma by520_540_oai : By passesAt 520 540 := byJoin by520_530 by530_540
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by520_540_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by520_540_oai
