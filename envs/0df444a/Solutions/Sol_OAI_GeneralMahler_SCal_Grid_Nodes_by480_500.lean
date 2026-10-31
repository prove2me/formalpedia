-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by480_500
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:09:28.897128+00:00
-- url     : https://prove2.me/submissions/a0fd7aec-de17-4685-8357-d801d5256e33

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run480
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by480_482 : By passesAt 480 482 := by
  apply byRun passesAt 480 2 482
  · rfl
  decide +kernel
lemma by482_485 : By passesAt 482 485 := by
  apply byRun passesAt 482 3 485
  · rfl
  decide +kernel
lemma by480_485 : By passesAt 480 485 := byJoin by480_482 by482_485
lemma by485_487 : By passesAt 485 487 := by
  apply byRun passesAt 485 2 487
  · rfl
  decide +kernel
lemma by487_490 : By passesAt 487 490 := by
  apply byRun passesAt 487 3 490
  · rfl
  decide +kernel
lemma by485_490 : By passesAt 485 490 := byJoin by485_487 by487_490
lemma by480_490 : By passesAt 480 490 := byJoin by480_485 by485_490
lemma by490_492 : By passesAt 490 492 := by
  apply byRun passesAt 490 2 492
  · rfl
  decide +kernel
lemma by492_495 : By passesAt 492 495 := by
  apply byRun passesAt 492 3 495
  · rfl
  decide +kernel
lemma by490_495 : By passesAt 490 495 := byJoin by490_492 by492_495
lemma by495_497 : By passesAt 495 497 := by
  apply byRun passesAt 495 2 497
  · rfl
  decide +kernel
lemma by497_500 : By passesAt 497 500 := by
  apply byRun passesAt 497 3 500
  · rfl
  decide +kernel
lemma by495_500 : By passesAt 495 500 := byJoin by495_497 by497_500
lemma by490_500 : By passesAt 490 500 := byJoin by490_495 by495_500
lemma by480_500_oai : By passesAt 480 500 := byJoin by480_490 by490_500
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by480_500_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by480_500_oai
