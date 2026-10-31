-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by560_580
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:13:31.556692+00:00
-- url     : https://prove2.me/submissions/73b0b13d-4fbf-4a7b-9d28-676276c88890

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run560
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by560_562 : By passesAt 560 562 := by
  apply byRun passesAt 560 2 562
  · rfl
  decide +kernel
lemma by562_565 : By passesAt 562 565 := by
  apply byRun passesAt 562 3 565
  · rfl
  decide +kernel
lemma by560_565 : By passesAt 560 565 := byJoin by560_562 by562_565
lemma by565_567 : By passesAt 565 567 := by
  apply byRun passesAt 565 2 567
  · rfl
  decide +kernel
lemma by567_570 : By passesAt 567 570 := by
  apply byRun passesAt 567 3 570
  · rfl
  decide +kernel
lemma by565_570 : By passesAt 565 570 := byJoin by565_567 by567_570
lemma by560_570 : By passesAt 560 570 := byJoin by560_565 by565_570
lemma by570_572 : By passesAt 570 572 := by
  apply byRun passesAt 570 2 572
  · rfl
  decide +kernel
lemma by572_575 : By passesAt 572 575 := by
  apply byRun passesAt 572 3 575
  · rfl
  decide +kernel
lemma by570_575 : By passesAt 570 575 := byJoin by570_572 by572_575
lemma by575_577 : By passesAt 575 577 := by
  apply byRun passesAt 575 2 577
  · rfl
  decide +kernel
lemma by577_580 : By passesAt 577 580 := by
  apply byRun passesAt 577 3 580
  · rfl
  decide +kernel
lemma by575_580 : By passesAt 575 580 := byJoin by575_577 by577_580
lemma by570_580 : By passesAt 570 580 := byJoin by570_575 by575_580
lemma by560_580_oai : By passesAt 560 580 := byJoin by560_570 by570_580
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by560_580_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by560_580_oai
