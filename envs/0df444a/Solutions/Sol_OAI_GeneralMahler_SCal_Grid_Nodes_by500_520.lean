-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by500_520
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:09:29.771418+00:00
-- url     : https://prove2.me/submissions/d2ed35db-fd68-46bc-adb0-92b69876a196

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run500
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by500_502 : By passesAt 500 502 := by
  apply byRun passesAt 500 2 502
  · rfl
  decide +kernel
lemma by502_505 : By passesAt 502 505 := by
  apply byRun passesAt 502 3 505
  · rfl
  decide +kernel
lemma by500_505 : By passesAt 500 505 := byJoin by500_502 by502_505
lemma by505_507 : By passesAt 505 507 := by
  apply byRun passesAt 505 2 507
  · rfl
  decide +kernel
lemma by507_510 : By passesAt 507 510 := by
  apply byRun passesAt 507 3 510
  · rfl
  decide +kernel
lemma by505_510 : By passesAt 505 510 := byJoin by505_507 by507_510
lemma by500_510 : By passesAt 500 510 := byJoin by500_505 by505_510
lemma by510_512 : By passesAt 510 512 := by
  apply byRun passesAt 510 2 512
  · rfl
  decide +kernel
lemma by512_515 : By passesAt 512 515 := by
  apply byRun passesAt 512 3 515
  · rfl
  decide +kernel
lemma by510_515 : By passesAt 510 515 := byJoin by510_512 by512_515
lemma by515_517 : By passesAt 515 517 := by
  apply byRun passesAt 515 2 517
  · rfl
  decide +kernel
lemma by517_520 : By passesAt 517 520 := by
  apply byRun passesAt 517 3 520
  · rfl
  decide +kernel
lemma by515_520 : By passesAt 515 520 := byJoin by515_517 by517_520
lemma by510_520 : By passesAt 510 520 := byJoin by510_515 by515_520
lemma by500_520_oai : By passesAt 500 520 := byJoin by500_510 by510_520
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by500_520_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by500_520_oai
