-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by460_480
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:09:06.407523+00:00
-- url     : https://prove2.me/submissions/b5fdf6ef-7070-4a15-9836-edea75923f3d

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run460
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by460_462 : By passesAt 460 462 := by
  apply byRun passesAt 460 2 462
  · rfl
  decide +kernel
lemma by462_465 : By passesAt 462 465 := by
  apply byRun passesAt 462 3 465
  · rfl
  decide +kernel
lemma by460_465 : By passesAt 460 465 := byJoin by460_462 by462_465
lemma by465_467 : By passesAt 465 467 := by
  apply byRun passesAt 465 2 467
  · rfl
  decide +kernel
lemma by467_470 : By passesAt 467 470 := by
  apply byRun passesAt 467 3 470
  · rfl
  decide +kernel
lemma by465_470 : By passesAt 465 470 := byJoin by465_467 by467_470
lemma by460_470 : By passesAt 460 470 := byJoin by460_465 by465_470
lemma by470_472 : By passesAt 470 472 := by
  apply byRun passesAt 470 2 472
  · rfl
  decide +kernel
lemma by472_475 : By passesAt 472 475 := by
  apply byRun passesAt 472 3 475
  · rfl
  decide +kernel
lemma by470_475 : By passesAt 470 475 := byJoin by470_472 by472_475
lemma by475_477 : By passesAt 475 477 := by
  apply byRun passesAt 475 2 477
  · rfl
  decide +kernel
lemma by477_480 : By passesAt 477 480 := by
  apply byRun passesAt 477 3 480
  · rfl
  decide +kernel
lemma by475_480 : By passesAt 475 480 := byJoin by475_477 by477_480
lemma by470_480 : By passesAt 470 480 := byJoin by470_475 by475_480
lemma by460_480_oai : By passesAt 460 480 := byJoin by460_470 by470_480
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by460_480_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by460_480_oai
