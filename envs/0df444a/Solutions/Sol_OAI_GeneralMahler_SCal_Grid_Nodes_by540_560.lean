-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by540_560
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:13:30.573774+00:00
-- url     : https://prove2.me/submissions/920a3d9d-aff9-4fd2-9c43-551b6c888c82

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run540
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by540_542 : By passesAt 540 542 := by
  apply byRun passesAt 540 2 542
  · rfl
  decide +kernel
lemma by542_545 : By passesAt 542 545 := by
  apply byRun passesAt 542 3 545
  · rfl
  decide +kernel
lemma by540_545 : By passesAt 540 545 := byJoin by540_542 by542_545
lemma by545_547 : By passesAt 545 547 := by
  apply byRun passesAt 545 2 547
  · rfl
  decide +kernel
lemma by547_550 : By passesAt 547 550 := by
  apply byRun passesAt 547 3 550
  · rfl
  decide +kernel
lemma by545_550 : By passesAt 545 550 := byJoin by545_547 by547_550
lemma by540_550 : By passesAt 540 550 := byJoin by540_545 by545_550
lemma by550_552 : By passesAt 550 552 := by
  apply byRun passesAt 550 2 552
  · rfl
  decide +kernel
lemma by552_555 : By passesAt 552 555 := by
  apply byRun passesAt 552 3 555
  · rfl
  decide +kernel
lemma by550_555 : By passesAt 550 555 := byJoin by550_552 by552_555
lemma by555_557 : By passesAt 555 557 := by
  apply byRun passesAt 555 2 557
  · rfl
  decide +kernel
lemma by557_560 : By passesAt 557 560 := by
  apply byRun passesAt 557 3 560
  · rfl
  decide +kernel
lemma by555_560 : By passesAt 555 560 := byJoin by555_557 by557_560
lemma by550_560 : By passesAt 550 560 := byJoin by550_555 by555_560
lemma by540_560_oai : By passesAt 540 560 := byJoin by540_550 by550_560
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by540_560_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by540_560_oai
