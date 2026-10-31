-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by120_140
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:48:15.960174+00:00
-- url     : https://prove2.me/submissions/5a978ad9-b4ab-46ea-a3c1-e87697514a9b

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run120
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by120_122 : By passesAt 120 122 := by
  apply byRun passesAt 120 2 122
  · rfl
  decide +kernel
lemma by122_125 : By passesAt 122 125 := by
  apply byRun passesAt 122 3 125
  · rfl
  decide +kernel
lemma by120_125 : By passesAt 120 125 := byJoin by120_122 by122_125
lemma by125_127 : By passesAt 125 127 := by
  apply byRun passesAt 125 2 127
  · rfl
  decide +kernel
lemma by127_130 : By passesAt 127 130 := by
  apply byRun passesAt 127 3 130
  · rfl
  decide +kernel
lemma by125_130 : By passesAt 125 130 := byJoin by125_127 by127_130
lemma by120_130 : By passesAt 120 130 := byJoin by120_125 by125_130
lemma by130_132 : By passesAt 130 132 := by
  apply byRun passesAt 130 2 132
  · rfl
  decide +kernel
lemma by132_135 : By passesAt 132 135 := by
  apply byRun passesAt 132 3 135
  · rfl
  decide +kernel
lemma by130_135 : By passesAt 130 135 := byJoin by130_132 by132_135
lemma by135_137 : By passesAt 135 137 := by
  apply byRun passesAt 135 2 137
  · rfl
  decide +kernel
lemma by137_140 : By passesAt 137 140 := by
  apply byRun passesAt 137 3 140
  · rfl
  decide +kernel
lemma by135_140 : By passesAt 135 140 := byJoin by135_137 by137_140
lemma by130_140 : By passesAt 130 140 := byJoin by130_135 by135_140
lemma by120_140_oai : By passesAt 120 140 := byJoin by120_130 by130_140
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by120_140_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by120_140_oai
