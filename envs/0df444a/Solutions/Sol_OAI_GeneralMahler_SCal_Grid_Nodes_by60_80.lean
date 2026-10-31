-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by60_80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:17:31.699318+00:00
-- url     : https://prove2.me/submissions/8a296f65-afea-49eb-bdf9-0ef81efbc308

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run60
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by60_62 : By passesAt 60 62 := by
  apply byRun passesAt 60 2 62
  · rfl
  decide +kernel
lemma by62_65 : By passesAt 62 65 := by
  apply byRun passesAt 62 3 65
  · rfl
  decide +kernel
lemma by60_65 : By passesAt 60 65 := byJoin by60_62 by62_65
lemma by65_67 : By passesAt 65 67 := by
  apply byRun passesAt 65 2 67
  · rfl
  decide +kernel
lemma by67_70 : By passesAt 67 70 := by
  apply byRun passesAt 67 3 70
  · rfl
  decide +kernel
lemma by65_70 : By passesAt 65 70 := byJoin by65_67 by67_70
lemma by60_70 : By passesAt 60 70 := byJoin by60_65 by65_70
lemma by70_72 : By passesAt 70 72 := by
  apply byRun passesAt 70 2 72
  · rfl
  decide +kernel
lemma by72_75 : By passesAt 72 75 := by
  apply byRun passesAt 72 3 75
  · rfl
  decide +kernel
lemma by70_75 : By passesAt 70 75 := byJoin by70_72 by72_75
lemma by75_77 : By passesAt 75 77 := by
  apply byRun passesAt 75 2 77
  · rfl
  decide +kernel
lemma by77_80 : By passesAt 77 80 := by
  apply byRun passesAt 77 3 80
  · rfl
  decide +kernel
lemma by75_80 : By passesAt 75 80 := byJoin by75_77 by77_80
lemma by70_80 : By passesAt 70 80 := byJoin by70_75 by75_80
lemma by60_80_oai : By passesAt 60 80 := byJoin by60_70 by70_80
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by60_80_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by60_80_oai
