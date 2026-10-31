-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by140_160
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:51:10.239104+00:00
-- url     : https://prove2.me/submissions/8616cc6f-2ec9-4b3a-bb1e-a8049481be52

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run140
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by140_142 : By passesAt 140 142 := by
  apply byRun passesAt 140 2 142
  · rfl
  decide +kernel
lemma by142_145 : By passesAt 142 145 := by
  apply byRun passesAt 142 3 145
  · rfl
  decide +kernel
lemma by140_145 : By passesAt 140 145 := byJoin by140_142 by142_145
lemma by145_147 : By passesAt 145 147 := by
  apply byRun passesAt 145 2 147
  · rfl
  decide +kernel
lemma by147_150 : By passesAt 147 150 := by
  apply byRun passesAt 147 3 150
  · rfl
  decide +kernel
lemma by145_150 : By passesAt 145 150 := byJoin by145_147 by147_150
lemma by140_150 : By passesAt 140 150 := byJoin by140_145 by145_150
lemma by150_152 : By passesAt 150 152 := by
  apply byRun passesAt 150 2 152
  · rfl
  decide +kernel
lemma by152_155 : By passesAt 152 155 := by
  apply byRun passesAt 152 3 155
  · rfl
  decide +kernel
lemma by150_155 : By passesAt 150 155 := byJoin by150_152 by152_155
lemma by155_157 : By passesAt 155 157 := by
  apply byRun passesAt 155 2 157
  · rfl
  decide +kernel
lemma by157_160 : By passesAt 157 160 := by
  apply byRun passesAt 157 3 160
  · rfl
  decide +kernel
lemma by155_160 : By passesAt 155 160 := byJoin by155_157 by157_160
lemma by150_160 : By passesAt 150 160 := byJoin by150_155 by155_160
lemma by140_160_oai : By passesAt 140 160 := byJoin by140_150 by150_160
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by140_160_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by140_160_oai
