-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by220_240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:56:39.529762+00:00
-- url     : https://prove2.me/submissions/e8336b9e-8699-4e59-843a-7c7ae303253a

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run220
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by220_222 : By passesAt 220 222 := by
  apply byRun passesAt 220 2 222
  · rfl
  decide +kernel
lemma by222_225 : By passesAt 222 225 := by
  apply byRun passesAt 222 3 225
  · rfl
  decide +kernel
lemma by220_225 : By passesAt 220 225 := byJoin by220_222 by222_225
lemma by225_227 : By passesAt 225 227 := by
  apply byRun passesAt 225 2 227
  · rfl
  decide +kernel
lemma by227_230 : By passesAt 227 230 := by
  apply byRun passesAt 227 3 230
  · rfl
  decide +kernel
lemma by225_230 : By passesAt 225 230 := byJoin by225_227 by227_230
lemma by220_230 : By passesAt 220 230 := byJoin by220_225 by225_230
lemma by230_232 : By passesAt 230 232 := by
  apply byRun passesAt 230 2 232
  · rfl
  decide +kernel
lemma by232_235 : By passesAt 232 235 := by
  apply byRun passesAt 232 3 235
  · rfl
  decide +kernel
lemma by230_235 : By passesAt 230 235 := byJoin by230_232 by232_235
lemma by235_237 : By passesAt 235 237 := by
  apply byRun passesAt 235 2 237
  · rfl
  decide +kernel
lemma by237_240 : By passesAt 237 240 := by
  apply byRun passesAt 237 3 240
  · rfl
  decide +kernel
lemma by235_240 : By passesAt 235 240 := byJoin by235_237 by237_240
lemma by230_240 : By passesAt 230 240 := byJoin by230_235 by235_240
lemma by220_240_oai : By passesAt 220 240 := byJoin by220_230 by230_240
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by220_240_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by220_240_oai
