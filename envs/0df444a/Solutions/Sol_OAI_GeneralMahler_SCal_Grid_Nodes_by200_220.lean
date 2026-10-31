-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by200_220
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:53:22.964332+00:00
-- url     : https://prove2.me/submissions/dc51d95e-1ca1-4895-b533-fcd3b2214337

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run200
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by200_202 : By passesAt 200 202 := by
  apply byRun passesAt 200 2 202
  · rfl
  decide +kernel
lemma by202_205 : By passesAt 202 205 := by
  apply byRun passesAt 202 3 205
  · rfl
  decide +kernel
lemma by200_205 : By passesAt 200 205 := byJoin by200_202 by202_205
lemma by205_207 : By passesAt 205 207 := by
  apply byRun passesAt 205 2 207
  · rfl
  decide +kernel
lemma by207_210 : By passesAt 207 210 := by
  apply byRun passesAt 207 3 210
  · rfl
  decide +kernel
lemma by205_210 : By passesAt 205 210 := byJoin by205_207 by207_210
lemma by200_210 : By passesAt 200 210 := byJoin by200_205 by205_210
lemma by210_212 : By passesAt 210 212 := by
  apply byRun passesAt 210 2 212
  · rfl
  decide +kernel
lemma by212_215 : By passesAt 212 215 := by
  apply byRun passesAt 212 3 215
  · rfl
  decide +kernel
lemma by210_215 : By passesAt 210 215 := byJoin by210_212 by212_215
lemma by215_217 : By passesAt 215 217 := by
  apply byRun passesAt 215 2 217
  · rfl
  decide +kernel
lemma by217_220 : By passesAt 217 220 := by
  apply byRun passesAt 217 3 220
  · rfl
  decide +kernel
lemma by215_220 : By passesAt 215 220 := byJoin by215_217 by217_220
lemma by210_220 : By passesAt 210 220 := byJoin by210_215 by215_220
lemma by200_220_oai : By passesAt 200 220 := byJoin by200_210 by210_220
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by200_220_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by200_220_oai
