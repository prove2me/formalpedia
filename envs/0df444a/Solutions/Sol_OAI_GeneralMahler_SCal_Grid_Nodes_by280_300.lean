-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by280_300
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:00:40.254106+00:00
-- url     : https://prove2.me/submissions/e4e1ffde-5f18-42eb-bb56-b12360237af1

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run280
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by280_282 : By passesAt 280 282 := by
  apply byRun passesAt 280 2 282
  · rfl
  decide +kernel
lemma by282_285 : By passesAt 282 285 := by
  apply byRun passesAt 282 3 285
  · rfl
  decide +kernel
lemma by280_285 : By passesAt 280 285 := byJoin by280_282 by282_285
lemma by285_287 : By passesAt 285 287 := by
  apply byRun passesAt 285 2 287
  · rfl
  decide +kernel
lemma by287_290 : By passesAt 287 290 := by
  apply byRun passesAt 287 3 290
  · rfl
  decide +kernel
lemma by285_290 : By passesAt 285 290 := byJoin by285_287 by287_290
lemma by280_290 : By passesAt 280 290 := byJoin by280_285 by285_290
lemma by290_292 : By passesAt 290 292 := by
  apply byRun passesAt 290 2 292
  · rfl
  decide +kernel
lemma by292_295 : By passesAt 292 295 := by
  apply byRun passesAt 292 3 295
  · rfl
  decide +kernel
lemma by290_295 : By passesAt 290 295 := byJoin by290_292 by292_295
lemma by295_297 : By passesAt 295 297 := by
  apply byRun passesAt 295 2 297
  · rfl
  decide +kernel
lemma by297_300 : By passesAt 297 300 := by
  apply byRun passesAt 297 3 300
  · rfl
  decide +kernel
lemma by295_300 : By passesAt 295 300 := byJoin by295_297 by297_300
lemma by290_300 : By passesAt 290 300 := byJoin by290_295 by295_300
lemma by280_300_oai : By passesAt 280 300 := byJoin by280_290 by290_300
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by280_300_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by280_300_oai
