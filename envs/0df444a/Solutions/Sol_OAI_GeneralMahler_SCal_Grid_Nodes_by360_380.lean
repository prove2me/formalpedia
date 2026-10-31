-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by360_380
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:04:42.227103+00:00
-- url     : https://prove2.me/submissions/be130a36-4d6e-4f16-93ba-86172ab91a4c

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run360
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by360_362 : By passesAt 360 362 := by
  apply byRun passesAt 360 2 362
  · rfl
  decide +kernel
lemma by362_365 : By passesAt 362 365 := by
  apply byRun passesAt 362 3 365
  · rfl
  decide +kernel
lemma by360_365 : By passesAt 360 365 := byJoin by360_362 by362_365
lemma by365_367 : By passesAt 365 367 := by
  apply byRun passesAt 365 2 367
  · rfl
  decide +kernel
lemma by367_370 : By passesAt 367 370 := by
  apply byRun passesAt 367 3 370
  · rfl
  decide +kernel
lemma by365_370 : By passesAt 365 370 := byJoin by365_367 by367_370
lemma by360_370 : By passesAt 360 370 := byJoin by360_365 by365_370
lemma by370_372 : By passesAt 370 372 := by
  apply byRun passesAt 370 2 372
  · rfl
  decide +kernel
lemma by372_375 : By passesAt 372 375 := by
  apply byRun passesAt 372 3 375
  · rfl
  decide +kernel
lemma by370_375 : By passesAt 370 375 := byJoin by370_372 by372_375
lemma by375_377 : By passesAt 375 377 := by
  apply byRun passesAt 375 2 377
  · rfl
  decide +kernel
lemma by377_380 : By passesAt 377 380 := by
  apply byRun passesAt 377 3 380
  · rfl
  decide +kernel
lemma by375_380 : By passesAt 375 380 := byJoin by375_377 by377_380
lemma by370_380 : By passesAt 370 380 := byJoin by370_375 by375_380
lemma by360_380_oai : By passesAt 360 380 := byJoin by360_370 by370_380
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by360_380_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by360_380_oai
