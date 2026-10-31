-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by320_340
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:00:42.420053+00:00
-- url     : https://prove2.me/submissions/cab814d5-4514-4b91-b110-874fa72afc93

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run320
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by320_322 : By passesAt 320 322 := by
  apply byRun passesAt 320 2 322
  · rfl
  decide +kernel
lemma by322_325 : By passesAt 322 325 := by
  apply byRun passesAt 322 3 325
  · rfl
  decide +kernel
lemma by320_325 : By passesAt 320 325 := byJoin by320_322 by322_325
lemma by325_327 : By passesAt 325 327 := by
  apply byRun passesAt 325 2 327
  · rfl
  decide +kernel
lemma by327_330 : By passesAt 327 330 := by
  apply byRun passesAt 327 3 330
  · rfl
  decide +kernel
lemma by325_330 : By passesAt 325 330 := byJoin by325_327 by327_330
lemma by320_330 : By passesAt 320 330 := byJoin by320_325 by325_330
lemma by330_332 : By passesAt 330 332 := by
  apply byRun passesAt 330 2 332
  · rfl
  decide +kernel
lemma by332_335 : By passesAt 332 335 := by
  apply byRun passesAt 332 3 335
  · rfl
  decide +kernel
lemma by330_335 : By passesAt 330 335 := byJoin by330_332 by332_335
lemma by335_337 : By passesAt 335 337 := by
  apply byRun passesAt 335 2 337
  · rfl
  decide +kernel
lemma by337_340 : By passesAt 337 340 := by
  apply byRun passesAt 337 3 340
  · rfl
  decide +kernel
lemma by335_340 : By passesAt 335 340 := byJoin by335_337 by337_340
lemma by330_340 : By passesAt 330 340 := byJoin by330_335 by335_340
lemma by320_340_oai : By passesAt 320 340 := byJoin by320_330 by330_340
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by320_340_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by320_340_oai
