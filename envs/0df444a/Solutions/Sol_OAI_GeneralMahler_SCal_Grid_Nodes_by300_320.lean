-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by300_320
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:00:41.242443+00:00
-- url     : https://prove2.me/submissions/5b9fa5cc-1464-4a95-b0f7-d769c45cbf5d

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run300
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by300_302 : By passesAt 300 302 := by
  apply byRun passesAt 300 2 302
  · rfl
  decide +kernel
lemma by302_305 : By passesAt 302 305 := by
  apply byRun passesAt 302 3 305
  · rfl
  decide +kernel
lemma by300_305 : By passesAt 300 305 := byJoin by300_302 by302_305
lemma by305_307 : By passesAt 305 307 := by
  apply byRun passesAt 305 2 307
  · rfl
  decide +kernel
lemma by307_310 : By passesAt 307 310 := by
  apply byRun passesAt 307 3 310
  · rfl
  decide +kernel
lemma by305_310 : By passesAt 305 310 := byJoin by305_307 by307_310
lemma by300_310 : By passesAt 300 310 := byJoin by300_305 by305_310
lemma by310_312 : By passesAt 310 312 := by
  apply byRun passesAt 310 2 312
  · rfl
  decide +kernel
lemma by312_315 : By passesAt 312 315 := by
  apply byRun passesAt 312 3 315
  · rfl
  decide +kernel
lemma by310_315 : By passesAt 310 315 := byJoin by310_312 by312_315
lemma by315_317 : By passesAt 315 317 := by
  apply byRun passesAt 315 2 317
  · rfl
  decide +kernel
lemma by317_320 : By passesAt 317 320 := by
  apply byRun passesAt 317 3 320
  · rfl
  decide +kernel
lemma by315_320 : By passesAt 315 320 := byJoin by315_317 by317_320
lemma by310_320 : By passesAt 310 320 := byJoin by310_315 by315_320
lemma by300_320_oai : By passesAt 300 320 := byJoin by300_310 by310_320
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by300_320_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by300_320_oai
