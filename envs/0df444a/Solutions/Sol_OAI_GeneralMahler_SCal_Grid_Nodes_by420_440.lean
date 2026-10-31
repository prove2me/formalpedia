-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by420_440
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:05:06.826281+00:00
-- url     : https://prove2.me/submissions/2bd80aa1-415b-40ff-909c-011c140336b9

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run420
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by420_422 : By passesAt 420 422 := by
  apply byRun passesAt 420 2 422
  · rfl
  decide +kernel
lemma by422_425 : By passesAt 422 425 := by
  apply byRun passesAt 422 3 425
  · rfl
  decide +kernel
lemma by420_425 : By passesAt 420 425 := byJoin by420_422 by422_425
lemma by425_427 : By passesAt 425 427 := by
  apply byRun passesAt 425 2 427
  · rfl
  decide +kernel
lemma by427_430 : By passesAt 427 430 := by
  apply byRun passesAt 427 3 430
  · rfl
  decide +kernel
lemma by425_430 : By passesAt 425 430 := byJoin by425_427 by427_430
lemma by420_430 : By passesAt 420 430 := byJoin by420_425 by425_430
lemma by430_432 : By passesAt 430 432 := by
  apply byRun passesAt 430 2 432
  · rfl
  decide +kernel
lemma by432_435 : By passesAt 432 435 := by
  apply byRun passesAt 432 3 435
  · rfl
  decide +kernel
lemma by430_435 : By passesAt 430 435 := byJoin by430_432 by432_435
lemma by435_437 : By passesAt 435 437 := by
  apply byRun passesAt 435 2 437
  · rfl
  decide +kernel
lemma by437_440 : By passesAt 437 440 := by
  apply byRun passesAt 437 3 440
  · rfl
  decide +kernel
lemma by435_440 : By passesAt 435 440 := byJoin by435_437 by437_440
lemma by430_440 : By passesAt 430 440 := byJoin by430_435 by435_440
lemma by420_440_oai : By passesAt 420 440 := byJoin by420_430 by430_440
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by420_440_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by420_440_oai
