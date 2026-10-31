-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by400_420
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:04:43.28689+00:00
-- url     : https://prove2.me/submissions/40cfb5b8-c768-438f-8260-b454a0de6e52

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run400
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by400_402 : By passesAt 400 402 := by
  apply byRun passesAt 400 2 402
  · rfl
  decide +kernel
lemma by402_405 : By passesAt 402 405 := by
  apply byRun passesAt 402 3 405
  · rfl
  decide +kernel
lemma by400_405 : By passesAt 400 405 := byJoin by400_402 by402_405
lemma by405_407 : By passesAt 405 407 := by
  apply byRun passesAt 405 2 407
  · rfl
  decide +kernel
lemma by407_410 : By passesAt 407 410 := by
  apply byRun passesAt 407 3 410
  · rfl
  decide +kernel
lemma by405_410 : By passesAt 405 410 := byJoin by405_407 by407_410
lemma by400_410 : By passesAt 400 410 := byJoin by400_405 by405_410
lemma by410_412 : By passesAt 410 412 := by
  apply byRun passesAt 410 2 412
  · rfl
  decide +kernel
lemma by412_415 : By passesAt 412 415 := by
  apply byRun passesAt 412 3 415
  · rfl
  decide +kernel
lemma by410_415 : By passesAt 410 415 := byJoin by410_412 by412_415
lemma by415_417 : By passesAt 415 417 := by
  apply byRun passesAt 415 2 417
  · rfl
  decide +kernel
lemma by417_420 : By passesAt 417 420 := by
  apply byRun passesAt 417 3 420
  · rfl
  decide +kernel
lemma by415_420 : By passesAt 415 420 := byJoin by415_417 by417_420
lemma by410_420 : By passesAt 410 420 := byJoin by410_415 by415_420
lemma by400_420_oai : By passesAt 400 420 := byJoin by400_410 by410_420
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by400_420_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by400_420_oai
