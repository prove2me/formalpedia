-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by260_280
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:57:24.863838+00:00
-- url     : https://prove2.me/submissions/07bf83fe-b3f0-47ef-bba5-e8d1d721f355

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run260
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by260_262 : By passesAt 260 262 := by
  apply byRun passesAt 260 2 262
  · rfl
  decide +kernel
lemma by262_265 : By passesAt 262 265 := by
  apply byRun passesAt 262 3 265
  · rfl
  decide +kernel
lemma by260_265 : By passesAt 260 265 := byJoin by260_262 by262_265
lemma by265_267 : By passesAt 265 267 := by
  apply byRun passesAt 265 2 267
  · rfl
  decide +kernel
lemma by267_270 : By passesAt 267 270 := by
  apply byRun passesAt 267 3 270
  · rfl
  decide +kernel
lemma by265_270 : By passesAt 265 270 := byJoin by265_267 by267_270
lemma by260_270 : By passesAt 260 270 := byJoin by260_265 by265_270
lemma by270_272 : By passesAt 270 272 := by
  apply byRun passesAt 270 2 272
  · rfl
  decide +kernel
lemma by272_275 : By passesAt 272 275 := by
  apply byRun passesAt 272 3 275
  · rfl
  decide +kernel
lemma by270_275 : By passesAt 270 275 := byJoin by270_272 by272_275
lemma by275_277 : By passesAt 275 277 := by
  apply byRun passesAt 275 2 277
  · rfl
  decide +kernel
lemma by277_280 : By passesAt 277 280 := by
  apply byRun passesAt 277 3 280
  · rfl
  decide +kernel
lemma by275_280 : By passesAt 275 280 := byJoin by275_277 by277_280
lemma by270_280 : By passesAt 270 280 := byJoin by270_275 by275_280
lemma by260_280_oai : By passesAt 260 280 := byJoin by260_270 by270_280
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by260_280_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by260_280_oai
