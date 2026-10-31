-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by240_260
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:57:02.18462+00:00
-- url     : https://prove2.me/submissions/39de4cca-8b29-430c-a71d-ad87a7f98254

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run240
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by240_242 : By passesAt 240 242 := by
  apply byRun passesAt 240 2 242
  · rfl
  decide +kernel
lemma by242_245 : By passesAt 242 245 := by
  apply byRun passesAt 242 3 245
  · rfl
  decide +kernel
lemma by240_245 : By passesAt 240 245 := byJoin by240_242 by242_245
lemma by245_247 : By passesAt 245 247 := by
  apply byRun passesAt 245 2 247
  · rfl
  decide +kernel
lemma by247_250 : By passesAt 247 250 := by
  apply byRun passesAt 247 3 250
  · rfl
  decide +kernel
lemma by245_250 : By passesAt 245 250 := byJoin by245_247 by247_250
lemma by240_250 : By passesAt 240 250 := byJoin by240_245 by245_250
lemma by250_252 : By passesAt 250 252 := by
  apply byRun passesAt 250 2 252
  · rfl
  decide +kernel
lemma by252_255 : By passesAt 252 255 := by
  apply byRun passesAt 252 3 255
  · rfl
  decide +kernel
lemma by250_255 : By passesAt 250 255 := byJoin by250_252 by252_255
lemma by255_257 : By passesAt 255 257 := by
  apply byRun passesAt 255 2 257
  · rfl
  decide +kernel
lemma by257_260 : By passesAt 257 260 := by
  apply byRun passesAt 257 3 260
  · rfl
  decide +kernel
lemma by255_260 : By passesAt 255 260 := byJoin by255_257 by257_260
lemma by250_260 : By passesAt 250 260 := byJoin by250_255 by255_260
lemma by240_260_oai : By passesAt 240 260 := byJoin by240_250 by250_260
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by240_260_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by240_260_oai
