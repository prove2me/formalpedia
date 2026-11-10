-- Prove2me | solution 1 for LevyFoundations.leanlevy_chat27_exponent_injective_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:39:36.467006+00:00
-- url     : https://prove2.me/submissions/ed832a4f-f939-4121-b3b1-ec75f0879a1a

import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_triple_ext_public

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Transfer a wrapper triple to the source-exact LeanLevy triple. -/
private def chat27_toOriginal (T : LevyFoundations.LevyKhintchineTriple) :
    ProbabilityTheory.LevyKhintchineTriple :=
  { drift := T.drift
    gaussianVariance := T.gaussianVariance
    levyMeasure := T.levyMeasure
    levyMeasure_isLevyMeasure := T.levyMeasure_condition }

theorem solution
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, LevyFoundations.exponent T ξ = LevyFoundations.exponent U ξ) :
    T = U := by
  have heq : chat27_toOriginal T = chat27_toOriginal U :=
    ProbabilityTheory.leanlevy_chat27_triple_ext_public (by
      intro ξ
      change LevyFoundations.exponent T ξ = LevyFoundations.exponent U ξ
      exact h ξ)
  have hb : T.drift = U.drift :=
    congrArg ProbabilityTheory.LevyKhintchineTriple.drift heq
  have hs : T.gaussianVariance = U.gaussianVariance :=
    congrArg ProbabilityTheory.LevyKhintchineTriple.gaussianVariance heq
  have hn : T.levyMeasure = U.levyMeasure :=
    congrArg ProbabilityTheory.LevyKhintchineTriple.levyMeasure heq
  cases T with
  | mk b s n hnT =>
    cases U with
    | mk b' s' n' hnU =>
      cases hb
      cases hs
      cases hn
      rfl