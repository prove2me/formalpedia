-- Prove2me | solution 1 for GlobalTheory.matrix_oneParamGroup_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:01.543909+00:00
-- url     : https://prove2.me/submissions/fc573537-740b-4017-8f21-4b777c632e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMatrixOneParameterGroupEqExp
import Theorems.Thm_GlobalTheory_banach_oneParamGroup_eq_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := banach_oneParamGroup_eq_exp M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩
end GlobalTheory
