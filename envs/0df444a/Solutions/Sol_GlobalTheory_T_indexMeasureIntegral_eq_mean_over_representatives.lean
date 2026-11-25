-- Prove2me | solution 1 for GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:58:38.516182+00:00
-- url     : https://prove2.me/submissions/6ae22434-4b70-4be0-9877-f63687f21e6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Theorems.Thm_GlobalTheory_IdxInt_cint_eq_mean_reps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W), B ≤ A → (∀ w, ∀ b ∈ B, φ (w + b) = φ w) → (∀ w, w ∉ A → φ w = 0) → (∀ w ∈ R, w ∈ A) → (∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) → Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧ cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_mean_reps | exact GlobalTheory.IdxInt.cint_eq_mean_reps | (intros; apply GlobalTheory.IdxInt.cint_eq_mean_reps <;> assumption)
end _root_.GlobalTheory.T
