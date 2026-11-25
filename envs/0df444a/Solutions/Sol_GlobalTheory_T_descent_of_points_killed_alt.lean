-- Prove2me | solution 1 for GlobalTheory.T.descent_of_points_killed_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:34.786668+00:00
-- url     : https://prove2.me/submissions/850d9458-e80a-4507-b2fd-4c2215d9c911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DescentOfPointsKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DescentOfPointsKilledStatement
import Theorems.Thm_GlobalTheory_descent_of_points_killed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  first | exact @GlobalTheory.descent_of_points_killed | exact GlobalTheory.descent_of_points_killed | (intros; apply GlobalTheory.descent_of_points_killed <;> assumption)
end _root_.GlobalTheory.T
