-- Prove2me | solution 1 for GlobalTheory.T.unitaryGroup_secondKind_coordinates_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:40.525863+00:00
-- url     : https://prove2.me/submissions/07930d2f-88a5-4961-85cb-a2ee796679c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOneStatement
import Theorems.Thm_GlobalTheory_UnitaryChart_second_kind_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  first | exact @GlobalTheory.UnitaryChart.second_kind_chart | exact GlobalTheory.UnitaryChart.second_kind_chart | (intros; apply GlobalTheory.UnitaryChart.second_kind_chart <;> assumption)
end _root_.GlobalTheory.T
