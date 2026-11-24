-- Prove2me | solution 1 for GlobalTheory.T.eq_sum_integral_cube_derivatives_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:52.446421+00:00
-- url     : https://prove2.me/submissions/8d76f0f3-bda9-41e1-be1d-b21d94c85626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSumIntegralCubeDerivatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSumIntegralCubeDerivativesStatement
import Theorems.Thm_GlobalTheory_CubeTaylor_eq_sum_integral_cube_derivatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  first | exact @GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | exact GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | (intros; apply GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives <;> assumption)
end _root_.GlobalTheory.T
