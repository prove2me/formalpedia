-- Prove2me | solution 1 for GlobalTheory.T.local_continuous_section_vecMul_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:17.6928+00:00
-- url     : https://prove2.me/submissions/e13eb326-2f01-46ba-9edf-6397297371c6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbitStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_exists_local_section


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | exact GlobalTheory.CompanionTheory.OrbitSection.exists_local_section | (intros; apply GlobalTheory.CompanionTheory.OrbitSection.exists_local_section <;> assumption)
end _root_.GlobalTheory.T
