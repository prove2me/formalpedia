-- Prove2me | solution 1 for GlobalTheory.T.local_unique_square_root_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:38.906534+00:00
-- url     : https://prove2.me/submissions/994fc6fb-4fdb-4656-aad6-83a9dfd0cbdc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalUniqueSquareRootNearOne
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalUniqueSquareRootNearOneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RingSqrt_exists_local_sqrt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧ (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  first | exact @GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | exact GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | (intros; apply GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt <;> assumption)
end _root_.GlobalTheory.T
