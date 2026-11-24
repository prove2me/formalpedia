-- Prove2me | solution 1 for GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:43.562781+00:00
-- url     : https://prove2.me/submissions/745c3e2f-7720-4ad7-acdb-c1ae316fda71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
import Theorems.Thm_GlobalTheory_spectralNorm_closedBall_isOpen_isCompact_nhds_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  first | exact @GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | exact GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | (intros; apply GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis <;> assumption)
end _root_.GlobalTheory.T
