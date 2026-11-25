-- Prove2me | solution 1 for GlobalTheory.T.encard_sublattices_index_fixed_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:12.020041+00:00
-- url     : https://prove2.me/submissions/7c3c0ac2-32a0-424d-b551-d48c0b5c9904

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLeStatement
import Theorems.Thm_GlobalTheory_TraceCount_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  first | exact @GlobalTheory.TraceCount.main | exact GlobalTheory.TraceCount.main | (intros; apply GlobalTheory.TraceCount.main <;> assumption)
end _root_.GlobalTheory.T
