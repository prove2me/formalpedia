-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:44.621803+00:00
-- url     : https://prove2.me/submissions/34314683-d59a-44e0-ac5d-f0e10d3d30e3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts G) := inferInstance
  have h1 := Measure.haarMeasure_unique μ K₀
  have h2 := Measure.haarMeasure_unique ν K₀
  have a0 : μ K₀ ≠ 0 := fun h => hμ (by rw [h1, h, zero_smul])
  have b0 : ν K₀ ≠ 0 := fun h => hν (by rw [h2, h, zero_smul])
  have at' : μ K₀ ≠ ⊤ := K₀.isCompact.measure_lt_top.ne
  have bt : ν K₀ ≠ ⊤ := K₀.isCompact.measure_lt_top.ne
  refine ⟨μ K₀ / ν K₀, ENNReal.div_ne_zero.2 ⟨a0, bt⟩, ENNReal.div_ne_top at' b0, ?_⟩
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  rw [smul_smul, ← h2, ENNReal.div_mul_cancel b0 bt]
end GlobalTheory.CompanionTheory.HaarPK
