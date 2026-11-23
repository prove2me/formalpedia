-- Prove2me | solution 1 for GlobalTheory.FrameUnits.exists_le_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:53.55075+00:00
-- url     : https://prove2.me/submissions/1d3a0b91-6a9c-43c7-a453-e49d4eb3b700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace GlobalTheory.FrameUnits
theorem _root_.solution {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R) (φ : E → ℝ)
    (hφ : Continuous φ) (hp : ∀ l ∈ S, ∀ z, φ (z + l) = φ z) : ∃ C, ∀ z, φ z ≤ C := by
  haveI := FiniteDimensional.proper ℂ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E) R).image hφ).bddAbove
  refine ⟨C, fun z => ?_⟩
  obtain ⟨l, hl, h⟩ := hS z
  rw [← hp l hl z]
  exact hC ⟨_, mem_closedBall_zero_iff.2 h, rfl⟩
end GlobalTheory.FrameUnits
