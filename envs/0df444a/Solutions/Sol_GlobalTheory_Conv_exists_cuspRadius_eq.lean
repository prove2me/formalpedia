-- Prove2me | solution 1 for GlobalTheory.Conv.exists_cuspRadius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:04.600579+00:00
-- url     : https://prove2.me/submissions/2a2030b5-1948-4df7-a542-de25ac848ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∃ T, cuspRadius T = ε := by
  refine ⟨-Real.log ε / (2 * Real.pi), ?_⟩
  have h2 : 2 * Real.pi * (-Real.log ε / (2 * Real.pi)) = -Real.log ε := by
    field_simp
  rw [cuspRadius, h2, neg_neg, Real.exp_log hε]
end GlobalTheory.Conv
