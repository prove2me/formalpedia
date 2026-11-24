-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.exists_le_mul_of_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:57.171803+00:00
-- url     : https://prove2.me/submissions/53238b0d-34a2-4719-ba29-f6d4e80eb9be

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaComplement
namespace GlobalTheory.ThetaComplement
theorem _root_.solution {g : ℕ} (p q : (Fin g → ℂ) → ℝ) (hp : Continuous p)
    (hq : Continuous q) (hp2 : ∀ (r : ℝ) z, p ((r : ℂ) • z) = r ^ 2 * p z)
    (hq2 : ∀ (r : ℝ) z, q ((r : ℂ) • z) = r ^ 2 * q z) (hpos : ∀ z, z ≠ 0 → 0 < p z) :
    ∃ C : ℝ, ∀ z, q z ≤ C * p z := by
  have hne : ∀ z ∈ Metric.sphere (0 : Fin g → ℂ) 1, z ≠ 0 := by
    intro z hz h
    rw [h] at hz
    simp at hz
  have hc : ContinuousOn (fun z => q z / p z) (Metric.sphere (0 : Fin g → ℂ) 1) :=
    hq.continuousOn.div hp.continuousOn (fun z hz => (hpos z (hne z hz)).ne')
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : Fin g → ℂ) 1).image_of_continuousOn hc).bddAbove
  refine ⟨C, fun z => ?_⟩
  by_cases hz : z = 0
  · have h1 := hp2 0 z
    have h2 := hq2 0 z
    simp only [ofReal_zero, zero_smul] at h1 h2
    rw [hz, h1, h2]; simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    set u : Fin g → ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) • z with hu
    have hus : u ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      field_simp
    have h1 : q u / p u ≤ C := hC ⟨u, hus, rfl⟩
    rw [div_le_iff₀ (hpos u (hne u hus)), hu, hp2, hq2] at h1
    have h2 : 0 < ‖z‖⁻¹ ^ 2 := by positivity
    have h3 : ‖z‖⁻¹ ^ 2 * q z ≤ ‖z‖⁻¹ ^ 2 * (C * p z) := by linarith
    exact le_of_mul_le_mul_left h3 h2
end GlobalTheory.ThetaComplement
