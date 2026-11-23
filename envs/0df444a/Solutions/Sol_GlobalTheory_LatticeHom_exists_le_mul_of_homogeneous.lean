-- Prove2me | solution 1 for GlobalTheory.LatticeHom.exists_le_mul_of_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:03.98358+00:00
-- url     : https://prove2.me/submissions/76b1cba0-8ef9-412f-9d7b-2d1992227b42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HermFormSwapOfIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
namespace GlobalTheory.LatticeHom
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (q q' : E → ℝ) (hq : Continuous q) (hq' : Continuous q') (hpos : ∀ z, z ≠ 0 → 0 < q z)
    (hs : ∀ (t : ℝ) z, q (t • z) = t ^ 2 * q z) (hs' : ∀ (t : ℝ) z, q' (t • z) = t ^ 2 * q' z) :
    ∃ C : ℝ, ∀ z, q' z ≤ C * q z := by
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun z => q' z / q z) (Metric.sphere (0 : E) 1) := by
    refine hq'.continuousOn.div hq.continuousOn ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    exact (hpos z hz0).ne'
  obtain ⟨C, hC⟩ := hS.bddAbove_image hcont
  refine ⟨C, fun z => ?_⟩
  have h0 : ∀ f : E → ℝ, (∀ (t : ℝ) z, f (t • z) = t ^ 2 * f z) → f 0 = 0 := by
    intro f hf
    simpa using hf 0 0
  by_cases hz : z = 0
  · rw [hz, h0 q hs, h0 q' hs', mul_zero]
  · have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hwS : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
    have hzw : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hw0 : ‖z‖⁻¹ • z ≠ 0 := by
      intro h
      rw [h] at hwS
      simp at hwS
    have hwpos := hpos _ hw0
    have hCw : q' (‖z‖⁻¹ • z) / q (‖z‖⁻¹ • z) ≤ C := hC (Set.mem_image_of_mem _ hwS)
    rw [div_le_iff₀ hwpos] at hCw
    rw [hzw, hs, hs']
    calc ‖z‖ ^ 2 * q' (‖z‖⁻¹ • z) ≤ ‖z‖ ^ 2 * (C * q (‖z‖⁻¹ • z)) :=
          mul_le_mul_of_nonneg_left hCw (sq_nonneg _)
      _ = C * (‖z‖ ^ 2 * q (‖z‖⁻¹ • z)) := by ring
end GlobalTheory.LatticeHom
