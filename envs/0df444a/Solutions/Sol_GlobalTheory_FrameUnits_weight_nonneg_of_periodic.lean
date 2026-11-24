-- Prove2me | solution 1 for GlobalTheory.FrameUnits.weight_nonneg_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:29:35.94115+00:00
-- url     : https://prove2.me/submissions/5a6ab66e-736f-4927-8b80-b26c72ae9207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Theorems.Thm_GlobalTheory_FrameUnits_exists_le_of_periodic
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_eq_zero_of_gaussian_decay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (r : E → ℂ) (hr : Differentiable ℂ r) (h0 : r 0 ≠ 0)
    (q : E → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) v, q (t • v) = ‖t‖ ^ 2 * q v)
    (hp : ∀ l ∈ S, ∀ z, ‖r (z + l)‖ * Real.exp (-q (z + l)) = ‖r z‖ * Real.exp (-q z))
    (v : E) : 0 ≤ q v := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨C, hC⟩ := exists_le_of_periodic hS (fun z => ‖r z‖ * Real.exp (-q z))
    (hr.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) hp
  have := eq_zero_of_gaussian_decay (fun t => r (t • v))
    (hr.comp (differentiable_id.smul_const v)) C (q v) hneg fun t => by
      have h1 := hC (t • v)
      simp only [hs, Real.exp_neg] at h1
      rwa [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at h1
  simp at this
  exact h0 this
end GlobalTheory.FrameUnits
