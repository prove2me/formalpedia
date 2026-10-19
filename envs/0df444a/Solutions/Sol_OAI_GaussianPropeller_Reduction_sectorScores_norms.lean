-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.sectorScores_norms
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:44:09.127221+00:00
-- url     : https://prove2.me/submissions/457bccae-c252-4446-a792-73230fba925d

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Attainment.lean:L228-L256
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.sectorScores_norms. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment

-- ---- from OAI.Probability.GaussianPropeller.Attainment ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem axis_inner (d : ℕ) (hd : 2 ≤ d) :
    ⟪axis0 d hd, axis0 d hd⟫ = 1 ∧ ⟪axis1 d hd, axis1 d hd⟫ = 1 ∧
      ⟪axis0 d hd, axis1 d hd⟫ = 0 ∧ ⟪axis1 d hd, axis0 d hd⟫ = 0 := by
  simp [axis0, axis1, EuclideanSpace.inner_single_left]

theorem sectorScores_norms (d : ℕ) (hd : 2 ≤ d) :
    ‖sectorScores d hd‖^2 = 36 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 1‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 2‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 1 - (sectorScores d hd).ofLp 2‖ = 6 := by
  obtain ⟨h00, h11, h01, h10⟩ := axis_inner d hd
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn (x : Space d) : ‖x‖^2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
  constructor
  · rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    change ‖(2 * Real.sqrt 3) • axis0 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd‖^2 = 36
    simp only [hn, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      h00, h01, h10, h11, starRingEnd_apply, star_trivial]
    nlinarith only [hs]
  · have hsq (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖^2 = 36 := by
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals dsimp [sectorScores]
      all_goals simp only [hn, inner_smul_left, inner_smul_right,
        inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        h00, h01, h10, h11, starRingEnd_apply, star_trivial]
      all_goals nlinarith only [hs]
    have he (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 6 := by
      nlinarith [hsq i j hij, norm_nonneg ((sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j)]
    exact ⟨he 0 1 (by decide), he 0 2 (by decide), he 1 2 (by decide)⟩

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.sectorScores_norms := @_root_.OAI.GaussianPropeller.Reduction.sectorScores_norms
