-- Prove2me | solution 1 for OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:57:57.488779+00:00
-- url     : https://prove2.me/submissions/955600b7-e313-40ba-a32a-40fa175aee35

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/PairBounds.lean:L42-L101
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral

-- ---- from OAI.Probability.GaussianPropeller.PairBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma orthonormal_triple_of_gram_pos (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∃ (f : Fin 3 → E) (a b c : ℝ), Orthonormal ℝ f ∧
      f 0 = e ∧ 0 < a ∧ 0 < c ∧ u = a • f 1 ∧ v = b • f 1 + c • f 2 ∧
      (a*c)^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have hu : u ≠ 0 := by
    intro h
    simp [h] at hd
  have ha : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let p : E := ‖u‖⁻¹ • u
  have hp : ‖p‖ = 1 := by simp [p, norm_smul, ha.ne']
  have hu' : u = ‖u‖ • p := by simp [p, smul_smul, ha.ne']
  have hep : ⟪e,p⟫ = 0 := by simp [p, inner_smul_right, heu]
  let b : ℝ := ⟪p,v⟫
  let w : E := v-b • p
  have hpw : ⟪p,w⟫ = 0 := by
    simp [w, b, inner_sub_right, inner_smul_right, hp]
  have hew : ⟪e,w⟫ = 0 := by simp [w, inner_sub_right, inner_smul_right, hev, hep]
  have hd' : ‖u‖^2*‖w‖^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
    have h : ‖w‖^2 = ‖v‖^2-b^2 := by
      rw [show w = v-b • p from rfl, norm_sub_sq_real, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, hp, one_pow, mul_one, inner_smul_right,
        real_inner_comm p v]
      dsimp [b]
      ring
    rw [h, hu', inner_smul_left, starRingEnd_apply, star_trivial]
    change _ = ‖‖u‖ • p‖^2 * ‖v‖^2 - (‖u‖ * b)^2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hp, mul_one]
    ring
  have hw : w ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero] at hd'
    linarith only [hd, hd']
  have hc : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let q : E := ‖w‖⁻¹ • w
  have hq : ‖q‖ = 1 := by simp [q, norm_smul, hc.ne']
  have hw' : w = ‖w‖ • q := by simp [q, smul_smul, hc.ne']
  have hpq : ⟪p,q⟫ = 0 := by simp [q, inner_smul_right, hpw]
  have heq : ⟪e,q⟫ = 0 := by simp [q, inner_smul_right, hew]
  refine ⟨![e,p,q], ‖u‖, b, ‖w‖, ?_, rfl, ha, hc, hu', ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> simpa using (by assumption : ‖_‖ = 1)
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | exact (hij rfl).elim
        | exact hep
        | exact heq
        | exact hpq
        | exact (real_inner_comm e p).trans hep
        | exact (real_inner_comm e q).trans heq
        | exact (real_inner_comm p q).trans hpq
  · change v = b • p + ‖w‖ • q
    rw [← hw']
    dsimp [w]
    module
  · rw [mul_pow]
    exact hd'

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

-- [generator] trimmed: open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry
open GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

-- [generator] trimmed: open GaussianPropeller.Analytic GaussianPropeller.PairIntegral
open GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianPropeller.Pair

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.PairGeometry
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal


theorem solution.{uE} : type_of% @_root_.OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos.{uE} := @_root_.OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos.{uE}
