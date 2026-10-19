-- Prove2me | solution 2 for OAI.EntropyRateDimension.BallRatios.information_component
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:05:44.413428+00:00
-- url     : https://prove2.me/submissions/2ad39d0b-695c-4ef5-ba74-61ead404f79a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallIntegrability.lean:L64-L91
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.BallRatios.information_component. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallIntegrability ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

theorem component_le (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (i : ι) :
    S.component μ i ≤ μ := by
  calc
    S.component μ i ≤ ∑ j, S.component μ j :=
      Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
    _ = μ := hμ.symm

theorem affine_preimage_closedBall (S : System ι) (i : ι) (x r : ℝ) :
    S.affine i ⁻¹' closedBall (S.affine i x) (|S.ratio i| *r) = closedBall x r := by
  ext y
  simp only [mem_preimage,mem_closedBall,Real.dist_eq]
  have he : S.affine i y-S.affine i x = S.ratio i*(y-x) := by simp only [affine]; ring
  rw [he,abs_mul]
  exact mul_le_mul_iff_right₀ (S.ratio_pos i)

theorem component_ball (S : System ι) (μ : Measure ℝ) (i : ι) (x r : ℝ) :
    S.component μ i (closedBall (S.affine i x) (|S.ratio i| *r)) =
      ENNReal.ofReal (S.weight i) * μ (closedBall x r) := by
  rw [component,Measure.smul_apply,smul_eq_mul,Measure.map_apply
    (S.affine_continuous i).measurable isClosed_closedBall.measurableSet,
    S.affine_preimage_closedBall]

end System

namespace BallRatios
theorem massReal_pos (μ : Measure ℝ) [IsFiniteMeasure μ] {x r : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) : 0 < μ.real (closedBall x r) := by
  exact ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
    (closedBall_mem_nhds x hr))) (measure_ne_top μ _)

theorem information_component {ι : Type uι} [Fintype ι] (S : System ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : S.SelfSimilar μ) (i : ι)
    {x r : ℝ} (hx : x ∈ μ.support) (hr : 0 < r) :
    information μ (S.affine i x) (|S.ratio i| *r) =
      information μ x r - Real.log (S.weight i) -
        logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) := by
  have hbase := massReal_pos μ hx hr
  have hcomp : (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) =
      S.weight i * μ.real (closedBall x r) := by
    simp only [Measure.real,S.component_ball,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (S.weight_nonneg i)]
  have hcp : 0 < (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    rw [hcomp]; exact mul_pos (S.weight_pos i) hbase
  have htop : 0 < μ.real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    exact hcp.trans_le (ENNReal.toReal_mono (measure_ne_top μ _)
      (S.component_le μ hμ i _))
  have hl : logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) =
      Real.log (μ.real (closedBall (S.affine i x) (|S.ratio i| *r))) -
        Real.log (S.weight i) - Real.log (μ.real (closedBall x r)) := by
    unfold logRatio
    rw [ENNReal.toReal_div]
    change Real.log (μ.real _ / (S.component μ i).real _) = _
    rw [Real.log_div htop.ne' hcp.ne']
    rw [hcomp,Real.log_mul (S.weight_pos i).ne' hbase.ne']
    ring
  rw [hl]
  unfold information
  ring
end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end Coding
end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.BallRatios.information_component.{uι} := @_root_.OAI.EntropyRateDimension.BallRatios.information_component.{uι}
