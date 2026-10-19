-- Prove2me | solution 1 for OAI.ProjectionMoments.rieszPotential_ball_control
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:41:32.225837+00:00
-- url     : https://prove2.me/submissions/f9bd549b-05f1-4b80-9e83-a76bc1d817ce

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/RieszPotential.lean:L116-L142
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.rieszPotential_ball_control. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential

-- ---- from OAI.Probability.ProjectionMoments.RieszPotential ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rieszPotential_ball_control [Nontrivial E] {α : ℝ} (hα : 0 ≤ α)
    {h : E → ℝ≥0∞} (hh : Measurable h) (z : E) {r : ℝ} (hr : 0 < r) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall z r) ≤
      rieszPotential α h * ENNReal.ofReal (r^α) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrt : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm (s : E) (hs : s ∈ Metric.closedBall z r) :
      1 ≤ ENNReal.ofReal (r^α) * rieszKernel α z s := by
    have hs' : ‖s-z‖ ≤ r := by simpa [dist_eq_norm] using hs
    have hb := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hs') hα
    rw [rieszKernel, ENNReal.rpow_neg, ← ENNReal.ofReal_rpow_of_pos hr]
    calc
      _ = (ENNReal.ofReal r)^α*((ENNReal.ofReal r)^α)⁻¹ :=
        (ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hr0) hrt)) (ENNReal.rpow_ne_top_of_nonneg hα hrt)).symm
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hb)
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ s in Metric.closedBall z r, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro s hs
      simpa only [mul_one,mul_left_comm] using mul_le_mul' le_rfl (hnorm s hs)
    _ ≤ ∫⁻ s, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (r^α)*(∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) :=
      lintegral_const_mul _ (hh.mul (measurable_rieszKernel α z))
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' (show _ ≤ rieszPotential α h from le_iSup (fun z => ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) z) le_rfl

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.rieszPotential_ball_control := @_root_.OAI.ProjectionMoments.rieszPotential_ball_control
