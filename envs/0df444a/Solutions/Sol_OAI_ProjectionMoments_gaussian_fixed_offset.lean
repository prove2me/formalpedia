-- Prove2me | solution 1 for OAI.ProjectionMoments.gaussian_fixed_offset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:37:56.773969+00:00
-- url     : https://prove2.me/submissions/50f5d73d-290d-49cd-aef8-093377607698

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/RieszPotential.lean:L13-L47
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.gaussian_fixed_offset. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_replicaConstant_le
import Theorems.Thm_OAI_ProjectionMoments_lowerDensity_graph_moment_scaled

-- ---- from OAI.Probability.ProjectionMoments.FrameMoments ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma replicaConstant_real_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E} (hν : ν Set.univ ≤ 1) {a : ℝ} {m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    NoiselessRegression.replicaConstant ν a m ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E := by
  apply le_trans _ (NoiselessRegression.replicaConstant_le hν hd le_rfl hm)
  have hr : (4 : ℝ)^a ≤ (4 : ℝ)^(Module.finrank ℝ E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hc : ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^a) ≤
      ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^(Module.finrank ℝ E : ℝ)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by positivity))
  exact add_le_add le_rfl (mul_le_mul' hc le_rfl)

end

lemma ennreal_root_bound {q : ℕ} (hq : q ≠ 0) {v : ℝ≥0∞} {B : ℝ}
    (hB : 0 ≤ B) (h : v ≤ ENNReal.ofReal B ^ q) :
    v ^ (1/(q:ℝ)) ≤ ENNReal.ofReal B := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hh := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1/(q:ℝ))
  rwa [← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hB q) (by positivity),
    ← Real.rpow_natCast_mul hB, mul_one_div_cancel hq', Real.rpow_one] at hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma measure_eq_zero_of_allBall_zero [BorelSpace E] {ν : Measure E} {a : ℝ}
    (hν : AllBallMass ν 0 a) (z : E) {R : ℝ} (hR : 0 < R)
    (hs : ν.support ⊆ Metric.closedBall z R) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    exact propext (iff_of_true (Set.mem_univ x) (hs hx))
  rw [he]
  apply le_antisymm _ bot_le
  simpa using hν z R hR

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.RieszPotential ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_fixed_offset {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 ≤ K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hq : 1 ≤ q) (hmargin : (q:ℝ)+m ≤ a)
    (ha : a ≤ Module.finrank ℝ E) (b : Label m) :
    (∫⁻ A : Fin m → E, (lowerDensity ν m (A,rowMap A z+b))^q
      ∂Measure.pi (fun _ => stdGaussian E))^(1/(q:ℝ)) ≤
      ENNReal.ofReal ((128:ℝ)^Module.finrank ℝ E * K * R^(a-m)) := by
  have hd : 1 ≤ Module.finrank ℝ E := by
    have hq' : 1 ≤ (q:ℝ) := by exact_mod_cast hq
    have hdd : (1:ℝ) ≤ Module.finrank ℝ E := by linarith [(show (0:ℝ) ≤ m from Nat.cast_nonneg m)]
    exact_mod_cast hdd
  have hm : m ≤ Module.finrank ℝ E := by
    exact_mod_cast (show (m:ℝ) ≤ Module.finrank ℝ E by linarith [(show (0:ℝ) ≤ q from Nat.cast_nonneg q)])
  rcases eq_or_lt_of_le hK with hK | hK
  · have hz := measure_eq_zero_of_allBall_zero (hK ▸ hν) z hR hs
    subst ν
    simp only [lowerDensity_zero,zero_pow (by omega : q ≠ 0),lintegral_zero]
    rw [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/q)]
    exact bot_le
  · have hc : 1+ENNReal.ofReal ((3:ℝ)^Module.finrank ℝ E*(4:ℝ)^a)*(2:ℝ≥0∞)^(m+1) ≤
        (128:ℝ≥0∞)^Module.finrank ℝ E := by
      simpa only [NoiselessRegression.replicaConstant,Measure.dirac_apply_of_mem (Set.mem_univ (0:E))] using
        replicaConstant_real_le (ν := Measure.dirac (0:E)) (by simp) hd ha hm
    apply ennreal_root_bound (q := q) (by omega) (by positivity)
    have hh := lowerDensity_graph_moment_scaled hν hK z hR hs m q hmargin b
    apply hh.trans
    apply pow_le_pow_left'
    calc
      _ ≤ ENNReal.ofReal (K*R^(a-m))*(128:ℝ≥0∞)^Module.finrank ℝ E := mul_le_mul' le_rfl hc
      _ = _ := by
        rw [mul_comm]
        simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^Module.finrank ℝ E),
          ENNReal.ofReal_mul hK.le,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 128),
          ENNReal.ofReal_ofNat,mul_assoc]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.gaussian_fixed_offset := @_root_.OAI.ProjectionMoments.gaussian_fixed_offset
