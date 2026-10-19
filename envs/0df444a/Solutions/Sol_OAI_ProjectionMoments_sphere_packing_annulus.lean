-- Prove2me | solution 1 for OAI.ProjectionMoments.sphere_packing_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:53:40.354705+00:00
-- url     : https://prove2.me/submissions/dc374c45-26df-4f70-b79f-096f5b77e46f

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Caps.lean:L15-L73
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.sphere_packing_annulus. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_packing_annulus (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) * (r/2)^Module.finrank ℝ E ≤
      (1+r/2)^Module.finrank ℝ E - (1-r/2)^Module.finrank ℝ E := by
  classical
  let δ := r/2
  let U : Set E := ⋃ c ∈ s, Metric.ball c δ
  let V : Set E := Metric.ball 0 (1-δ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinner : 0 < 1-δ := by dsimp [δ]; linarith
  have houter : 0 < 1+δ := by positivity
  have hdis : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
    have hxc' : dist x c < δ := hxc
    have hx0 : ‖x‖ < 1-δ := by simpa [V, Metric.mem_ball, dist_zero_right] using hxV
    have hc1 := hs c hc
    have htri := dist_triangle c x (0 : E)
    rw [dist_zero_right, dist_zero_right, dist_comm c x, hc1] at htri
    linarith
  have hsub : U ∪ V ⊆ Metric.ball (0 : E) (1+δ) := by
    rintro x (hx | hx)
    · obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
      apply Metric.mem_ball.mpr
      have htri := dist_triangle x c (0 : E)
      rw [dist_zero_right c, hs c hc] at htri
      exact htri.trans_lt (by have hh : dist x c < δ := hxc; linarith)
    · exact (Metric.ball_subset_ball (by linarith : 1-δ ≤ 1+δ)) hx
  have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable
    (fun c _ => Metric.isOpen_ball.measurableSet)
  have hvol : ((s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) +
      ENNReal.ofReal ((1-δ)^Module.finrank ℝ E)) * volume (Metric.ball (0 : E) 1) ≤
      ENNReal.ofReal ((1+δ)^Module.finrank ℝ E)*volume (Metric.ball (0 : E) 1) := by
    calc
      _ = volume (U ∪ V) := by
        rw [measure_union hUV Metric.isOpen_ball.measurableSet,
          show volume U = (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*
            volume (Metric.ball (0 : E) 1) by
            rw [measure_biUnion_finset hdis (fun _ _ => Metric.isOpen_ball.measurableSet)]
            simp only [Measure.addHaar_ball_of_pos volume _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc],
          Measure.addHaar_ball_of_pos volume 0 hinner, add_mul]
      _ ≤ volume (Metric.ball (0 : E) (1+δ)) := measure_mono hsub
      _ = _ := Measure.addHaar_ball_of_pos volume 0 houter
  have hv0 : volume (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hh := (ENNReal.mul_le_mul_iff_left hv0 hvt).mp hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg houter.le _) hh
  simp only [ENNReal.toReal_add (by finiteness :
    (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≠ ∞) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _),
    ENNReal.toReal_ofReal (pow_nonneg hinner.le _)] at hreal
  dsimp [δ] at hreal
  linarith

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.sphere_packing_annulus := @_root_.OAI.ProjectionMoments.sphere_packing_annulus
