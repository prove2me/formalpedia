-- Prove2me | solution 1 for OAI.NoiselessRegression.lintegral_pi_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:35:57.257813+00:00
-- url     : https://prove2.me/submissions/ba5019dd-cfa0-41bc-a018-c8a6fc3621ff

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Stream.lean:L213-L237
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.lintegral_pi_prefix. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Definitions.Def_OAI_Probability_GaussianRegression_Stream
import Theorems.Thm_OAI_NoiselessRegression_lintegral_pi_snoc

-- ---- from OAI.Probability.GaussianRegression.Stream ----
namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by
  induction T with
  | zero =>
    have : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases h : t ≤ T
    · have he (x : Fin T → E) (y : E) :
          (fun i : Fin t => (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE ht i)) =
            (fun i : Fin t => x (Fin.castLE h i)) := by
        ext i
        change (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE h i).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      rw [lintegral_pi_snoc ν (fun x : Fin (T+1) → E => f (fun i => x (Fin.castLE ht i)))
        (hf.comp (by fun_prop))]
      simp_rw [he, lintegral_const, measure_univ, mul_one]
      exact ih h
    · have he : t = T+1 := by omega
      subst t
      rfl

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.NoiselessRegression.lintegral_pi_prefix := @_root_.OAI.NoiselessRegression.lintegral_pi_prefix
