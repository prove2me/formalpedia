-- Prove2me | solution 1 for OAI.SubsphereRegression.lintegral_pi_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:26:01.378699+00:00
-- url     : https://prove2.me/submissions/300ce805-1fe3-4519-b8d4-b656328da41c

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Streaming.lean:L211-L235
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.lintegral_pi_prefix. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Theorems.Thm_OAI_SubsphereRegression_lintegral_pi_snoc

-- ---- from OAI.Probability.Subsphere.Regression.Streaming ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
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

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end StreamCaps

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ObservationAC

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.lintegral_pi_prefix := @_root_.OAI.SubsphereRegression.lintegral_pi_prefix
