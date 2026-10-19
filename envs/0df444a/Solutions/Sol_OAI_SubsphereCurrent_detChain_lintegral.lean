-- Prove2me | solution 1 for OAI.SubsphereCurrent.detChain_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:46:02.674469+00:00
-- url     : https://prove2.me/submissions/e6de01b5-d374-421d-9710-ffd862ee6f67

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L378-L399
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.detChain_lintegral. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Theorems.Thm_OAI_SubsphereRegression_lintegral_pi_snoc

-- ---- from OAI.Probability.Subsphere.Kernels.Precision ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

section FiniteVersion
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]
variable {μ : Measure X} (p : X → PMF A)

end FiniteVersion

namespace KernelLearner

end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

section EquivSampling
variable {A B : Type*}
variable [Fintype A] [Nonempty A]

end EquivSampling

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

section CountableBind
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]

lemma pmf_toMeasure_bind (p : PMF A) (k : A → PMF B) :
    (p.bind k).toMeasure = p.toMeasure.bind (fun a => (k a).toMeasure) := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.bind_apply, Measure.bind_apply (measurableSet_singleton b)
      (measurable_of_countable _).aemeasurable, lintegral_countable']
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

lemma pmf_lintegral_bind (p : PMF A) (k : A → PMF B) (f : B → ℝ≥0∞) :
    (∫⁻ b, f b ∂(p.bind k).toMeasure) =
      ∫⁻ a, ∫⁻ b, f b ∂(k a).toMeasure ∂p.toMeasure := by
  rw [pmf_toMeasure_bind, Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
end CountableBind

section Chain
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

omit [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A] in
lemma detChain_snoc (F : ℕ → A → ℝ → A) (a : A) (n : ℕ)
    (r : Fin n → ℝ) (u : ℝ) :
    detChain F a (n+1) (Fin.snoc r u) = F n (detChain F a n r) u := by
  simp [detChain]

lemma measurable_detChain {F : ℕ → A → ℝ → A}
    (hF : ∀ n a, Measurable (F n a)) (a : A) (n : ℕ) :
    Measurable (detChain F a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hj : Measurable (Function.uncurry (F n)) :=
      measurable_from_prod_countable_right (hF n)
    exact hj.comp ((ih.comp (by fun_prop)).prodMk (measurable_pi_apply (Fin.last n)))

lemma detChain_lintegral {F : ℕ → A → ℝ → A} {K : ℕ → A → PMF A}
    (hF : ∀ n a, Measurable (F n a))
    (hFK : ∀ n a, coinLaw.map (F n a) = (K n a).toMeasure)
    (a : A) (n : ℕ) (f : A → ℝ≥0∞) :
    (∫⁻ r : Fin n → ℝ, f (detChain F a n r) ∂Measure.pi (fun _ => coinLaw)) =
      ∫⁻ b, f b ∂(lawChain K a n).toMeasure := by
  induction n generalizing f with
  | zero => simp [detChain, lawChain, PMF.toMeasure_pure]
  | succ n ih =>
    rw [SubsphereRegression.lintegral_pi_snoc coinLaw
      (fun r => f (detChain F a (n+1) r))
      ((measurable_of_countable f).comp (measurable_detChain hF a (n+1)))]
    simp_rw [detChain_snoc]
    calc
      _ = ∫⁻ r : Fin n → ℝ, ∫⁻ b, f b ∂(K n (detChain F a n r)).toMeasure
          ∂Measure.pi (fun _ => coinLaw) := by
        apply lintegral_congr
        intro r
        rw [← hFK, lintegral_map (measurable_of_countable f) (hF _ _)]
      _ = ∫⁻ b, ∫⁻ c, f c ∂(K n b).toMeasure ∂(lawChain K a n).toMeasure := by
        exact ih (fun b => ∫⁻ c, f c ∂(K n b).toMeasure)
      _ = _ := by rw [lawChain, pmf_lintegral_bind]

end Chain
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section

namespace SubsphereCurrent
end SubsphereCurrent

namespace SubsphereRegression.Learner
-- [generator] dropped: open SubsphereCurrent (measurable_countable_select)

end SubsphereRegression.Learner

namespace SubsphereCurrent
namespace KernelLearner
end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v w
namespace SubsphereCurrent

namespace KernelLearner
end KernelLearner

namespace SeededLearner
end SeededLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.detChain_lintegral := @_root_.OAI.SubsphereCurrent.detChain_lintegral
