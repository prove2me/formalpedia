-- Prove2me | solution 1 for OAI.SubsphereCurrent.measurable_finiteSample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:41:28.982479+00:00
-- url     : https://prove2.me/submissions/535423b5-723c-41c0-879c-1b9e5c42a464

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L211-L225
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.measurable_finiteSample. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_finiteSample_eq_iff

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

lemma measurable_finiteCDF {X : Type*} [MeasurableSpace X] {n : ℕ}
    {p : X → PMF (Fin n)} (hp : ∀ i, Measurable (fun x => p x i)) (k : ℕ) :
    Measurable (fun x => finiteCDF (p x) k) := by
  unfold finiteCDF
  apply Finset.measurable_sum
  intro j _
  split_ifs
  · exact (hp _).ennreal_toReal
  · exact measurable_const

lemma measurable_finiteSample {X : Type*} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {p : X → PMF (Fin n)} {r : X → ℝ}
    (hp : ∀ i, Measurable (fun x => p x i)) (hr : Measurable r) :
    Measurable (fun x => finiteSample (p x) (r x)) := by
  apply measurable_to_countable'
  intro i
  simp only [Set.preimage, Set.mem_singleton_iff, finiteSample_eq_iff]
  have hm (j : Fin n) : MeasurableSet
      {x | finiteCDF (p x) j.val ≤ r x ∧ r x < finiteCDF (p x) (j.val+1)} :=
    (measurableSet_le (measurable_finiteCDF hp _) hr).inter
      (measurableSet_lt hr (measurable_finiteCDF hp _))
  have he : MeasurableSet {x | ∃ j : Fin n, finiteCDF (p x) j.val ≤ r x ∧
      r x < finiteCDF (p x) (j.val+1)} := by
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hm
  exact (hm i).union ((MeasurableSet.const _).inter he.compl)

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

end CountableBind

section Chain
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.measurable_finiteSample := @_root_.OAI.SubsphereCurrent.measurable_finiteSample
