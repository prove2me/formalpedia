-- Prove2me | solution 1 for OAI.SubsphereCurrent.finiteSample_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:39:48.391121+00:00
-- url     : https://prove2.me/submissions/e5e1949c-e9be-4a7e-bc7d-27705fdcffb0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L180-L199
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.finiteSample_eq_iff. The node keeps its source
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

-- ---- from OAI.Probability.Subsphere.Kernels.Precision ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
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

lemma finiteCDF_mono {n : ℕ} (p : PMF (Fin n)) : Monotone (finiteCDF p) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _
  split_ifs <;> positivity

lemma finiteCDF_interval_unique {n : ℕ} (p : PMF (Fin n)) {i j : Fin n} {r : ℝ}
    (hi : finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1))
    (hj : finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)) : i = j := by
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · have := finiteCDF_mono p (show i.val+1 ≤ j.val by omega)
    linarith
  · exact h
  · have := finiteCDF_mono p (show j.val+1 ≤ i.val by omega)
    linarith

lemma finiteSample_eq_on_interval {n : ℕ} [NeZero n] (p : PMF (Fin n))
    (i : Fin n) {r : ℝ} (hi : finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) :
    finiteSample p r = i := by
  have hex : ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1) := ⟨i, hi⟩
  rw [finiteSample, dite_eq_left hex]
  exact finiteCDF_interval_unique p hex.choose_spec hi

lemma finiteSample_eq_iff {n : ℕ} [NeZero n] (p : PMF (Fin n)) (i : Fin n) (r : ℝ) :
    finiteSample p r = i ↔
      (finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) ∨
      (i = 0 ∧ ¬ ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)) := by
  by_cases hex : ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1)
  · constructor
    · intro h
      left
      have hc : hex.choose = i := by simpa only [finiteSample, dite_eq_left hex] using h
      simpa only [hc] using hex.choose_spec
    · rintro (h | ⟨_, h⟩)
      · exact finiteSample_eq_on_interval p i h
      · exact (h hex).elim
  · constructor
    · intro hi
      right
      exact ⟨(by simpa [finiteSample, hex] using hi.symm), hex⟩
    · rintro (hi | ⟨hi, _⟩)
      · exact (hex ⟨i, hi⟩).elim
      · simp [finiteSample, hex, hi]

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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.finiteSample_eq_iff := @_root_.OAI.SubsphereCurrent.finiteSample_eq_iff
