-- Prove2me | solution 1 for OAI.SubsphereCurrent.finiteSample_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:44:13.556132+00:00
-- url     : https://prove2.me/submissions/6f5eb048-c74d-45bd-8485-8533de0bbfce

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L233-L262
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.finiteSample_map. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_measurable_finiteSample

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

lemma finiteCDF_zero {n : ℕ} (p : PMF (Fin n)) : finiteCDF p 0 = 0 := by
  simp [finiteCDF]

lemma finiteCDF_succ {n : ℕ} (p : PMF (Fin n)) (i : Fin n) :
    finiteCDF p (i.val + 1) = finiteCDF p i.val + (p i).toReal := by
  simp [finiteCDF, Finset.sum_range_succ, i.isLt]

lemma finiteCDF_mono {n : ℕ} (p : PMF (Fin n)) : Monotone (finiteCDF p) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _
  split_ifs <;> positivity

lemma finiteCDF_total {n : ℕ} (p : PMF (Fin n)) : finiteCDF p n = 1 := by
  have hs : ∑ i : Fin n, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have ht : ∑ i : Fin n, (p i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i), hs, ENNReal.toReal_one]
  rw [← ht]
  simpa [finiteCDF] using (Fin.sum_univ_eq_sum_range
    (fun j => if h : j < n then (p ⟨j,h⟩).toReal else 0) n).symm

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

lemma finiteCDF_interval_exists {n : ℕ} (p : PMF (Fin n)) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ i : Fin n, finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1) := by
  have hex : ∃ k : ℕ, r < finiteCDF p k := ⟨n, by rwa [finiteCDF_total]⟩
  have hpos : 0 < Nat.find hex := by
    by_contra! h
    have hz : Nat.find hex = 0 := by omega
    have hh := Nat.find_spec hex
    rw [hz, finiteCDF_zero] at hh
    linarith
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (by rwa [finiteCDF_total])
  refine ⟨⟨Nat.find hex - 1, by omega⟩, ?_, ?_⟩
  · change finiteCDF p (Nat.find hex - 1) ≤ r
    exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using Nat.find_spec hex

lemma finiteSample_eq_on_interval {n : ℕ} [NeZero n] (p : PMF (Fin n))
    (i : Fin n) {r : ℝ} (hi : finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)) :
    finiteSample p r = i := by
  have hex : ∃ j : Fin n, finiteCDF p j.val ≤ r ∧ r < finiteCDF p (j.val+1) := ⟨i, hi⟩
  rw [finiteSample, dite_eq_left hex]
  exact finiteCDF_interval_unique p hex.choose_spec hi

lemma finiteSample_map {n : ℕ} [NeZero n] (p : PMF (Fin n)) :
    coinLaw.map (finiteSample p) = p.toMeasure := by
  have hm : Measurable (finiteSample p) :=
    measurable_finiteSample (fun _ => measurable_const) measurable_id
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply hm (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  change volume.restrict (Ico 0 1) ((finiteSample p) ⁻¹' {i}) = p i
  rw [Measure.restrict_apply (hm (measurableSet_singleton i))]
  have he : ((finiteSample p) ⁻¹' {i}) ∩ Ico 0 1 =
      Ico (finiteCDF p i.val) (finiteCDF p (i.val+1)) := by
    ext r
    constructor
    · rintro ⟨he,hr0,hr1⟩
      have hex := finiteCDF_interval_exists p hr0 hr1
      have hs : finiteSample p r = i := he
      rcases (finiteSample_eq_iff p i r).1 hs with hi | hi
      · exact hi
      · exact (hi.2 hex).elim
    · intro hi
      refine ⟨finiteSample_eq_on_interval p i hi, ?_, ?_⟩
      · have hlo : 0 ≤ finiteCDF p i.val := by
          simpa only [finiteCDF_zero] using finiteCDF_mono p (Nat.zero_le i.val)
        exact hlo.trans hi.1
      · have hhi : finiteCDF p (i.val+1) ≤ 1 := by
          simpa only [finiteCDF_total] using finiteCDF_mono p (show i.val+1 ≤ n by omega)
        exact hi.2.trans_le hhi
  rw [he, Real.volume_Ico, finiteCDF_succ]
  simp only [add_sub_cancel_left, ENNReal.ofReal_toReal (p.apply_ne_top i)]

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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.finiteSample_map := @_root_.OAI.SubsphereCurrent.finiteSample_map
