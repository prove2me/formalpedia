-- Prove2me | solution 1 for OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:38:12.803705+00:00
-- url     : https://prove2.me/submissions/ee818a99-232b-44ce-af34-b25ea8366333

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L89-L106
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereRegression_sphere_observation_quasi

-- ---- from OAI.Probability.Subsphere.Regression.Precision ----
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
section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

end StreamTransfer

namespace Learner

end Learner

namespace Learner

end Learner

section LowerFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end LowerFubini

namespace Learner
end Learner

end SubsphereRegression

end
end

end OAI

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

lemma borelPMF_ae_eq (hp : ∀ a, AEMeasurable (fun x => p x a) μ) :
    p =ᵐ[μ] borelPMF p hp := by
  classical
  have hc : ∀ᵐ x ∂μ, ∀ a, p x a = (hp a).mk (fun x => p x a) x :=
    ae_all_iff.mpr (fun a => (hp a).ae_eq_mk)
  filter_upwards [hc] with x hx
  have hs : ∑ a, (hp a).mk (fun x => p x a) x = 1 := by
    simp_rw [← hx]
    simpa only [tsum_fintype] using (p x).tsum_coe
  apply PMF.ext
  intro a
  simp only [borelPMF, dite_eq_left hs, PMF.ofFintype_apply]
  exact hx a
end FiniteVersion

namespace KernelLearner

lemma run_congr {d M T : ℕ} (L K : KernelLearner d M T)
    (hi : L.initial = K.initial) (s : UnitSphere d) (x : Samples d T)
    (ht : ∀ t q (i : Fin T), L.transition t q (x i, ⟪x i,s.val⟫) =
      K.transition t q (x i, ⟪x i,s.val⟫)) (n : ℕ) :
    L.run s x n = K.run s x n := by
  induction n with
  | zero => simp only [run, hi]
  | succ n ih =>
    simp only [run, ih]
    congr 1
    funext a
    cases a with
    | inr a => rfl
    | inl q =>
      dsimp only
      split_ifs
      · rw [ht]
      · rfl

lemma borelVersion_success_ae {d M T : ℕ} (L : KernelLearner d M T)
    (hL : L.CompletedRules) (hd : 3 ≤ d) (ε : ℝ) :
    (fun z : UnitSphere d × Samples d T => L.conditionalSuccess ε z.1 z.2) =ᵐ[
      (uniformSphere d).prod (sampleLaw d T)]
    (fun z => (L.borelVersion hL).conditionalSuccess ε z.1 z.2) := by
  let : NeZero d := ⟨by omega⟩
  have hgood : ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
      ∀ t q (i : Fin T), L.transition t q (z.2 i, ⟪z.2 i,z.1.val⟫) =
      (L.borelVersion hL).transition t q (z.2 i, ⟪z.2 i,z.1.val⟫) := by
    simp only [ae_all_iff]
    intro t q i
    have he := (SubsphereRegression.sphere_sample_observation_quasi
      (E := Vector d) (by simpa using hd) i).ae (borelPMF_ae_eq (L.transition t q) (hL t q))
    simpa only [borelVersion, real_inner_comm, SubsphereRegression.sphereLaw,
      uniformSphere, sampleLaw, observationReference, SubsphereRegression.Vector] using he
  filter_upwards [hgood] with z hz
  have hr := run_congr L (L.borelVersion hL) rfl z.1 z.2 hz T
  simp only [conditionalSuccess, estimateLaw, terminal, hr, borelVersion]

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
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.KernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae := @_root_.OAI.SubsphereCurrent.KernelLearner.borelVersion_success_ae
