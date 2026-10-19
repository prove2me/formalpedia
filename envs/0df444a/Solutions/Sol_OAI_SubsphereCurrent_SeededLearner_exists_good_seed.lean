-- Prove2me | solution 1 for OAI.SubsphereCurrent.SeededLearner.exists_good_seed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:52:01.336629+00:00
-- url     : https://prove2.me/submissions/c9eec444-b540-4dfa-a8ba-1a8148926401

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean:L834-L858
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.SeededLearner.exists_good_seed. The node keeps its source
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

lemma measurePreserving_swapFirstTwo {A : Type u} {B : Type v} {C : Type w}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (swapFirstTwo A B C) (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    (((MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ ν ρ)))

namespace KernelLearner
lemma conditionalSuccess_le_one {d M T : ℕ} (L : KernelLearner d M T)
    (ε : ℝ) (s : UnitSphere d) (x : Samples d T) : L.conditionalSuccess ε s x ≤ 1 :=
  prob_le_one

end KernelLearner

namespace SeededLearner
lemma uniformSuccess_average_seed {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] :
    L.uniformSuccess ρ ε = ∫⁻ ω, ∫⁻ z : UnitSphere d × Samples d T,
      (L.rules ω).conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) ∂ρ := by
  let e := swapFirstTwo Ω (UnitSphere d) (Samples d T)
  have hp := measurePreserving_swapFirstTwo ρ (uniformSphere d) (sampleLaw d T)
  have hm := (hL.uniform_experiment ε).comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  change AEMeasurable (fun z : Ω × (UnitSphere d × Samples d T) =>
    (L.rules z.1).conditionalSuccess ε z.2.1 z.2.2)
      (ρ.prod ((uniformSphere d).prod (sampleLaw d T))) at hm
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2)
  change (∫⁻ z : Ω × (UnitSphere d × Samples d T),
    (L.rules z.1).conditionalSuccess ε z.2.1 z.2.2
      ∂ρ.prod ((uniformSphere d).prod (sampleLaw d T))) = L.uniformSuccess ρ ε at he
  rw [← he, lintegral_prod _ hm]

lemma exists_good_seed {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (ε : ℝ) [NeZero d] :
    ∃ ω, (L.rules ω).CompletedRules ∧ L.uniformSuccess ρ ε ≤
      ∫⁻ z : UnitSphere d × Samples d T, (L.rules ω).conditionalSuccess ε z.1 z.2
        ∂(uniformSphere d).prod (sampleLaw d T) := by
  let f := fun ω => ∫⁻ z : UnitSphere d × Samples d T,
    (L.rules ω).conditionalSuccess ε z.1 z.2 ∂(uniformSphere d).prod (sampleLaw d T)
  have hf : ∫⁻ ω, f ω ∂ρ ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂ρ := by
        apply lintegral_mono
        intro ω
        calc
          _ ≤ ∫⁻ _ : UnitSphere d × Samples d T, (1 : ℝ≥0∞)
              ∂(uniformSphere d).prod (sampleLaw d T) :=
            lintegral_mono fun z => (L.rules ω).conditionalSuccess_le_one ε z.1 z.2
          _ = 1 := by simp
      _ = 1 := by simp
  obtain ⟨ω,hω,hbound⟩ := exists_notMem_null_lintegral_le (f := f) hf
    (N := {ω | ¬(L.rules ω).CompletedRules}) hL.completed_rules
  refine ⟨ω, by simpa using hω, ?_⟩
  rw [L.uniformSuccess_average_seed ρ hL ε]
  exact hbound
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
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.SeededLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.SubsphereCurrent.SeededLearner.exists_good_seed.{u} := @_root_.OAI.SubsphereCurrent.SeededLearner.exists_good_seed.{u}
