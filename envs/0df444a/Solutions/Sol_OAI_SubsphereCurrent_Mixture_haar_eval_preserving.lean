-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.haar_eval_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:34:25.071976+00:00
-- url     : https://prove2.me/submissions/cb36b487-cbc4-4091-95a7-b45c9990d68e

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Haar.lean:L75-L90
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.haar_eval_preserving. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_integral

-- ---- from OAI.Probability.Subsphere.Mixture.Haar ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

lemma haar_eval_preserving [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun u : Orthogonal E => act u x) orthogonalLaw
      SubsphereRegression.ambientSphereLaw := by
  refine ⟨(continuous_act.comp (continuous_id.prodMk continuous_const)).measurable,?_⟩
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun u : Orthogonal E => act u x) :=
    (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_apply hm hs]
  have hi := haar_eval_integral hx ((measurable_const : Measurable (fun _ : E => (1 : ℝ≥0∞))).indicator hs)
  have he : (fun u : Orthogonal E => s.indicator (fun _ => (1 : ℝ≥0∞)) (act u x)) =
      ((fun u : Orthogonal E => act u x) ⁻¹' s).indicator (fun _ => 1) := by
    funext u
    by_cases h : act u x ∈ s <;> simp [Set.indicator,h]
  rw [he,lintegral_indicator_const (hs.preimage hm),lintegral_indicator_const hs] at hi
  simpa using hi

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.haar_eval_preserving := @_root_.OAI.SubsphereCurrent.Mixture.haar_eval_preserving
