-- Prove2me | solution 1 for OAI.SubsphereCurrent.Polar.sphereMap_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:55:07.268608+00:00
-- url     : https://prove2.me/submissions/e4a8a772-9423-4584-bd40-14ec8ea15611

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Integration.lean:L158-L189
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Polar.sphereMap_preserving. The node keeps its source
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

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma sphereMap_preserving (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereMap e) (Affine.sphereLaw E) (Affine.sphereLaw F) := by
  have hc (s : Set (Metric.sphere (0 : F) 1)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereMap e) ⁻¹' s)) =
        e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,_,⟨y,hy,rfl⟩,rfl⟩
      exact ⟨r,hr,_,⟨sphereMap e y,hy,rfl⟩, by change r • e y.val = e (r • y.val); simp⟩
    · rintro ⟨r,hr,_,⟨y,hy,rfl⟩,he⟩
      refine ⟨r,hr,_,⟨(sphereMap e).symm y,?_,rfl⟩,?_⟩
      · simpa using hy
      · apply e.injective
        change e (r • e.symm y.val) = e x
        simpa using he
  have hsphere : (volume : Measure E).toSphere.map (sphereMap e) =
      (volume : Measure F).toSphere := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereMap e).measurable hs,
      Measure.toSphere_apply' _ ((sphereMap e).measurable hs),
      Measure.toSphere_apply' _ hs,hc]
    rw [e.toLinearEquiv.finrank_eq]
    congr 1
    rw [← e.measurePreserving.map_eq]
    exact (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
  have huniv : (volume : Measure E).toSphere univ = (volume : Measure F).toSphere univ := by
    rw [← hsphere,Measure.map_apply (sphereMap e).measurable MeasurableSet.univ]
    rfl
  refine ⟨(sphereMap e).measurable,?_⟩
  rw [Affine.sphereLaw, Measure.map_smul _ _ ⇑(sphereMap e),
    hsphere, huniv, Affine.sphereLaw]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Polar
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Polar.sphereMap_preserving := @_root_.OAI.SubsphereCurrent.Polar.sphereMap_preserving
