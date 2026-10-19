-- Prove2me | solution 1 for OAI.SubsphereCurrent.Weighted.nested_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:57:41.384886+00:00
-- url     : https://prove2.me/submissions/5429392d-086c-4a30-94c4-9b94a104be85

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Integration.lean:L386-L405
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Weighted.nested_average. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Polar_sphereMap_preserving

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

lemma nestedTest_point {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k)
    (s : Metric.sphere (0 : B.space) 1) :
    onTest (nestedTest A B) (@Polar.sphereMap B.space (B.space.map A.space.subtype)
      B.space.normedAddCommGroup B.space.innerProductSpace
      (B.space.map A.space.subtype).normedAddCommGroup (B.space.map A.space.subtype).innerProductSpace (nestedSpaceEquiv A B) s) =
      onTest A (B.point s) := by
  apply Subtype.ext
  change A.center+A.radius • (B.center : Vector d)+(A.radius*B.radius) • (s.val.val : Vector d) =
    A.center+A.radius • ((B.center : Vector d)+B.radius • (s.val.val : Vector d))
  rw [smul_add,smul_smul,add_assoc]

lemma borel_onTest {d n : ℕ} (A : Affine.Test d n) : Measurable (onTest A) := by
  apply Measurable.subtype_mk
  change Measurable (fun s : Affine.Sphere A.space => A.center+A.radius • (s.val : Vector d))
  fun_prop

lemma nested_average {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s, g (onTest (nestedTest A B) s) ∂Affine.sphereLaw (nestedTest A B).space) =
      ∫⁻ s, g (onTest A (B.point s)) ∂Affine.sphereLaw B.space := by
  let e : B.space ≃ₗᵢ[ℝ] (nestedTest A B).space := nestedSpaceEquiv A B
  let f := @Polar.sphereMap B.space (nestedTest A B).space
    B.space.normedAddCommGroup B.space.innerProductSpace
    (nestedTest A B).space.normedAddCommGroup (nestedTest A B).space.innerProductSpace e
  have hp := @Polar.sphereMap_preserving B.space (nestedTest A B).space
    B.space.normedAddCommGroup B.space.innerProductSpace inferInstance inferInstance inferInstance
    (nestedTest A B).space.normedAddCommGroup (nestedTest A B).space.innerProductSpace
    inferInstance inferInstance inferInstance e
  calc
    _ = ∫⁻ s, g (onTest (nestedTest A B) (f s)) ∂Affine.sphereLaw B.space := by
      exact (hp.lintegral_comp (hg.comp (borel_onTest (nestedTest A B)))).symm
    _ = _ := by
      apply lintegral_congr
      intro s
      congr 1
      exact nestedTest_point A B s

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
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Weighted.nested_average := @_root_.OAI.SubsphereCurrent.Weighted.nested_average
