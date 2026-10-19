-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.directionLaw_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:42:26.607994+00:00
-- url     : https://prove2.me/submissions/afb536a5-afbd-4428-8506-b81d5d9bed97

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean:L91-L104
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.directionLaw_invariant. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
import Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_isometry

-- ---- from OAI.Probability.Subsphere.Mixture.Haar ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma act_mul (u v : Orthogonal E) (x : E) : act (u*v) x = act u (act v x) := rfl

variable [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma blockIso_mul (V : Submodule ℝ E) (u u' : Orthogonal V) (w w' : Orthogonal Vᗮ) (x : E) :
    blockIso V (u*u') (w*w') x = blockIso V u w (blockIso V u' w' x) := by
  rw [blockIso_apply V u' w',map_add,blockIso_on_left,blockIso_on_right]
  rw [blockIso_apply,act_mul,act_mul]

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

-- ---- from OAI.Probability.Subsphere.Mixture.BetaTheory ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma stable_map_eq (N : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x ∈ N, e x ∈ N) (hinv : ∀ x ∈ N, e.symm x ∈ N) :
    N.map e.toLinearMap = N := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact h x hx
  · intro x hx
    exact ⟨e.symm x,hinv x hx,e.apply_symm_apply x⟩

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
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma blockIso_symm (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    (blockIso V u w).symm = blockIso V u⁻¹ w⁻¹ := by
  ext x
  apply (blockIso V u w).injective
  rw [LinearIsometryEquiv.apply_symm_apply,← blockIso_mul]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_left_mem (V N : Submodule ℝ E) (hVN : V ≤ N) (u : Orthogonal V)
    {x : E} (hx : x ∈ N) : blockIso V u 1 x ∈ N := by
  rw [blockIso_apply,act_one]
  apply N.add_mem (hVN (act (E := V) u (V.orthogonalProjectionOnto x)).prop)
  change Vᗮ.starProjection x ∈ N
  rw [Submodule.starProjection_orthogonal_val]
  exact N.sub_mem hx (hVN (V.orthogonalProjectionOnto x).prop)

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_left_stable (V N : Submodule ℝ E) (hVN : V ≤ N) (u : Orthogonal V) :
    N.map (blockIso V u 1).toLinearMap = N := by
  apply stable_map_eq
  · exact fun _ hx => block_left_mem V N hVN u hx
  · rw [blockIso_symm]
    simpa using (fun x (hx : x ∈ N) => block_left_mem V N hVN u⁻¹ hx)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

lemma preserving_map_of_intertwining {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → Y} {g : X → X} {h : Y → Y}
    (hf : Measurable f) (hg : MeasurePreserving g μ μ) (hh : Measurable h)
    (hc : ∀ x, f (g x) = h (f x)) : MeasurePreserving h (μ.map f) (μ.map f) := by
  refine ⟨hh,?_⟩
  rw [Measure.map_map hh hf]
  calc
    _ = μ.map (f ∘ g) := by congr 1; funext x; exact (hc x).symm
    _ = (μ.map g).map f := (Measure.map_map hf hg.measurable).symm
    _ = _ := by rw [hg.map_eq]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Latitude ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma directionLaw_invariant (V N : Submodule ℝ E) [Nontrivial N] (hVN : V ≤ N)
    (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    MeasurePreserving (blockIso V u w) (directionLaw V N) (directionLaw V N) := by
  let r := restrictIso N (blockIso V u 1) (block_left_stable V N hVN u)
  have hr : MeasurePreserving r SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw := SubsphereRegression.ambientSphereLaw_isometry r
  have hg := (measurePreserving_mul_left (orthogonalLaw (E := Vᗮ)) w).prod hr
  apply preserving_map_of_intertwining (measurable_directionSampler V N) hg
    (blockIso V u w).continuous.measurable
  intro z
  change blockIso V 1 (w*z.1) (blockIso V u 1 (z.2 : E)) =
    blockIso V u w (blockIso V 1 z.1 (z.2 : E))
  rw [← blockIso_mul,← blockIso_mul]
  simp

end
open scoped ENNReal NNReal

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_invariant := @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_invariant
