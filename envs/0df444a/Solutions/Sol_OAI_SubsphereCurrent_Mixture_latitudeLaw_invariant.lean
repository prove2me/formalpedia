-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.latitudeLaw_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:48:16.880995+00:00
-- url     : https://prove2.me/submissions/aa7d2ddc-d357-40cb-8e4d-8f418b2f7d15

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean:L201-L222
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.latitudeLaw_invariant. The node keeps its source
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
lemma block_right_fix_e (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) (w : Orthogonal Vᗮ) :
    blockIso V 1 w (e.val : E) = (e.val : E) := by simp [act_one]

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_right_latitude_mem (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (w : Orthogonal Vᗮ) {x : E} (hx : x ∈ latitudeSpace V e) :
    blockIso V 1 w x ∈ latitudeSpace V e := by
  rw [latitudeSpace,Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← block_right_fix_e V e w,LinearIsometryEquiv.inner_map_map]
  exact hx

omit [MeasurableSpace E] [BorelSpace E] in
lemma block_right_latitude_stable (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (w : Orthogonal Vᗮ) :
    (latitudeSpace V e).map (blockIso V 1 w).toLinearMap = latitudeSpace V e := by
  apply stable_map_eq
  · exact fun _ hx => block_right_latitude_mem V e w hx
  · rw [blockIso_symm]
    simpa using (fun x (hx : x ∈ latitudeSpace V e) => block_right_latitude_mem V e w⁻¹ hx)

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

lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

lemma latitudeLaw_invariant (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    [Nontrivial (latitudeSpace V e)] {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta)
    (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    MeasurePreserving (blockIso V u w) (latitudeLaw V e a delta) (latitudeLaw V e a delta) := by
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  let r := restrictIso (latitudeSpace V e) (blockIso V 1 w) (block_right_latitude_stable V e w)
  have hr : MeasurePreserving r SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw := SubsphereRegression.ambientSphereLaw_isometry r
  have hg := (MeasurePreserving.id (betaMeasure a delta)).prod
    ((measurePreserving_mul_left (orthogonalLaw (E := V)) u).prod hr)
  apply preserving_map_of_intertwining (measurable_latitudeSampler V e) hg
    (blockIso V u w).continuous.measurable
  intro z
  change blockIso V (u*z.2.1) 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • blockIso V 1 w (z.2.2 : E)) =
    blockIso V u w (blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E)))
  have he : Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • blockIso V 1 w (z.2.2 : E) =
      blockIso V 1 w (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E)) := by
    simp only [map_add,map_smul,block_right_fix_e]
  rw [he,← blockIso_mul,← blockIso_mul]
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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_invariant := @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_invariant
