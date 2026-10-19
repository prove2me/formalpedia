-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.block_average_unit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:36:16.10572+00:00
-- url     : https://prove2.me/submissions/917313f2-2907-4342-831d-2a9e9f635ad5

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean:L136-L154
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.block_average_unit. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_integral

-- ---- from OAI.Probability.Subsphere.Mixture.BetaTheory ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
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

lemma haar_scaled_integral [Nontrivial E] (x : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u : Orthogonal E, f (act u x) ∂orthogonalLaw) =
      ∫⁻ y, f (‖x‖ • y) ∂SubsphereRegression.ambientSphereLaw := by
  by_cases hx : x = 0
  · subst x
    simp [act]
  · have he (u : Orthogonal E) : act u x = ‖x‖ • act u (NormedSpace.normalize x) := by
      change u.val x = ‖x‖ • u.val (NormedSpace.normalize x)
      rw [← map_smul,NormedSpace.norm_smul_normalize]
    simp_rw [he]
    exact haar_eval_integral (NormedSpace.norm_normalize hx)
      (f := fun y => f (‖x‖ • y)) (hf.comp (by fun_prop))

lemma measurable_mixtureSampler (V : Submodule ℝ E) : Measurable (mixtureSampler V) := by
  unfold mixtureSampler
  fun_prop

lemma block_average (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (x : E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
      ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ))) =
    ∫⁻ s : V, ∫⁻ t : Vᗮ,
      f (‖V.orthogonalProjectionOnto x‖ • (s : E)+‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E))
      ∂SubsphereRegression.ambientSphereLaw ∂SubsphereRegression.ambientSphereLaw := by
  have hm : Measurable (fun z : Orthogonal V × Orthogonal Vᗮ => f (blockIso V z.1 z.2 x)) :=
    hf.comp (continuous_blockIso V |>.comp (continuous_id.prodMk continuous_const)).measurable
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [blockIso_apply]
  have hright (u : Orthogonal V) :
      (∫⁻ w : Orthogonal Vᗮ,
        f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+(act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E))
        ∂orthogonalLaw) =
      ∫⁻ t : Vᗮ, f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+
        ‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E)) ∂SubsphereRegression.ambientSphereLaw := by
    exact haar_scaled_integral (Vᗮ.orthogonalProjectionOnto x)
      (f := fun t : Vᗮ => f ((act (E := V) u (V.orthogonalProjectionOnto x) : E)+(t : E)))
      (hf.comp (by fun_prop))
  simp_rw [hright]
  have hmf : Measurable (fun s : V => ∫⁻ t : Vᗮ,
      f ((s : E)+‖Vᗮ.orthogonalProjectionOnto x‖ • (t : E))
        ∂SubsphereRegression.ambientSphereLaw) := by
    apply Measurable.lintegral_prod_right
    exact hf.comp (by fun_prop)
  exact haar_scaled_integral (V.orthogonalProjectionOnto x) hmf

lemma block_average_unit (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    {x : E} (hx : ‖x‖ = 1) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
      ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ))) =
    ∫⁻ z : V × Vᗮ, f (mixtureSampler V (perpCoordinate V x,z))
      ∂(SubsphereRegression.ambientSphereLaw (E := V)).prod
        (SubsphereRegression.ambientSphereLaw (E := Vᗮ)) := by
  rw [block_average V x hf]
  have hm : Measurable (fun z : V × Vᗮ => f (mixtureSampler V (perpCoordinate V x,z))) :=
    hf.comp (measurable_mixtureSampler V |>.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_prod (fun z : V × Vᗮ => f (mixtureSampler V (perpCoordinate V x,z))) hm.aemeasurable]
  have hn := V.norm_sq_eq_add_norm_sq_projection x
  rw [hx,one_pow] at hn
  have hleft : Real.sqrt (1-perpCoordinate V x) = ‖V.orthogonalProjectionOnto x‖ := by
    unfold perpCoordinate
    rw [show 1-‖Vᗮ.orthogonalProjectionOnto x‖^2 = ‖V.orthogonalProjectionOnto x‖^2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  change Real.sqrt (1-‖Vᗮ.orthogonalProjectionOnto x‖^2) = ‖V.orthogonalProjectionOnto x‖ at hleft
  simp only [mixtureSampler,perpCoordinate,hleft,Real.sqrt_sq (norm_nonneg _)]

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
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

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

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.block_average_unit := @_root_.OAI.SubsphereCurrent.Mixture.block_average_unit
