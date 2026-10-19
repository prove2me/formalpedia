-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.directionLaw_beta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:44:37.097272+00:00
-- url     : https://prove2.me/submissions/127d359e-eece-4fc1-89ef-824f2a42c88a

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean:L106-L122
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.directionLaw_beta. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_sphere_projection_beta

-- ---- from OAI.Probability.Subsphere.Mixture.Haar ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x

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

lemma nested_starProjection (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    (((U.comap N.subtype).starProjection x : N) : E) = U.starProjection (x : E) := by
  have he : (U.comap N.subtype).starProjection x =
      (⟨U.starProjection (x : E), h (U.orthogonalProjectionOnto (x : E)).prop⟩ : N) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (U.orthogonalProjectionOnto (x : E)).prop
    · intro w hw
      exact U.starProjection_inner_eq_zero (x : E) (w : E) hw
  exact congrArg Subtype.val he

lemma nested_orthogonal_starProjection (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ((((U.comap N.subtype)ᗮ).starProjection x : N) : E) = Uᗮ.starProjection (x : E) := by
  rw [Submodule.starProjection_orthogonal_val,Submodule.starProjection_orthogonal_val]
  change (x : E)-(((U.comap N.subtype).starProjection x : N) : E) = _
  rw [nested_starProjection U N h]

lemma nested_orthogonal_projection_norm (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ‖(U.comap N.subtype)ᗮ.orthogonalProjectionOnto x‖ = ‖Uᗮ.orthogonalProjectionOnto (x : E)‖ := by
  exact congrArg norm (nested_orthogonal_starProjection U N h x)

omit [FiniteDimensional ℝ E] in
lemma nested_rank (U N : Submodule ℝ E) (h : U ≤ N) :
    Module.finrank ℝ (U.comap N.subtype) = Module.finrank ℝ U :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

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

lemma measurable_perpCoordinate (V : Submodule ℝ E) : Measurable (perpCoordinate V) := by
  unfold perpCoordinate
  fun_prop

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
lemma perpCoordinate_blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    perpCoordinate V (blockIso V u w x) = perpCoordinate V x := by
  rw [perpCoordinate,blockIso_apply,map_add,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [perpCoordinate,act_norm]

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

lemma nested_perp_beta (U N : Submodule ℝ E) (hUN : U ≤ N)
    (hU : 0 < Module.finrank ℝ U) (hN : Module.finrank ℝ U < Module.finrank ℝ N) :
    MeasurePreserving (fun x : N => ‖Uᗮ.orthogonalProjectionOnto (x : E)‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ))/2)
        ((Module.finrank ℝ U : ℝ)/2)) := by
  let H := U.comap N.subtype
  have hH : Module.finrank ℝ H = Module.finrank ℝ U := nested_rank U N hUN
  have hdim := H.finrank_add_finrank_orthogonal
  have hHc : 0 < Module.finrank ℝ Hᗮ := by omega
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial H := Module.nontrivial_of_finrank_pos (hH ▸ hU)
  let : Nontrivial Hᗮ := Module.nontrivial_of_finrank_pos hHc
  let : Nontrivial Hᗮᗮ := by simpa using (inferInstance : Nontrivial H)
  have hc : (Module.finrank ℝ Hᗮ : ℝ) =
      (Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ) := by
    have hd : (Module.finrank ℝ H : ℝ)+(Module.finrank ℝ Hᗮ : ℝ) = Module.finrank ℝ N := by
      exact_mod_cast hdim
    rw [hH] at hd
    linarith
  have he : (fun x : N => ‖Hᗮ.orthogonalProjectionOnto x‖^2) =
      (fun x : N => ‖Uᗮ.orthogonalProjectionOnto (x : E)‖^2) := by
    funext x
    rw [nested_orthogonal_projection_norm U N hUN]
  have hHcc : Module.finrank ℝ Hᗮᗮ = Module.finrank ℝ H :=
    congrArg (fun S : Submodule ℝ N => Module.finrank ℝ S) (Submodule.orthogonal_orthogonal H)
  simpa only [he,hHcc,hH,hc] using sphere_projection_beta Hᗮ

lemma directionLaw_beta (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hV : 0 < Module.finrank ℝ V) (hN : Module.finrank ℝ V < Module.finrank ℝ N) :
    MeasurePreserving (perpCoordinate V) (directionLaw V N)
      (betaMeasure (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        ((Module.finrank ℝ V : ℝ)/2)) := by
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  have h := (nested_perp_beta V N hVN hV hN).comp
    (measurePreserving_snd (μ := orthogonalLaw (E := Vᗮ)))
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [directionLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_directionSampler V N)]
  calc
    _ = Measure.map (fun z : Orthogonal Vᗮ × N => perpCoordinate V (z.2 : E))
        ((orthogonalLaw (E := Vᗮ)).prod SubsphereRegression.ambientSphereLaw) := by
      congr 1
      funext z
      exact perpCoordinate_blockIso V 1 z.1 (z.2 : E)
    _ = _ := h.map_eq

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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_beta := @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_beta
