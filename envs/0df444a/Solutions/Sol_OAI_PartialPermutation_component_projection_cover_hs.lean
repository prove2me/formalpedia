-- Prove2me | solution 1 for OAI.PartialPermutation.component_projection_cover_hs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:01:33.822602+00:00
-- url     : https://prove2.me/submissions/a14c2447-fb42-43e7-8b0c-1ab649dabe6e

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean:L101-L118
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.component_projection_cover_hs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Theorems.Thm_OAI_PartialPermutation_componentSpace_orthogonal

-- ---- from OAI.RepresentationTheory.PartialPermutation.HilbertSchmidt ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

lemma hsNormSq_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ V)
    (A : Module.End ℂ V) : hsNormSq A = ∑ i, ‖A (e i)‖ ^ 2 := by
  rw [hsNormSq, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (e i))

lemma hsNormSq_adjoint (A : Module.End ℂ V) : hsNormSq (LinearMap.adjoint A) = hsNormSq A := by
  unfold hsNormSq
  rw [LinearMap.adjoint_adjoint, LinearMap.trace_mul_comm]

lemma adjoint_mul_eq (A B : Module.End ℂ V) :
    LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A :=
  LinearMap.adjoint_comp A B

lemma adjoint_projection_eq (W : Submodule ℂ V) :
    LinearMap.adjoint W.starProjection.toLinearMap = W.starProjection.toLinearMap := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [LinearMap.adjoint_inner_right]
  exact W.inner_starProjection_left_eq_right u v

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ConvolutionKernels ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
open scoped BigOperators ComplexConjugate

noncomputable section

section
variable {G : Type*} [Group G] [Fintype G]

lemma projection_kernel_mul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (W : Submodule ℂ V) (P : Module.End ℂ V)
    (hP : LinearMap.adjoint P = P) (hact : ∀ x ∈ W, P x = x) :
    W.starProjection.toLinearMap * P = W.starProjection.toLinearMap := by
  have he : P * W.starProjection.toLinearMap = W.starProjection.toLinearMap := by
    ext x
    exact hact _ (W.starProjection_apply_mem x)
  have he' := congrArg LinearMap.adjoint he
  simpa only [adjoint_mul_eq, adjoint_projection_eq, hP] using he'

end
end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ComponentGeometry ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
section Geometry
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
lemma iSup_componentSpace : ⨆ c, componentSpace ρ c = ⊤ := by
  change (⨆ c : isotypicComponents ℂ[G] ρ.asModule, c.val.restrictScalars ℂ) = ⊤
  rw [← Submodule.restrictScalars_iSup, ← sSup_eq_iSup', sSup_isotypicComponents,
    Submodule.restrictScalars_top]

lemma sum_component_projections
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] (v : V) :
    ∑ c, (componentSpace ρ c).starProjection v = v :=
  (componentSpace_orthogonal ρ hρ).sum_projection_of_mem_iSup v
    (by rw [iSup_componentSpace]; trivial)

lemma sum_component_norm_sq
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] (v : V) :
    ∑ c, ‖(componentSpace ρ c).starProjection v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := (componentSpace_orthogonal ρ hρ).norm_sum
    (fun c => (componentSpace ρ c).orthogonalProjectionOnto v) Finset.univ
  change ‖∑ c, (componentSpace ρ c).starProjection v‖ ^ 2 =
    ∑ c, ‖(componentSpace ρ c).starProjection v‖ ^ 2 at h
  rw [sum_component_projections ρ hρ] at h
  exact h.symm

end Geometry
end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ProjectionCovers ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

section Cover
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    {ι : Type*} [Fintype ι] (P : ι → Module.End ℂ V)
    (hP : ∀ i, LinearMap.adjoint (P i) = P i)
    (hcover : ∀ c : isotypicComponents ℂ[G] ρ.asModule,
      ∃ i, ∀ x ∈ componentSpace ρ c, P i x = x)

include ρ hρ hP hcover

lemma component_projection_cover_norm (v : V) : ‖v‖^2 ≤ ∑ i, ‖P i v‖^2 := by
  let : Fintype (isotypicComponents ℂ[G] ρ.asModule) := Fintype.ofFinite _
  calc
    _ = ∑ c, ‖(componentSpace ρ c).starProjection v‖^2 :=
      (sum_component_norm_sq ρ hρ v).symm
    _ ≤ ∑ c, ∑ i, ‖(componentSpace ρ c).starProjection (P i v)‖^2 := by
      apply Finset.sum_le_sum
      intro c _
      obtain ⟨i, hi⟩ := hcover c
      have he := congrArg (fun A : Module.End ℂ V => A v)
        (projection_kernel_mul (componentSpace ρ c) (P i) (hP i) hi)
      change (componentSpace ρ c).starProjection (P i v) =
        (componentSpace ρ c).starProjection v at he
      rw [← he]
      exact Finset.single_le_sum (fun j _ =>
        sq_nonneg (‖(componentSpace ρ c).starProjection (P j v)‖)) (Finset.mem_univ i)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact sum_component_norm_sq ρ hρ (P i v)

lemma component_projection_cover_hs (A : Module.End ℂ V) :
    hsNormSq A ≤ ∑ i, hsNormSq (A * P i) := by
  let e := stdOrthonormalBasis ℂ V
  calc
    _ = ∑ j, ‖LinearMap.adjoint A (e j)‖^2 := by
      rw [← hsNormSq_adjoint A, hsNormSq_eq_sum e]
    _ ≤ ∑ j, ∑ i, ‖P i (LinearMap.adjoint A (e j))‖^2 :=
      Finset.sum_le_sum (fun j _ => component_projection_cover_norm ρ hρ P hP hcover _)
    _ = ∑ i, hsNormSq (P i * LinearMap.adjoint A) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [hsNormSq_eq_sum e]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hsNormSq_adjoint (A * P i), adjoint_mul_eq, hP]

end Cover
end
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.PartialPermutation.component_projection_cover_hs := @_root_.OAI.PartialPermutation.component_projection_cover_hs
