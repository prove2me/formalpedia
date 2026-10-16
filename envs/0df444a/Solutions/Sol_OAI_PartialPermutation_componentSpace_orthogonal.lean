-- Prove2me | solution 1 for OAI.PartialPermutation.componentSpace_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:53:22.272597+00:00
-- url     : https://prove2.me/submissions/68c0f53c-7938-4ad8-9148-9e928afa557e

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ComponentGeometry.lean:L51-L70
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.componentSpace_orthogonal. The node keeps its source
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

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSpace_invariant (c : isotypicComponents ℂ[G] ρ.asModule)
    (g : G) (v : V) (hv : v ∈ componentSpace ρ c) : ρ g v ∈ componentSpace ρ c := by
  have h := c.val.smul_mem (MonoidAlgebra.single g (1 : ℂ)) hv
  change ρ.asAlgebraHom (MonoidAlgebra.single g 1) v ∈ c.val at h
  change ρ g v ∈ c.val
  simpa using h

omit [Fintype G] in
lemma componentSpace_projection_commute
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (c : isotypicComponents ℂ[G] ρ.asModule) (g : G) (v : V) :
    ρ g ((componentSpace ρ c).starProjection v) =
      (componentSpace ρ c).starProjection (ρ g v) := by
  have he : (componentSpace ρ c).map (ρ g) = componentSpace ρ c := by
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      exact componentSpace_invariant ρ c g v hv
    · intro v hv
      exact ⟨ρ g⁻¹ v, componentSpace_invariant ρ c g⁻¹ v hv, by simp⟩
  have hm := ((ρ g).isometryOfInner (hρ g)).map_starProjection (componentSpace ρ c) v
  simpa only [LinearMap.coe_isometryOfInner, LinearMap.isometryOfInner_toLinearMap, he] using hm

omit [Fintype G] in
lemma componentSpace_orthogonal
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    OrthogonalFamily ℂ (fun c => componentSpace ρ c) (fun c => (componentSpace ρ c).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro c d hcd x hx
  apply (Submodule.starProjection_apply_eq_zero_iff (K := componentSpace ρ d)).mp
  let p : ρ.IntertwiningMap ρ :=
    { toLinearMap := (componentSpace ρ d).starProjection.toLinearMap
      isIntertwining' g := by
        ext v
        exact (componentSpace_projection_commute ρ hρ d g v).symm }
  let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ p
  have hi : c.val.IsFullyInvariant := .of_mem_isotypicComponents c.property
  have hmem : f x ∈ c.val := hi f hx
  have hmem' : f x ∈ d.val := (componentSpace ρ d).starProjection_apply_mem x
  have hd : Disjoint c.val d.val :=
    (sSupIndep_isotypicComponents ℂ[G] ρ.asModule).pairwiseDisjoint c.property d.property
      (Subtype.coe_ne_coe.mpr hcd)
  exact Submodule.disjoint_def.mp hd (f x) hmem hmem'

end Geometry
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


theorem solution : type_of% @_root_.OAI.PartialPermutation.componentSpace_orthogonal := @_root_.OAI.PartialPermutation.componentSpace_orthogonal
