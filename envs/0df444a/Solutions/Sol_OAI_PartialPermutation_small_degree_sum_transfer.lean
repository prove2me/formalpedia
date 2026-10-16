-- Prove2me | solution 1 for OAI.PartialPermutation.small_degree_sum_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:14:38.228978+00:00
-- url     : https://prove2.me/submissions/6df25976-5139-452c-b558-995dcf6f1587

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/DegreeTransfer.lean:L51-L74
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.small_degree_sum_transfer. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Theorems.Thm_OAI_PartialPermutation_component_kernel
import Theorems.Thm_OAI_PartialPermutation_component_projection_cover_hs
import Theorems.Thm_OAI_PartialPermutation_smallTypeKernel_identity_of_kernel
import Theorems.Thm_OAI_PartialPermutation_small_type_hs_bound

-- ---- from OAI.RepresentationTheory.PartialPermutation.Characters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
open scoped BigOperators ComplexConjugate MonoidAlgebra

noncomputable section
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
include hρ

omit [Fintype G] in
lemma unitary_adjoint (g : G) : LinearMap.adjoint (ρ g) = ρ g⁻¹ := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [LinearMap.adjoint_inner_right]
  have h := hρ g u (ρ g⁻¹ v)
  simpa using h

omit [Fintype G] in
lemma unitary_character_inv (g : G) : ρ.character g⁻¹ = conj (ρ.character g) := by
  let e := stdOrthonormalBasis ℂ V
  rw [Representation.character, Representation.character, ← unitary_adjoint ρ hρ,
    LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_right, inner_conj_symm]

variable [Representation.IsIrreducible ρ]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.RegularRepresentation ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
variable (G : Type*) [Group G] [Fintype G]

lemma regularRep_unitary (g : G) (f k : EuclideanSpace ℂ G) :
    inner ℂ (regularRep G g f) (regularRep G g k) = inner ℂ f k := by
  simp only [PiLp.inner_apply, regularRep_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun h => rfl)

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Plancherel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma componentRep_unitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (c : isotypicComponents ℂ[G] ρ.asModule) : IsUnitary (componentRep ρ c) := by
  intro g x y
  exact hρ g x.val y.val

lemma irreducibleRep_unitary (c : IrreducibleIndex G) :
    IsUnitary (G := G) (V := irreducibleSpace c) (irreducibleRep c) :=
  componentRep_unitary (regularRep G) (regularRep_unitary G) c

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

lemma complexFourier_adjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (f : G → ℂ) :
    LinearMap.adjoint (complexFourier ρ f) = complexFourier ρ (fun g => conj (f g⁻¹)) := by
  unfold complexFourier
  simp only [map_sum, map_smulₛₗ, unitary_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp

lemma complexFourier_selfAdjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (f : G → ℂ) (hf : ∀ g, f g⁻¹ = conj (f g)) :
    LinearMap.adjoint (complexFourier ρ f) = complexFourier ρ f := by
  rw [complexFourier_adjoint ρ hρ]
  simp [hf]

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

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSpace_invariant (c : isotypicComponents ℂ[G] ρ.asModule)
    (g : G) (v : V) (hv : v ∈ componentSpace ρ c) : ρ g v ∈ componentSpace ρ c := by
  have h := c.val.smul_mem (MonoidAlgebra.single g (1 : ℂ)) hv
  change ρ.asAlgebraHom (MonoidAlgebra.single g 1) v ∈ c.val at h
  change ρ g v ∈ c.val
  simpa using h

end Geometry
end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ProjectionEnergy ----
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

lemma centralCharacterKernel_inv {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (τ : Representation ℂ G W) (hτ : IsUnitary τ) (g : G) :
    centralCharacterKernel τ g⁻¹ = conj (centralCharacterKernel τ g) := by
  simp [centralCharacterKernel, unitary_character_inv τ hτ]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.SmallKernels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma smallTypeKernel_inv (R : ℝ) (g : G) :
    smallTypeKernel G R g⁻¹ = conj (smallTypeKernel G R g) := by
  simp only [smallTypeKernel, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp [centralCharacterKernel_inv _ (irreducibleRep_unitary c)]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.DegreeTransfer ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

lemma joint_small_type_cover (hb : 0 < b) (hD : 0 < Module.finrank ℂ V)
    (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (c : isotypicComponents ℂ[↥(⨆ i, H i)] (Representation.asModule (ρ.comp (⨆ i, H i).subtype))) :
    ∃ i, ∀ x ∈ componentSpace (ρ.comp (⨆ i, H i).subtype) c,
      complexFourier (ρ.comp (H i).subtype)
        (smallTypeKernel (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ)))) x = x := by
  let J := ⨆ i, H i
  let ρJ : Representation ℂ J V := ρ.comp J.subtype
  obtain ⟨i, d, k, hd, hk, hki, hka⟩ := component_kernel ρ H hb hD hρ hcomm c
  let σ : Subrepresentation (ρ.comp (H i).subtype) :=
    { toSubmodule := componentSpace ρJ c
      apply_mem_toSubmodule := fun g v hv =>
        componentSpace_invariant ρJ c ⟨g, le_iSup H i g.property⟩ v hv }
  have hu : IsUnitary σ.toRepresentation := fun g x y => hρ g x y
  have ha : complexFourier σ.toRepresentation k = 1 := by
    ext x
    rw [complexFourier_subrep]
    exact hka x.val x.property
  have hs := smallTypeKernel_identity_of_kernel σ.toRepresentation hu k d
    ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) hd hk ha
  refine ⟨i, fun x hx => ?_⟩
  have ht := congrArg (fun A : Module.End ℂ σ.toSubmodule => A ⟨x, hx⟩) hs
  have ht' := congrArg (fun y : σ.toSubmodule => (y : V)) ht
  rw [complexFourier_subrep] at ht'
  exact ht'

theorem small_degree_sum_transfer [Representation.IsIrreducible ρ]
    (hb : 0 < b) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : ∀ i, LeftCosetCap f (H i) B) :
    (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * ∑ i, smallDegreeSum (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : 0 < Module.finrank ℂ V := Module.finrank_pos
  let R := (Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))
  let P (i : Fin b) := complexFourier (ρ.comp (H i).subtype) (smallTypeKernel (H i) R)
  have hp (i : Fin b) : LinearMap.adjoint (P i) = P i :=
    complexFourier_selfAdjoint (G := H i) (ρ.comp (H i).subtype)
      (fun (g : H i) => hρ g) _ (smallTypeKernel_inv R)
  have hcover := component_projection_cover_hs (G := ↥(⨆ i, H i))
    (ρ.comp (⨆ i, H i).subtype) (fun (g : ↥(⨆ i, H i)) => hρ g) P hp
    (joint_small_type_cover ρ H hb hD hρ hcomm) (complexFourier ρ (fun g => f g))
  calc
    _ ≤ (Module.finrank ℂ V : ℝ) * ∑ i, hsNormSq (complexFourier ρ (fun g => f g) * P i) :=
      mul_le_mul_of_nonneg_left hcover (by positivity)
    _ = ∑ i, (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ (fun g => f g) * P i) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ i, B * mass f * smallDegreeSum (H i) R :=
      Finset.sum_le_sum (fun i _ => small_type_hs_bound ρ hρ (H i) R f B hf (hcap i))
    _ = _ := by rw [Finset.mul_sum]

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
open scoped MonoidAlgebra BigOperators
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.PartialPermutation.small_degree_sum_transfer := @_root_.OAI.PartialPermutation.small_degree_sum_transfer
