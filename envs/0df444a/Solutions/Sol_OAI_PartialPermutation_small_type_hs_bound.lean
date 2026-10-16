-- Prove2me | solution 1 for OAI.PartialPermutation.small_type_hs_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:58:59.424573+00:00
-- url     : https://prove2.me/submissions/ee2f11fc-db80-498c-99a7-9db81ad406cb

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean:L49-L67
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.small_type_hs_bound. The node keeps its source
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
import Theorems.Thm_OAI_PartialPermutation_complexFourier_smallTypeKernel
import Theorems.Thm_OAI_PartialPermutation_finite_group_plancherel
import Theorems.Thm_OAI_PartialPermutation_fourier_bessel
import Theorems.Thm_OAI_PartialPermutation_leftKernel_l2

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

lemma hsNormSq_adjoint (A : Module.End ℂ V) : hsNormSq (LinearMap.adjoint A) = hsNormSq A := by
  unfold hsNormSq
  rw [LinearMap.adjoint_adjoint, LinearMap.trace_mul_comm]

lemma adjoint_mul_eq (A B : Module.End ℂ V) :
    LinearMap.adjoint (A * B) = LinearMap.adjoint B * LinearMap.adjoint A :=
  LinearMap.adjoint_comp A B

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

lemma complexFourier_leftKernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) :
    complexFourier ρ (leftKernel H k f) =
      complexFourier (ρ.comp H.subtype) k * complexFourier ρ (fun g => (f g : ℂ)) := by
  classical
  unfold complexFourier leftKernel
  simp_rw [Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Fintype.sum_equiv (Equiv.mulLeft (h : G)⁻¹)
  intro g
  simp only [smul_mul_smul_comm, ← map_mul, MonoidHom.comp_apply, Equiv.coe_mulLeft,
    Subgroup.subtype_apply, mul_inv_cancel_left]

lemma inverse_rightCap (H : Subgroup G) (f : G → ℝ) (B : ℝ)
    (hcap : LeftCosetCap f H B) : RightCosetCap (fun g => f g⁻¹) H B := by
  intro g
  have he : ∑ h : H, f (((h : G) * g)⁻¹) = ∑ h : H, f (g⁻¹ * h) := by
    apply Fintype.sum_equiv (Equiv.inv H)
    intro h
    simp
  rw [he]
  exact hcap g⁻¹

lemma mass_inverse (f : G → ℝ) : mass (fun g => f g⁻¹) = mass f := by
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

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

lemma smallTypeKernel_energy (R : ℝ) :
    (Fintype.card G : ℝ) * ∑ g, ‖smallTypeKernel G R g‖^2 = smallDegreeSum G R := by
  rw [finite_group_plancherel]
  unfold smallDegreeSum
  apply Finset.sum_congr rfl
  intro c _
  rw [complexFourier_smallTypeKernel]
  split_ifs <;> simp [hsNormSq, LinearMap.trace_one, pow_two]

lemma kernel_hs_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (k : H → ℂ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier (ρ.comp H.subtype) k * complexFourier ρ (fun g => f g)) ≤
      B * mass f * ((Fintype.card H : ℝ) * ∑ h, ‖k h‖^2) := by
  have hc : (H.index : ℝ) * (Fintype.card H : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using H.index_mul_card)
  have hi : (H.index : ℝ) ≠ 0 := by exact_mod_cast H.index_ne_zero_of_finite
  calc
    _ ≤ (Fintype.card G : ℝ) * ∑ g, ‖leftKernel H k f g‖^2 := by
      rw [← complexFourier_leftKernel]
      exact fourier_bessel ρ hρ _
    _ ≤ (Fintype.card G : ℝ) * (B / H.index * mass f * ∑ h, ‖k h‖^2) :=
      mul_le_mul_of_nonneg_left (leftKernel_l2 H k f B hf hcap) (by positivity)
    _ = _ := by rw [← hc]; field_simp

lemma small_type_hs_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (R : ℝ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier ρ (fun g => f g) *
        complexFourier (ρ.comp H.subtype) (smallTypeKernel H R)) ≤
      B * mass f * smallDegreeSum H R := by
  have hi := kernel_hs_energy ρ hρ H (smallTypeKernel H R) (fun g => f g⁻¹) B
    (fun g => hf _) (inverse_rightCap H f B hcap)
  rw [mass_inverse, smallTypeKernel_energy] at hi
  have hP := complexFourier_selfAdjoint (G := H) (ρ.comp H.subtype)
    (fun (g : H) => hρ g) (smallTypeKernel H R) (smallTypeKernel_inv R)
  have hA : LinearMap.adjoint (complexFourier ρ (fun g => (f g⁻¹ : ℂ))) =
      complexFourier ρ (fun g => (f g : ℂ)) := by
    rw [complexFourier_adjoint ρ hρ]
    simp
  rw [← hsNormSq_adjoint (_ * _), adjoint_mul_eq, hA, hP] at hi
  exact hi

section Cover
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    {ι : Type*} [Fintype ι] (P : ι → Module.End ℂ V)
    (hP : ∀ i, LinearMap.adjoint (P i) = P i)
    (hcover : ∀ c : isotypicComponents ℂ[G] ρ.asModule,
      ∃ i, ∀ x ∈ componentSpace ρ c, P i x = x)

include ρ hρ hP hcover

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


theorem solution : type_of% @_root_.OAI.PartialPermutation.small_type_hs_bound := @_root_.OAI.PartialPermutation.small_type_hs_bound
