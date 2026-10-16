-- Prove2me | solution 1 for OAI.PartialPermutation.exists_isotypicKernelModel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:09:03.582686+00:00
-- url     : https://prove2.me/submissions/a3108d3d-f6a5-43e3-a44c-ad42271e78d0

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/IsotypicKernels.lean:L63-L113
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.exists_isotypicKernelModel. The node keeps its source
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
import Theorems.Thm_OAI_PartialPermutation_character_kernel_identity

-- ---- from OAI.RepresentationTheory.PartialPermutation.Characters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

lemma character_norm_sq_sum : ∑ g, ‖ρ.character g‖ ^ 2 = (Fintype.card G : ℝ) := by
  let := invertibleOfNonzero (show (Nat.card G : ℂ) ≠ 0 by simp [Nat.card_eq_fintype_card])
  have h := Representation.char_orthonormal ρ ρ
  have he : Nonempty (Representation.Equiv ρ ρ) := ⟨Representation.Equiv.refl ρ⟩
  simp only [ite_eq_left he, unitary_character_inv ρ hρ] at h
  have hN : (Nat.card G : ℂ) ≠ 0 := by simp [Nat.card_eq_fintype_card]
  have hsum : (∑ g, ρ.character g * conj (ρ.character g)) = (Nat.card G : ℂ) := by
    simpa [hN, mul_assoc] using congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) h
  have ht := congrArg Complex.re hsum
  simpa only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, Complex.natCast_re, Nat.card_eq_fintype_card] using ht

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.IsotypicMatrices ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PartialPermutation

section Burnside
variable {R S : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup S]
    [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]
    [IsSimpleModule R S] [FiniteDimensional ℂ S]

lemma simple_action_surjective : Function.Surjective (Algebra.lsmul ℂ ℂ S (A := R)) := by
  intro f
  let E := Module.End R S
  let f' : Module.End E S :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => by
        obtain ⟨t, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ
          (A := R) (V := S)).surjective c
        change f (t • x) = t • f x
        exact f.map_smul t x }
  have : Module.Finite E S := Module.Finite.of_restrictScalars_finite ℂ E S
  obtain ⟨r, hr⟩ := (Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := S)) f'
  refine ⟨r, ?_⟩
  ext x
  exact congrArg (fun A : Module.End E S => A x) hr

end Burnside

section Isotypic
variable {R M S : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [AddCommGroup S] [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]

lemma isotypicLift_action {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (r : R) :
    isotypicLift e (Algebra.lsmul ℂ ℂ S r) = Algebra.lsmul ℂ ℂ M r := by
  ext x
  apply (e.restrictScalars ℂ).injective
  simp [isotypicLift, diagonalEnd, LinearEquiv.conjAlgEquiv_apply, map_smul]
  ext i
  rfl

lemma isotypicLift_range [IsSimpleModule R S] [FiniteDimensional ℂ S]
    {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (A : Module.End ℂ S) :
    ∃ r : R, isotypicLift e A = Algebra.lsmul ℂ ℂ M r := by
  obtain ⟨r, rfl⟩ := simple_action_surjective (R := R) A
  exact ⟨r, isotypicLift_action e r⟩

lemma mem_isotypicOrbitMap_range {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (v : M) :
    v ∈ LinearMap.range (isotypicOrbitMap e v) := by
  refine ⟨1, ?_⟩
  simp [isotypicOrbitMap]

lemma isotypicOrbitMap_range_invariant {m : ℕ} (e : M ≃ₗ[R] Fin m → S)
    (v : M) (r : R) (x : M) (hx : x ∈ LinearMap.range (isotypicOrbitMap e v)) :
    r • x ∈ LinearMap.range (isotypicOrbitMap e v) := by
  obtain ⟨A, rfl⟩ := hx
  refine ⟨Algebra.lsmul ℂ ℂ S r * A, ?_⟩
  change isotypicLift e (_ * A) v = r • (isotypicLift e A v)
  rw [map_mul, Module.End.mul_apply, isotypicLift_action]
  rfl

lemma finrank_isotypicOrbitMap_range [FiniteDimensional ℂ S] {m : ℕ}
    (e : M ≃ₗ[R] Fin m → S) (v : M) :
    Module.finrank ℂ (LinearMap.range (isotypicOrbitMap e v)) ≤
      (Module.finrank ℂ S) ^ 2 := by
  calc
    _ ≤ Module.finrank ℂ (Module.End ℂ S) := LinearMap.finrank_range_le _
    _ = _ := by rw [Module.finrank_linearMap]; ring

end Isotypic

end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.IsotypicKernels ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
open scoped MonoidAlgebra BigOperators ComplexConjugate

noncomputable section
variable {G M : Type*} [Group G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]

lemma ofModule'_apply (g : G) (x : M) :
    Representation.ofModule' (k := ℂ) (G := G) M g x =
      (MonoidAlgebra.single g (1 : ℂ)) • x := by
  rw [← Representation.asAlgebraHom_single_one, ofModule'_algebra]
  rfl

lemma ofModule'_irreducible [IsSimpleModule ℂ[G] M] :
    Representation.IsIrreducible (Representation.ofModule' (k := ℂ) (G := G) M) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr (ofModule'ModuleEquiv (G := G) (M := M))

variable [Fintype G]

lemma exists_isotypicKernelModel [FiniteDimensional ℂ M] [Nontrivial M]
    (h : IsIsotypic ℂ[G] M)
    (hu : ∀ (g : G) (x y : M), inner ℂ ((MonoidAlgebra.single g (1 : ℂ)) • x)
      ((MonoidAlgebra.single g (1 : ℂ)) • y) = inner ℂ x y) :
    Nonempty (IsotypicKernelModel G M) := by
  have : Module.Finite ℂ[G] M := Module.Finite.of_restrictScalars_finite ℂ ℂ[G] M
  obtain ⟨m, hm, S, hS, ⟨e⟩⟩ := h.linearEquiv_fun
  let : IsSimpleModule ℂ[G] S := hS
  have : Nontrivial S := IsSimpleModule.nontrivial ℂ[G] S
  have : FiniteDimensional ℂ S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℂ) S.subtype_injective
  let : NormedAddCommGroup S := inferInstanceAs (NormedAddCommGroup (S.restrictScalars ℂ))
  let : InnerProductSpace ℂ S := inferInstanceAs (InnerProductSpace ℂ (S.restrictScalars ℂ))
  let σ := Representation.ofModule' (k := ℂ) (G := G) S
  have : Representation.IsIrreducible σ := ofModule'_irreducible
  have hσ : IsUnitary σ := by
    intro g x y
    change inner ℂ (Representation.ofModule' (k := ℂ) (G := G) S g x)
      (Representation.ofModule' (k := ℂ) (G := G) S g y) = _
    rw [ofModule'_apply, ofModule'_apply]
    exact hu g x.val y.val
  let k : G → ℂ := fun g => ((Module.finrank ℂ S : ℂ) / Fintype.card G) * conj (σ.character g)
  let F := (isotypicLift e).comp (Matrix.toLinAlgEquiv (Module.finBasis ℂ S)).toAlgHom
  refine ⟨{ degree := Module.finrank ℂ S
            degree_pos := Module.finrank_pos
            lift := F
            lift_image := fun A => isotypicLift_range e _
            orbit := fun v => ⟨LinearMap.range (isotypicOrbitMap e v),
              mem_isotypicOrbitMap_range e v, isotypicOrbitMap_range_invariant e v,
              finrank_isotypicOrbitMap_range e v⟩
            kernel := k
            kernel_norm := ?_
            kernel_inv := ?_
            kernel_action := ?_ }⟩
  · have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [k, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_conj,
      mul_pow, ← Finset.mul_sum, character_norm_sq_sum σ hσ]
    field_simp
  · intro g
    simp [k, unitary_character_inv σ hσ]
  · have he' := congrArg (isotypicLift e) (character_kernel_identity σ hσ)
    have ha (g : G) : isotypicLift e (σ g) =
        Algebra.lsmul ℂ ℂ M (MonoidAlgebra.single g (1 : ℂ)) := by
      change isotypicLift e (Representation.ofModule' (k := ℂ) (G := G) S g) = _
      rw [← Representation.asAlgebraHom_single_one, ofModule'_algebra, isotypicLift_action]
    change isotypicLift e (complexFourier σ k) = isotypicLift e 1 at he'
    simp only [complexFourier, map_sum, map_smul, map_one, ha] at he'
    intro x
    have ht := congrArg (fun A : Module.End ℂ M => A x) he'
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Algebra.lsmul_apply,
      Module.End.one_apply] using ht

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
open scoped BigOperators
open scoped MonoidAlgebra BigOperators
open scoped MonoidAlgebra BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.PartialPermutation.exists_isotypicKernelModel := @_root_.OAI.PartialPermutation.exists_isotypicKernelModel
