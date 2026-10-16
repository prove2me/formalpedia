-- Prove2me | solution 1 for OAI.PartialPermutation.character_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:45:22.223472+00:00
-- url     : https://prove2.me/submissions/7e9b85e4-2b40-4311-a206-ab577e7ac1cf

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Characters.lean:L55-L79
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.character_kernel_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage

-- ---- from OAI.RepresentationTheory.PartialPermutation.SchurAverage ----
namespace OAI

section

open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra

namespace PartialPermutation

section SchurAverage
variable {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

omit [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ] in
lemma conjugateAverage_eq_averageMap (A : Module.End ℂ V) :
    conjugateAverage ρ A =
      letI := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
      (ρ.linHom ρ).averageMap A := by
  let := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  simp [conjugateAverage, Representation.averageMap, GroupAlgebra.average,
    Representation.linHom_apply, ← Module.End.mul_eq_comp, mul_assoc]

lemma conjugateAverage_scalar (A : Module.End ℂ V) :
    ∃ c : ℂ, conjugateAverage ρ A = c • (1 : Module.End ℂ V) := by
  let := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  let F : (ρ.linHom ρ).invariants :=
    ⟨(ρ.linHom ρ).averageMap A, (ρ.linHom ρ).averageMap_invariant A⟩
  let T := Representation.invariantsEquivIntertwiningMap ρ ρ F
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective T
  refine ⟨c, ?_⟩
  rw [Representation.IntertwiningMap.algebraMap_apply] at hc
  have h := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • (1 : Module.End ℂ V) = (ρ.linHom ρ).averageMap A at h
  rw [conjugateAverage_eq_averageMap]
  exact h.symm

omit [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ] in
lemma trace_conjugateAverage (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (conjugateAverage ρ A) = LinearMap.trace ℂ V A := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht (g : G) : LinearMap.trace ℂ V (ρ g * A * ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp [conjugateAverage, ht, hc]

lemma conjugateAverage_eq_trace (A : Module.End ℂ V) :
    conjugateAverage ρ A =
      (LinearMap.trace ℂ V A / (Module.finrank ℂ V : ℂ)) • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ := conjugateAverage_scalar ρ A
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have : Nontrivial V := by
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
      exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have ht := trace_conjugateAverage ρ A
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  rw [hc, ← ht, mul_div_cancel_right₀ _ hd]

end SchurAverage
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.MatrixCoefficients ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra

namespace PartialPermutation

section MatrixCoefficients
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) [Representation.IsIrreducible ρ]
include hρ

lemma matrixCoefficient_orthogonality (x y u v : V) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, inner ℂ x (ρ g u) * conj (inner ℂ y (ρ g v)) =
      (inner ℂ v u / (Module.finrank ℂ V : ℂ)) * inner ℂ x y := by
  have h := congrArg (fun A : Module.End ℂ V => inner ℂ x (A y))
    (conjugateAverage_eq_trace ρ (InnerProductSpace.rankOne ℂ u v).toLinearMap)
  have hu (g : G) : inner ℂ v (ρ g⁻¹ y) = conj (inner ℂ y (ρ g v)) := by
    rw [← inner_conj_symm]
    have ht := hρ g v (ρ g⁻¹ y)
    simpa using ht.symm
  simpa [conjugateAverage, LinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    InnerProductSpace.trace_rankOne, inner_smul_right, inner_sum, hu, mul_comm] using h

end MatrixCoefficients
end PartialPermutation

end

end OAI

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

variable [Representation.IsIrreducible ρ]

lemma character_kernel_identity :
    complexFourier ρ (fun g => ((Module.finrank ℂ V : ℂ) / Fintype.card G) *
      conj (ρ.character g)) = 1 := by
  classical
  let e := stdOrthonormalBasis ℂ V
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply]
  simp only [inner_sum, inner_smul_right, mul_assoc, ← Finset.mul_sum]
  have hs : (Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ρ.character g) * inner ℂ x (ρ g y) =
      (Module.finrank ℂ V : ℂ)⁻¹ * inner ℂ x y := by
    simp_rw [Representation.character, LinearMap.trace_eq_sum_inner _ e, map_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hc (i : Fin (Module.finrank ℂ V)) :=
      matrixCoefficient_orthogonality ρ hρ x (e i) y (e i)
    simp_rw [mul_comm (conj _), hc, div_eq_mul_inv]
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ => (Module.finrank ℂ V : ℂ)⁻¹ * z) (e.sum_inner_mul_inner x y)
  rw [div_eq_mul_inv, mul_assoc, hs, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]

end
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate MonoidAlgebra


theorem solution : type_of% @_root_.OAI.PartialPermutation.character_kernel_identity := @_root_.OAI.PartialPermutation.character_kernel_identity
