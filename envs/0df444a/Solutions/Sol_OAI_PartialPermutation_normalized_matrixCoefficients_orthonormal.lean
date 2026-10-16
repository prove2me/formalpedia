-- Prove2me | solution 1 for OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:57.928151+00:00
-- url     : https://prove2.me/submissions/11a53f23-e266-4ff1-9ddc-1117783944a2

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/MatrixCoefficients.lean:L34-L70
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

lemma normalized_matrixCoefficients_orthonormal {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ V) :
    Orthonormal ℂ (fun p : ι × ι =>
      (Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G) : ℂ) •
        (WithLp.toLp 2 (fun g : G => conj (inner ℂ (e p.1) (ρ g (e p.2)))))) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : (0 : ℝ) < Module.finrank ℂ V := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := V)
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hDc : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hNc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : (Real.sqrt ((Module.finrank ℂ V : ℝ) / Fintype.card G) : ℂ) ^ 2 =
      (Module.finrank ℂ V : ℂ) / Fintype.card G := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_nonneg hD.le hN.le)]
    push_cast
    rfl
  rw [orthonormal_iff_ite]
  intro p q
  rw [inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, PiLp.inner_apply, RCLike.inner_apply,
    starRingEnd_self_apply]
  simp_rw [mul_comm (conj (inner ℂ (e q.1) (ρ _ (e q.2))))]
  have h := matrixCoefficient_orthogonality ρ hρ (e p.1) (e q.1) (e p.2) (e q.2)
  have hs : ∑ g : G, inner ℂ (e p.1) (ρ g (e p.2)) *
      conj (inner ℂ (e q.1) (ρ g (e q.2))) =
      (Fintype.card G : ℂ) * ((inner ℂ (e q.2) (e p.2) /
        (Module.finrank ℂ V : ℂ)) * inner ℂ (e p.1) (e q.1)) := by
    rw [← h]
    field_simp
  rw [hs, orthonormal_iff_ite.mp e.orthonormal, orthonormal_iff_ite.mp e.orthonormal]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2
  · have hpq : p = q := Prod.ext h1 h2
    simp only [ite_eq_left, hpq, ← mul_assoc, ← pow_two, ht]
    field_simp
  · simp [h1, h2, Ne.symm h2, Prod.ext_iff]
  · simp [h1, h2, Prod.ext_iff]
  · simp [h1, h2, Prod.ext_iff]

end MatrixCoefficients
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra


theorem solution : type_of% @_root_.OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal := @_root_.OAI.PartialPermutation.normalized_matrixCoefficients_orthonormal
