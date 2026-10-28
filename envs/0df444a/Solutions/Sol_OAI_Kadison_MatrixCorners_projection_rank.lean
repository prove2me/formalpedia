-- Prove2me | solution 1 for OAI.Kadison.MatrixCorners.projection_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:18:24.948485+00:00
-- url     : https://prove2.me/submissions/47ec5631-7df2-4064-9b7a-1f027bf3b4a3

import Mathlib
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C013

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.MatrixTrace

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →ₗ[ℂ] ℂ)

variable (htr : ∀ x y, φ (x * y) = φ (y * x)) (hunit : φ 1 = 1)

include htr

lemma off_diagonal (i j : I) (hij : i ≠ j) : φ (single i j 1) = 0 := by
  have h := htr (single i i 1) (single i j 1)
  have hz : (single i j (1 : ℂ)) * single i i 1 = 0 :=
    Matrix.single_mul_single_of_ne 1 i j i hij.symm 1
  simpa [hz] using h

lemma diagonal_eq (i j : I) : φ (single i i 1) = φ (single j j 1) := by
  simpa using htr (single i j 1) (single j i 1)

variable [Nonempty I]

include hunit

lemma diagonal (i : I) : φ (single i i 1) = (Fintype.card I : ℂ)⁻¹ := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ) * φ (single i i 1) = 1 := by
    calc
      _ = ∑ j : I, φ (single j j 1) := by
        simp only [← diagonal_eq φ htr i, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ = φ 1 := by rw [← map_sum, Matrix.sum_single_one]
      _ = 1 := hunit
  apply (mul_left_cancel₀ hcard)
  rw [h, mul_inv_cancel₀ hcard]

lemma unique (a : Matrix I I ℂ) : φ a = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  have hsingle (i j : I) : φ (single i j (a i j)) =
      if i = j then (Fintype.card I : ℂ)⁻¹ * a i j else 0 := by
    have hs : single i j (a i j) = a i j • (single i j (1 : ℂ)) := by
      ext k l
      simp [Matrix.single]
    rw [hs, map_smul]
    by_cases hij : i = j
    · subst j
      rw [diagonal φ htr hunit, ite_eq_left rfl]
      exact mul_comm _ _
    · rw [off_diagonal φ htr i j hij, ite_eq_right hij, smul_zero]
  calc
    φ a = ∑ i : I, ∑ j : I, φ (single i j (a i j)) := by
      nth_rw 1 [Matrix.matrix_eq_sum_single a]
      simp only [map_sum]
    _ = (Fintype.card I : ℂ)⁻¹ * a.trace := by
      simp [hsingle, Matrix.trace, ← Finset.mul_sum]

end Kadison.MatrixTrace
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [StarOrderedRing A] in
include hτ h1 in
lemma stage_trace (a : Matrix I I ℂ) :
    τ (φ a) = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  apply MatrixTrace.unique (τ.toLinearMap.comp φ.toLinearMap)
  · intro x y
    change τ (φ (x*y)) = τ (φ (y*x))
    simpa only [map_mul] using hτ (φ x) (φ y)
  · change τ (φ 1) = 1
    simpa using h1

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixProjectionDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

lemma projection_eigenvalue (p : Matrix I I ℂ) (hp : IsStarProjection p) (i : I) :
    (projection_hermitian p hp).eigenvalues i=0 ∨ (projection_hermitian p hp).eigenvalues i=1 := by
  let U := (projection_hermitian p hp).eigenvectorUnitary
  have hid := congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U)) hp.isIdempotentElem.eq
  rw [map_mul] at hid
  have hd := (projection_hermitian p hp).conjStarAlgAut_star_eigenvectorUnitary
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U) p = _ at hd
  rw [hd] at hid
  have h := congrArg (fun M : Matrix I I ℂ => (M i i).re) hid
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq,Function.comp_apply,
    ] at h
  change ((projection_hermitian p hp).eigenvalues i : ℂ).re *
    ((projection_hermitian p hp).eigenvalues i : ℂ).re -
    ((projection_hermitian p hp).eigenvalues i : ℂ).im *
    ((projection_hermitian p hp).eigenvalues i : ℂ).im =
    ((projection_hermitian p hp).eigenvalues i : ℂ).re at h
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
  have hz : (projection_hermitian p hp).eigenvalues i *
      ((projection_hermitian p hp).eigenvalues i-1)=0 := by nlinarith
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp

lemma projection_diagonal_form (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    p=Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (projection_hermitian p hp).eigenvectorUnitary
      (Matrix.diagonal (fun i => if i∈projectionIndices p hp then (1:ℂ) else 0)) := by
  apply (projection_hermitian p hp).spectral_theorem.trans
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Function.comp_apply,projectionIndices,Set.mem_ofPred_eq]
    rcases projection_eigenvalue p hp i with he|he <;> simp [he]
  · simp [Matrix.diagonal_apply_ne _ h]

lemma trace_conjugation (U : unitary (Matrix I I ℂ)) (a : Matrix I I ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U a).trace=a.trace := by
  rw [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_comm,←mul_assoc,Unitary.coe_star_mul_self,one_mul]

lemma projection_trace (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    p.trace=(Fintype.card (projectionIndices p hp):ℂ) := by
  classical
  calc
    _ = _ := congrArg Matrix.trace (projection_diagonal_form p hp)
    _ = _ := by
      rw [trace_conjugation,Matrix.trace_diagonal]
      simp [Fintype.card_subtype]

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlphabetGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (p : Matrix I I ℂ) (hp : IsStarProjection p)
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  (e : G ≃ projectionIndices p hp)

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

include hτ h1 hατ in
omit [StarOrderedRing A] in
lemma projection_rank_oai : (Fintype.card (projectionIndices p hp):ℝ)=α*Fintype.card I := by
  have hd : (Fintype.card I:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (projectionIndices p hp):ℂ)=(α:ℂ)*Fintype.card I := by
    rw [←hατ,TracialGNS.stage_trace τ hτ h1 φ,projection_trace p hp]
    field_simp
  have hr := congrArg Complex.re hc
  simpa using hr

end Kadison.MatrixCorners

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixCorners.projection_rank_oai.{u_1, u_2} := @OAI.Kadison.MatrixCorners.projection_rank_oai.{u_1, u_2}
