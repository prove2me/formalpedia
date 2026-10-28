-- Prove2me | solution 1 for OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:18:24.052562+00:00
-- url     : https://prove2.me/submissions/f92a4224-1934-4392-9373-5bb3457733e0

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C013

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTrace
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCutEmbedding
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

attribute [local instance] Classical.propDecidable

omit [DecidableEq I] [DecidableEq J] in
lemma trace_reindex (e : J ≃ I) (a : Matrix J J ℂ) :
    (Matrix.reindex e e a).trace=a.trace := by
  exact e.symm.sum_comp (fun j => a j j)

omit [DecidableEq J] [DecidableEq K] in
lemma trace_cutBlock (a : Matrix J J ℂ) :
    (Matrix.fromBlocks a (0:Matrix J K ℂ) 0 0).trace=a.trace := by
  simp [Matrix.trace,Fintype.sum_sum_type]

lemma cutEmbedding_trace (s : Set I) (a : Matrix s s ℂ) :
    (cutEmbedding s a).trace=a.trace := by
  change (Matrix.reindex (Equiv.Set.sumCompl s) (Equiv.Set.sumCompl s)
    (Matrix.fromBlocks a (0:Matrix s (sᶜ:Set I) ℂ) 0 0)).trace=a.trace
  rw [trace_reindex,trace_cutBlock]

lemma cutEmbedding_one (s : Set I) :
    cutEmbedding s 1=Matrix.diagonal (fun i => if i∈s then (1:ℂ) else 0) := by
  ext i j
  by_cases hi : i∈s <;> by_cases hj : j∈s
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.one_apply,Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [show i≠j from fun h=>hj (h ▸ hi)]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [Matrix.diagonal_apply,hi]

lemma projectionEmbedding_one (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    projectionEmbedding p hp 1=p := by
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) _ (cutEmbedding _ 1)=p
  rw [cutEmbedding_one]
  exact (projection_diagonal_form p hp).symm

lemma projectionEmbedding_trace (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (a : Matrix (projectionIndices p hp) (projectionIndices p hp) ℂ) :
    (projectionEmbedding p hp a).trace=a.trace := by
  change (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) _ (cutEmbedding _ a)).trace=a.trace
  rw [trace_conjugation,cutEmbedding_trace]

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixUnitaryAlphabet
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

lemma shift_trace (g : G) : (shiftMatrix g).trace=if g=0 then (Fintype.card G:ℂ) else 0 := by
  rw [shiftMatrix,Matrix.trace_permutation]
  by_cases hg : g=0
  · subst g
    simp
  · have he : Function.fixedPoints (Equiv.addLeft g)=∅ := by
      ext x
      simp [Function.fixedPoints,Function.IsFixedPt,hg]
    simp only [he,Set.ncard_empty,Nat.cast_zero,ite_eq_right hg]

lemma shift_star_mul (g h : G) : star (shiftMatrix g)*shiftMatrix h=shiftMatrix (h-g) := by
  change (shiftMatrix g).conjTranspose*shiftMatrix h=_
  simp only [shiftMatrix,Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul]
  congr 1
  ext x
  simp [sub_eq_add_neg]

omit [Fintype G] in
lemma shift_zero : shiftMatrix (0:G)=1 := by
  change (Equiv.addLeft (0:G)).permMatrix ℂ=1
  have he : Equiv.addLeft (0:G)=Equiv.refl G := by ext x; simp
  rw [he,Matrix.permMatrix_refl]

lemma shift_gram (g h : G) : (star (shiftMatrix g)*shiftMatrix h).trace=
    if g=h then (Fintype.card G:ℂ) else 0 := by
  rw [shift_star_mul,shift_trace]
  simp [sub_eq_zero,eq_comm]

lemma projectionAlphabet_star_mul (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) :
    star (projectionAlphabet p hp e g)*projectionAlphabet p hp e g=p := by
  unfold projectionAlphabet
  rw [←map_star,←map_mul,←map_star,←map_mul,shift_star_mul,sub_self,shift_zero,
    map_one,projectionEmbedding_one]

lemma projectionAlphabet_gram (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g h : G) :
    (star (projectionAlphabet p hp e g)*projectionAlphabet p hp e h).trace=
      if g=h then (Fintype.card G:ℂ) else 0 := by
  unfold projectionAlphabet
  rw [←map_star,←map_mul,projectionEmbedding_trace,←map_star,←map_mul]
  change (Matrix.reindex e e (star (shiftMatrix g)*shiftMatrix h)).trace=_
  rw [trace_reindex,shift_gram]

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlphabetGNS
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_star_mul (g : G) : star (stageAlphabet φ p hp e g)*stageAlphabet φ p hp e g=φ p := by
  rw [stageAlphabet,←map_star,←map_mul,projectionAlphabet_star_mul]

include hτ h1 in
omit [StarOrderedRing A] in
lemma stageAlphabet_gram (g h : G) : τ (star (stageAlphabet φ p hp e g)*stageAlphabet φ p hp e h)=
    if g=h then τ (φ p) else 0 := by
  by_cases heq : g=h
  · subst h
    rw [stageAlphabet_star_mul,ite_eq_left rfl]
  · rw [ite_eq_right heq,stageAlphabet,stageAlphabet,←map_star,←map_mul,
      TracialGNS.stage_trace τ hτ h1 φ,projectionAlphabet_gram,ite_eq_right heq,mul_zero]

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

include hα in
lemma normalization_sq : ((((Real.sqrt α)⁻¹:ℝ):ℂ))^2=(α:ℂ)⁻¹ := by
  rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt hα.le,Complex.ofReal_inv]

include hτ h1 hα hατ in
lemma normalizedStageAlphabet_orthonormal_oai :
    Orthonormal ℂ (fun g : G => TracialGNS.algebraVector τ (normalizedStageAlphabet φ p hp e α g)) := by
  apply orthonormal_iff_ite.mpr
  intro g h
  simp only [normalizedStageAlphabet,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,TracialGNS.inner_algebraVector,stageAlphabet_gram τ hτ h1]
  by_cases heq : g=h
  · rw [ite_eq_left heq,ite_eq_left heq,hατ]
    rw [←mul_assoc,←sq,normalization_sq α hα,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hα.ne')]
  · rw [ite_eq_right heq,ite_eq_right heq,mul_zero,mul_zero]

end Kadison.MatrixCorners

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal_oai.{u_1, u_2, u_3} := @OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal_oai.{u_1, u_2, u_3}
