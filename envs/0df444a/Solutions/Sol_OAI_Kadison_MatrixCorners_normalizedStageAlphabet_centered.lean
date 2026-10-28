-- Prove2me | solution 1 for OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:17:40.064479+00:00
-- url     : https://prove2.me/submissions/37c88d28-07e6-4be6-9f02-201bf2b76b7b

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

lemma projectionAlphabet_trace (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) :
    (projectionAlphabet p hp e g).trace=if g=0 then (Fintype.card G:ℂ) else 0 := by
  rw [projectionAlphabet,projectionEmbedding_trace]
  change (Matrix.reindex e e (shiftMatrix g)).trace=_
  rw [trace_reindex,shift_trace]

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

include hτ h1 in
omit [StarOrderedRing A] in
lemma stageAlphabet_centered (g : G) (hg : g≠0) : τ (stageAlphabet φ p hp e g)=0 := by
  rw [stageAlphabet,TracialGNS.stage_trace τ hτ h1 φ,projectionAlphabet_trace,ite_eq_right hg,mul_zero]

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

include hτ h1 in
omit [StarOrderedRing A] in
lemma normalizedStageAlphabet_centered_oai (g : G) (hg : g≠0) :
    τ (normalizedStageAlphabet φ p hp e α g)=0 := by
  rw [normalizedStageAlphabet,map_smul,stageAlphabet_centered τ hτ h1 φ p hp e g hg,smul_zero]

end Kadison.MatrixCorners

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered_oai.{u_1, u_2, u_3} := @OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered_oai.{u_1, u_2, u_3}
