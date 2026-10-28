-- Prove2me | solution 1 for OAI.Kadison.MatrixColumnCorner.trace_minimal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:07.295462+00:00
-- url     : https://prove2.me/submissions/2c66d8b3-3446-4a7d-b60b-bdc112458cfe

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.MatrixDiffuse

open Matrix

lemma diagonal_trace {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (φ : Matrix I I ℂ →ₗ[ℂ] ℂ) (htr : ∀ x y, φ (x*y)=φ (y*x)) (hunit : φ 1=1)
    (i : I) : φ (single i i 1)=(Fintype.card I : ℂ)⁻¹ := by
  have hdiag : ∀ j : I, φ (single i i 1)=φ (single j j 1) := by
    intro j
    simpa using htr (single i j 1) (single j i 1)
  have hcard : (Fintype.card I : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ)*φ (single i i 1)=1 := by
    calc
      _=∑ j : I, φ (single j j 1) := by
        simp only [←hdiag,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _=φ 1 := by rw [←map_sum,Matrix.sum_single_one]
      _=1 := hunit
  apply mul_left_cancel₀ hcard
  rw [h,mul_inv_cancel₀ hcard]

end Kadison.MatrixDiffuse

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixColumnCorner

variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CStarAlgebra D]

lemma trace_minimal_oai [PartialOrder D] [StarOrderedRing D]
    (τ : D →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) (i : I) :
    τ (φ (Matrix.single i i 1))=(Fintype.card I : ℂ)⁻¹ :=
  MatrixDiffuse.diagonal_trace (τ.toLinearMap.comp φ.toLinearMap)
    (fun x y => by change τ (φ (x*y))=τ (φ (y*x)); simpa only [map_mul] using hτ (φ x) (φ y))
    (by change τ (φ 1)=1; simpa only [map_one] using h1) i

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixColumnCorner.trace_minimal_oai.{u_1, u_2} := @OAI.Kadison.MatrixColumnCorner.trace_minimal_oai.{u_1, u_2}
