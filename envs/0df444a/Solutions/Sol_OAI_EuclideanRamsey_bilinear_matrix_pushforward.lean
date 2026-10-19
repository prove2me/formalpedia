-- Prove2me | solution 1 for OAI.EuclideanRamsey.bilinear_matrix_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:04:08.84042+00:00
-- url     : https://prove2.me/submissions/b00b0a38-47cd-42ac-86f9-b5c608566d89

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean:L162-L190
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.bilinear_matrix_pushforward. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

end Trace

section MatrixContraction

lemma pi_basis_expansion {n : ℕ} (v : Fin n → ℝ) :
    v = ∑ j, v j • Pi.single j (1:ℝ) := by
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm

lemma bilinear_matrix_pushforward {k n : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  have hex (v w : Fin k → ℝ) : B v w = ∑ j, ∑ l,
      (v j*w l)*B (Pi.single j 1) (Pi.single l 1) := by
    conv_lhs => rw [pi_basis_expansion v, pi_basis_expansion w]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [hex]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro b; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open scoped BigOperators
open Matrix MeasureTheory


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.bilinear_matrix_pushforward := @_root_.OAI.EuclideanRamsey.bilinear_matrix_pushforward
