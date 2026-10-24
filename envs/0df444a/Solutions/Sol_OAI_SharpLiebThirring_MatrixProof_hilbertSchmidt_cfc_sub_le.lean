-- Prove2me | solution 1 for OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:59:30.697784+00:00
-- url     : https://prove2.me/submissions/b260dfe9-e5c9-43cb-bc2c-7ee4e432d2f5

import Mathlib
import Definitions.Def_OAIQWSLT000

section
-- module Solutions.OAIQW_LiebThirring.MatrixOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/


open Matrix Unitary
namespace MatrixProof
variable {n : Type u1} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma trace_star_mul_sum (A B : Matrix n n ℂ) :
    (trace (star A * B)).re = ∑ i, ∑ j, (star (A i j) * B i j).re := by
  simp only [trace, diag, mul_apply, star_eq_conjTranspose, conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  exact Finset.sum_comm

lemma trace_star_mul_change (U V : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    trace (star (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) *
      (star (U : Matrix n n ℂ) * B * (V : Matrix n n ℂ))) = trace (star A * B) := by
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.property
  have hv : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem V.property
  simp only [star_mul, star_star]
  calc
    _ = trace (star (V : Matrix n n ℂ) * (star A *
          ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ))) * B * (V : Matrix n n ℂ)) := by
      congr 1
      noncomm_ring
    _ = trace (star (V : Matrix n n ℂ) * (star A * B) * (V : Matrix n n ℂ)) := by simp [hu, mul_assoc]
    _ = trace ((V : Matrix n n ℂ) * star (V : Matrix n n ℂ) * (star A * B)) :=
      trace_mul_cycle _ _ _
    _ = trace (star A * B) := by rw [hv, one_mul]

lemma mixed_diagonal_sub (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ) =
      diagonal (fun i ↦ (a i : ℂ)) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
        (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) := by
  simp only [conjStarAlgAut_apply]
  calc
    _ = (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * diagonal (fun i ↦ (a i : ℂ)) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) -
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) * diagonal (fun i ↦ (b i : ℂ)) *
          (star (V : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by noncomm_ring
    _ = _ := by simp only [Unitary.coe_star_mul_self, one_mul, mul_one]

lemma mixed_diagonal_sub_apply (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (i j : n) :
    (star (U : Matrix n n ℂ) *
      (conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) -
        conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ)))) * (V : Matrix n n ℂ)) i j =
      ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
  rw [mixed_diagonal_sub]
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, Complex.ofReal_sub]
  ring

omit [DecidableEq n] in
lemma hsSquared_eq_trace (A : Matrix n n ℂ) :
    hsSquared A = (trace (star A * A)).re := by
  rw [trace_star_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma hsSquared_change (U V : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    hsSquared (star (U : Matrix n n ℂ) * A * (V : Matrix n n ℂ)) = hsSquared A := by
  rw [hsSquared_eq_trace, trace_star_mul_change, hsSquared_eq_trace]

/-- The finite-dimensional Hilbert--Schmidt calculus estimate,
proved in mixed eigenbases. -/
lemma hsSquared_cfc_sub_proof {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    hsSquared (hA.cfc f - hB.cfc f) ≤ L ^ 2 * hsSquared (A - B) := by
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  have ha : A = conjStarAlgAut ℂ (Matrix n n ℂ) U (diagonal (fun i ↦ (a i : ℂ))) :=
    hA.spectral_theorem
  have hb : B = conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal (fun i ↦ (b i : ℂ))) :=
    hB.spectral_theorem
  have hfm (i j : n) :
      (star (U : Matrix n n ℂ) * (hA.cfc f - hB.cfc f) * (V : Matrix n n ℂ)) i j =
        ((f (a i) - f (b j) : ℝ) : ℂ) *
          (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j :=
    mixed_diagonal_sub_apply U V (f ∘ a) (f ∘ b) i j
  have hm (i j : n) :
      (star (U : Matrix n n ℂ) * (A - B) * (V : Matrix n n ℂ)) i j =
        ((a i - b j : ℝ) : ℂ) * (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j := by
    rw [ha, hb]
    exact mixed_diagonal_sub_apply U V a b i j
  rw [← hsSquared_change U V (hA.cfc f - hB.cfc f),
    ← hsSquared_change U V (A - B)]
  simp only [hsSquared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [hfm, hm, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  have hh := sq_le_sq₀ (abs_nonneg (f (a i) - f (b j)))
    (mul_nonneg hL (abs_nonneg (a i - b j))) |>.2 (hf i j)
  rw [sq_abs, mul_pow, sq_abs] at hh
  nlinarith [mul_le_mul_of_nonneg_right hh
    (Complex.normSq_nonneg ((star (U : Matrix n n ℂ) * (V : Matrix n n ℂ)) i j))]

theorem hilbertSchmidt_cfc_sub_le_oai {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    ∑ i, ∑ j, Complex.normSq ((hA.cfc f - hB.cfc f) i j) ≤
      L ^ 2 * ∑ i, ∑ j, Complex.normSq ((A - B) i j) :=
  hsSquared_cfc_sub_proof hA hB f L hL hf

open MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal

end MatrixProof

open MeasureTheory Set Filter
open scoped Topology

open scoped MatrixOrder ComplexOrder


end SharpLiebThirring

end

end OAI
end

theorem solution.{u1} : type_of% @OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le_oai.{u1} := @OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le_oai.{u1}
