-- Prove2me | solution 1 for OAI.Problem346.symmetric_diagonal_mixed_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:32:24.058493+00:00
-- url     : https://prove2.me/submissions/6e3bd2aa-f69f-47c5-9459-4f8c54d87a65

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalCoefficient.lean:L88-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.symmetric_diagonal_mixed_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Theorems.Thm_OAI_Problem346_symmetric_update_eq

-- ---- from OAI.RepresentationTheory.FoulkesHowe.DiagonalCoefficient ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

lemma diagonalPolynomial_eval {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ) (x y : E) (c : ℂ) :
    (diagonalPolynomial T x y).eval c = T (fun _ => x + c • y) := by
  classical
  unfold diagonalPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (fun _ : Fin a => x + c • y) =
    (fun _ => c • y) + (fun _ => x) by ext; simp [add_comm]]
  rw [T.map_add_univ]
  apply Finset.sum_congr rfl
  intro s hs
  have h := T.map_piecewise_smul (fun _ => c)
    (s.piecewise (fun _ => y) (fun _ => x)) s
  have heq : s.piecewise (fun i => c • s.piecewise (fun _ => y) (fun _ => x) i)
      (s.piecewise (fun _ => y) (fun _ => x)) =
      s.piecewise (fun _ => c • y) (fun _ => x) := by
    ext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [heq] at h
  simpa [smul_eq_mul, mul_comm] using h.symm

lemma diagonalPolynomial_coeff_one {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ) (x y : E) :
    (diagonalPolynomial T x y).coeff 1 =
      ∑ i : Fin a, T (Function.update (fun _ => x) i y) := by
  classical
  unfold diagonalPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm (a := 1)]
  rw [← Finset.sum_filter]
  rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter]
  simp [Finset.powersetCard_one, Finset.piecewise_singleton]

/-- If a multilinear form vanishes on an affine diagonal line, its linear diagonal
coefficient vanishes. This statement does not require symmetry. -/
theorem diagonal_linear_coefficient_zero {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ) (x y : E)
    (h : ∀ c : ℂ, T (fun _ => x + c • y) = 0) :
    (∑ i : Fin a, T (Function.update (fun _ => x) i y)) = 0 := by
  have hp : diagonalPolynomial T x y = 0 :=
    Polynomial.zero_of_eval_zero _ (fun c => by rw [diagonalPolynomial_eval, h])
  rw [← diagonalPolynomial_coeff_one, hp]
  simp

/-- Coefficient extraction for a symmetric multilinear form along an affine diagonal.
This is the coefficient-of-c argument in the split binary form step. -/
theorem symmetric_diagonal_mixed_zero {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin a)) (v : Fin a → E),
      T (fun k => v (σ k)) = T v)
    (x y : E) (i : Fin a)
    (h : ∀ c : ℂ, T (fun _ => x + c • y) = 0) :
    T (Function.update (fun _ => x) i y) = 0 := by
  have hz := diagonal_linear_coefficient_zero T x y h
  have heq : (∑ j : Fin a, T (Function.update (fun _ => x) j y)) =
      (a : ℂ) * T (Function.update (fun _ => x) i y) := by
    calc
      _ = ∑ _j : Fin a, T (Function.update (fun _ => x) i y) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact symmetric_update_eq T hsym x y i j
      _ = _ := by simp [nsmul_eq_mul]
  rw [heq] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem346.symmetric_diagonal_mixed_zero.{u} := @_root_.OAI.Problem346.symmetric_diagonal_mixed_zero.{u}
