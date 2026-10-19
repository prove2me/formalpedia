-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.successProbability_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:29:32.52766+00:00
-- url     : https://prove2.me/submissions/b5ec8d6c-2fb2-4a18-a617-de0dd57935e6

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Basic.lean:L96-L111
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.successProbability_le_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic

-- ---- from OAI.Probability.EntangledGames.Basic ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]

lemma born_nonneg (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b := by
  rw [born_eq_quadratic]
  exact (Complex.nonneg_iff.mp
    (((S.alice_pos x a).kronecker (S.bob_pos y b)).dotProduct_mulVec_nonneg S.state)).1

lemma total_effect (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.alice x a ⊗ₖ S.bob y b = 1 := by
  classical
  calc
    _ = (∑ a, S.alice x a) ⊗ₖ (∑ b, S.bob y b) := by
      ext i j
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = 1 := by rw [S.alice_total, S.bob_total, Matrix.one_kronecker_one]

lemma born_sum (S : Strategy X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, S.born x y a b = 1 := by
  simp_rw [born_eq_quadratic]
  simp_rw [← Complex.re_sum, ← dotProduct_sum, ← Matrix.sum_mulVec]
  rw [total_effect, Matrix.one_mulVec]
  rw [dotProduct, Complex.re_sum]
  convert S.state_unit using 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq, Complex.mul_re]

end Strategy

namespace Strategy

end Strategy

lemma successProbability_le_one {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ 1 := by
  calc
    successProbability G S ≤ ∑ z, G.questionProb z *
        ∑ w : Fin (a + 1) × Fin (b + 1), S.born z.1 z.2 w.1 w.2 := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (G.questionProb_nonneg z)
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · exact le_rfl
      · exact S.born_nonneg _ _ _ _
    _ = 1 := by
      simp_rw [Fintype.sum_prod_type, S.born_sum, mul_one]
      simpa only [Fintype.sum_prod_type] using G.questionProb_sum

end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition
open scoped BigOperators ComplexOrder
open scoped Kronecker
open Matrix


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.successProbability_le_one := @_root_.OAI.ThresholdParallelRepetition.successProbability_le_one
