-- Prove2me | solution 1 for MarkovEntanglementExact.local_values_decompose_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:45:18.490664+00:00
-- url     : https://prove2.me/submissions/4ae605fc-6e26-4228-a533-80fe14f188d2

import Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

private lemma transition_bound {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (x : ι → ℝ) (i : ι) :
    |∑ j, P i j * x j| ≤ ‖x‖ := by
  calc
    |∑ j, P i j * x j| ≤ ∑ j, |P i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, P i j * |x j| := by simp_rw [abs_mul, abs_of_nonneg (hP.1 _ _)]
    _ ≤ ∑ j, P i j * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm x j) (hP.1 i j)
    _ = ‖x‖ := by rw [← Finset.sum_mul, hP.2 i, one_mul]

private lemma bellman_unique {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r Q Q' : ι → ℝ) (hQ : IsBellmanQ P r γ Q) (hQ' : IsBellmanQ P r γ Q') : Q = Q' := by
  have heq (i : ι) : (Q - Q') i = γ * ∑ j, P i j * (Q - Q') j := by
    rw [Pi.sub_apply, hQ i, hQ' i]
    simp_rw [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hb : ‖Q - Q'‖ ≤ γ * ‖Q - Q'‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hγ0 (norm_nonneg _))).mpr
    intro i
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left (transition_bound P hP (Q-Q') i) hγ0
  have hz : ‖Q - Q'‖ = 0 := by nlinarith [norm_nonneg (Q-Q')]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (hsep : IsSeparable P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ)
    (PA : Matrix SA SA ℝ) (PB : Matrix SB SB ℝ)
    (hA : IsLocalTransitionA P μ PA) (hB : IsLocalTransitionB P μ PB) :
    LocalValuesDecompose P PA PB γ := by
  classical
  rcases hsep with ⟨K, x, PAj, PBj, hAj, hBj, hx, hexp⟩
  have hmA : ∀ a a' b, ∑ b', P (a,b) (a',b') = (∑ k, x k • PAj k) a a' := by
    intro a a' b
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ b', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PAj k a a'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [← mul_assoc, ← Finset.mul_sum, (hBj k).2 b, mul_one]
  have hmB : ∀ a b b', ∑ a', P (a,b) (a',b') = (∑ k, x k • PBj k) b b' := by
    intro a b b'
    rw [hexp]
    simp only [Matrix.sum_apply]
    change (∑ a', ∑ k, x k * (PAj k a a' * PBj k b b')) = ∑ k, x k * PBj k b b'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum, ← Finset.sum_mul, (hAj k).2 a, one_mul]
  have hPA : PA = ∑ k, x k • PAj k := by
    ext a a'
    apply mul_left_cancel₀ (ne_of_gt (hμ.2.2.1 a))
    rw [hA a a']
    simp_rw [hmA]
    rw [← Finset.sum_mul]
    rfl
  have hPB : PB = ∑ k, x k • PBj k := by
    ext b b'
    apply mul_left_cancel₀ (ne_of_gt (hμ.2.2.2 b))
    rw [hB b b']
    simp_rw [hmB]
    rw [← Finset.sum_mul]
    rfl
  intro rA rB Q QA QB hQ hQA hQB
  have hlocal : IsBellmanQ P (fun p => rA p.1 + rB p.2) γ
      (fun p => QA p.1 + QB p.2) := by
    rintro ⟨a,b⟩
    have ha := hQA a
    have hb := hQB b
    have hsumA : (∑ j, P (a,b) j * QA j.1) = ∑ a', PA a a' * QA a' := by
      simp only [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_mul, hmA, hPA]
    have hsumB : (∑ j, P (a,b) j * QB j.2) = ∑ b', PB b b' * QB b' := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hmB, hPB]
    simp_rw [mul_add, Finset.sum_add_distrib, hsumA, hsumB]
    linarith
  have heq := bellman_unique P hP γ hγ0 hγ1 _ Q _ hQ hlocal
  intro p
  exact congrFun heq p

#print axioms solution
