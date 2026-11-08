-- Prove2me | solution 1 for MarkovEntanglementExact.separable_implies_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:45:22.7531+00:00
-- url     : https://prove2.me/submissions/4967afe6-3de3-4491-81e5-611453e7ecd3

import Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
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

private lemma bellman_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit (1 - γ • P) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro Q Q' he
  let r := (1 - γ • P).mulVec Q
  have hQ : IsBellmanQ P r γ Q := by
    intro i
    simp [r, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec, dotProduct]
  have hQ' : IsBellmanQ P r γ Q' := by
    intro i
    have he' := congrFun he i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at he'
    change Q' i = ((1 - γ • P).mulVec Q) i + γ * _
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    change Q' i = Q i - γ * (P.mulVec Q) i + γ * (P.mulVec Q') i
    linarith
  exact bellman_unique P hP γ hγ0 hγ1 r Q Q' hQ hQ'

private lemma inverse_bellman {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ)
    (γ : ℝ) (hunit : IsUnit (1 - γ • P)) (r : ι → ℝ) :
    IsBellmanQ P r γ ((1 - γ • P)⁻¹.mulVec r) := by
  have he : (1 - γ • P).mulVec ((1 - γ • P)⁻¹.mulVec r) = r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit),
      Matrix.one_mulVec]
  intro i
  have hi := congrFun he i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul] at hi
  change ((1 - γ • P)⁻¹.mulVec r) i = r i + γ * (P.mulVec ((1 - γ • P)⁻¹.mulVec r)) i
  linarith

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (hsep : IsSeparable P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    HasExactValueDecomposition P γ := by
  classical
  by_cases hab : Nonempty (SA × SB)
  · obtain ⟨a0,b0⟩ := hab
    rcases hsep with ⟨K, x, PAj, PBj, hAj, hBj, hx, hexp⟩
    let PA : Matrix SA SA ℝ := fun a a' => ∑ b', P (a,b0) (a',b')
    let PB : Matrix SB SB ℝ := fun b b' => ∑ a', P (a0,b) (a',b')
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
    have hPAid : ∀ a a' b, ∑ b', P (a,b) (a',b') = PA a a' := by
      intro a a' b
      dsimp [PA]
      rw [hmA, hmA]
    have hPBid : ∀ a b b', ∑ a', P (a,b) (a',b') = PB b b' := by
      intro a b b'
      dsimp [PB]
      rw [hmB, hmB]
    have hPA : IsTransitionMatrix PA := by
      constructor
      · intro a a'
        exact Finset.sum_nonneg fun b' _ => hP.1 _ _
      · intro a
        simpa only [PA, Fintype.sum_prod_type] using hP.2 (a,b0)
    have hPB : IsTransitionMatrix PB := by
      constructor
      · intro b b'
        exact Finset.sum_nonneg fun a' _ => hP.1 _ _
      · intro b
        change (∑ b', ∑ a', P (a0,b) (a',b')) = 1
        rw [Finset.sum_comm]
        simpa only [Fintype.sum_prod_type] using hP.2 (a0,b)
    let QA := fun rA : SA → ℝ => (1 - γ • PA)⁻¹.mulVec rA
    let QB := fun rB : SB → ℝ => (1 - γ • PB)⁻¹.mulVec rB
    have hQA (rA) : IsBellmanQ PA rA γ (QA rA) :=
      inverse_bellman PA γ (bellman_unit PA hPA γ hγ0 hγ1) rA
    have hQB (rB) : IsBellmanQ PB rB γ (QB rB) :=
      inverse_bellman PB γ (bellman_unit PB hPB γ hγ0 hγ1) rB
    refine ⟨QA, QB, ?_⟩
    intro rA rB Q hQ
    have hlocal : IsBellmanQ P (fun p => rA p.1 + rB p.2) γ
        (fun p => QA rA p.1 + QB rB p.2) := by
      rintro ⟨a,b⟩
      have ha := hQA rA a
      have hb := hQB rB b
      have hsumA : (∑ j, P (a,b) j * QA rA j.1) = ∑ a', PA a a' * QA rA a' := by
        simp only [Fintype.sum_prod_type]
        simp_rw [← Finset.sum_mul, hPAid]
      have hsumB : (∑ j, P (a,b) j * QB rB j.2) = ∑ b', PB b b' * QB rB b' := by
        simp only [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, hPBid]
      simp_rw [mul_add, Finset.sum_add_distrib, hsumA, hsumB]
      linarith
    have heq := bellman_unique P hP γ hγ0 hγ1 _ Q _ hQ hlocal
    intro p
    exact congrFun heq p
  · letI : IsEmpty (SA × SB) := not_nonempty_iff.mp hab
    refine ⟨(fun _ _ => 0), (fun _ _ => 0), ?_⟩
    intro rA rB Q hQ p
    exact isEmptyElim p

#print axioms solution

