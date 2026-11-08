-- Prove2me | solution 1 for MarkovEntanglementExact.bellman_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:45:26.112971+00:00
-- url     : https://prove2.me/submissions/d78ef7e0-c2cb-472c-b08d-f1331f8e2333

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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : ι → ℝ) :
    IsUnit (1 - γ • P) ∧
      IsBellmanQ P r γ ((1 - γ • P)⁻¹.mulVec r) ∧
      (∀ Q : ι → ℝ, IsBellmanQ P r γ Q → Q = (1 - γ • P)⁻¹.mulVec r) ∧
      HasSum (fun t : ℕ => γ ^ t • (P ^ t).mulVec r) ((1 - γ • P)⁻¹.mulVec r) := by
  classical
  have hunit := bellman_unit P hP γ hγ0 hγ1
  have hsol := inverse_bellman P γ hunit r
  refine ⟨hunit, hsol, (fun Q hQ => bellman_unique P hP γ hγ0 hγ1 r Q _ hQ hsol), ?_⟩
  let v : ℕ → ι → ℝ := fun t => γ ^ t • (P ^ t).mulVec r
  have hb : ∀ t : ℕ, ‖(P ^ t).mulVec r‖ ≤ ‖r‖ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      apply le_trans _ ih
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact transition_bound P hP _ i
  have hs : Summable v := by
    apply ((summable_geometric_of_lt_one hγ0 hγ1).mul_right ‖r‖).of_norm_bounded
    intro t
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ0 t)]
    exact mul_le_mul_of_nonneg_left (hb t) (pow_nonneg hγ0 t)
  have htail : HasSum (fun t => v (t + 1)) ((∑' t, v t) - r) := by
    simpa [v] using (hasSum_nat_add_iff' 1).mpr hs.hasSum
  have hstep (t : ℕ) : v (t + 1) = γ • P.mulVec (v t) := by
    simp only [v, pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul]
  have hmap : HasSum (fun t => γ • P.mulVec (v t)) (γ • P.mulVec (∑' t, v t)) := by
    apply Pi.hasSum.mpr
    intro i
    have hh := hasSum_sum (s := Finset.univ) (fun j _ => (Pi.hasSum.mp hs.hasSum j).mul_left (γ * P i j))
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc] using hh
  have he : (∑' t, v t) - r = γ • P.mulVec (∑' t, v t) := by
    simp_rw [← hstep] at hmap
    exact htail.unique hmap
  have hbell : IsBellmanQ P r γ (∑' t, v t) := by
    intro i
    have hi := congrFun he i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    change (∑' t, v t) i = r i + γ * (P.mulVec (∑' t, v t)) i
    linarith
  have hvalue := bellman_unique P hP γ hγ0 hγ1 r _ _ hbell hsol
  exact hvalue ▸ hs.hasSum

#print axioms solution

