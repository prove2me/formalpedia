-- Prove2me | solution 1 for GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:08.620886+00:00
-- url     : https://prove2.me/submissions/de96cf42-10fc-4d44-b3e4-599b13c6c846

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentity
import Theorems.Thm_GlobalTheory_shift_coeff_of_eval_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  intro N _ _ Ω X d c p hX h
  let a : N → ℕ → N := fun w i => if i < d then c i w else 0
  have ha : ∀ w i, d ≤ i → a w i = 0 := fun w i hi => if_neg (by omega)
  have hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N),
      X u w = ∑ i ∈ Finset.range M, u ^ i • a w i := by
    intro M hM u w
    rw [hX u, LinearMap.sum_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]
    · intro i _ hi
      rw [ha w i (by simpa using hi), smul_zero]
  have hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧
      ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w := by
    intro w
    refine shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_
    rw [← hXa d le_rfl u w]
    exact h u w
  refine ⟨?_, ?_⟩
  · ext w
    have tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w
        = ((-Ω) ^ n) (Ω (a w n)) := by
      intro n
      induction n with
      | zero => simp [(hco w).1]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add, ← add_assoc]
        have : ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n)) := by
          rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]
        rw [this, add_neg_cancel, zero_add]
    rw [Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]
  · intro α w hw q hq u
    have step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w := by
      intro k hk
      have h1 := (hco w).2 k
      rw [hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm] at h1
      exact add_right_cancel h1
    have all : ∀ k, a w k = q.coeff k • w := by
      intro k
      have hk : k ≤ k + d + q.natDegree + 1 := by omega
      refine Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w)
        (fun j _ hj => step j hj) ?_ hk
      rw [ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    rw [hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [all, smul_smul, mul_comm]
end GlobalTheory
