-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SemilinearResidue.exists_fixed_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:40.596699+00:00
-- url     : https://prove2.me/submissions/98849d42-2506-49b9-b7e0-89351fe361d6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_two_le_pow
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_recPoly_coeff_lead
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_exists_rel
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_solve_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}
namespace GroundTheory.PAdicHodge.SemilinearResidue
theorem _root_.solution [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V)
    (hz : ∀ N, (⇑φ)^[N] z ≠ 0) : ∃ x, x ≠ 0 ∧ φ x = x := by
  obtain ⟨m, ⟨c, hrel⟩, hli⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact absurd (by simpa using hrel) (hz 0)
  | succ n =>
    have h2 := two_le_pow (p := p) he
    obtain ⟨j, hj, hcj⟩ : ∃ j ∈ range (n + 1), c j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hz (n + 1)
      rw [hrel]
      exact Finset.sum_eq_zero (fun i hi => by rw [hcon i hi, zero_smul])
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by simp at hj; omega⟩
    set N := (p ^ e) ^ (t + 1) with hN
    have hN2 : 2 ≤ N := le_trans h2 (Nat.le_self_pow (by omega) _)
    set P : k[X] := recPoly (p ^ e) c 0 (j + t) - X with hP
    have hP0 : P.coeff 0 = 0 := by simp [hP, recPoly_coeff_zero]
    have hP1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hPN : P.coeff N ≠ 0 := by
      have hN1 : N ≠ 1 := by omega
      simp only [hP, coeff_sub, coeff_X, hN, recPoly_coeff_lead he c 0 j t]
      rw [if_neg (by omega), sub_zero]
      exact pow_ne_zero _ hcj
    obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hP0
    have hQ0 : Q.coeff 0 = -1 := by
      rw [← hP1, hQ, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul]
    have hQN : Q.coeff (N - 1) ≠ 0 := by
      rw [← coeff_X_mul, show N - 1 + 1 = N by omega, ← hQ]
      exact hPN
    have hdeg : Q.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h, coeff_C, if_neg (by omega)] at hQN
      exact hQN rfl
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hdeg
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [IsRoot, ← coeff_zero_eq_eval_zero, hQ0] at hy
      exact one_ne_zero (neg_eq_zero.mp hy)
    have hy' : (recPoly (p ^ e) c 0 (j + t)).eval y = y := by
      have : P.eval y = 0 := by rw [hQ, eval_mul, hy.eq_zero, mul_zero]
      simp only [hP, eval_sub, eval_X] at this
      exact sub_eq_zero.mp this
    refine ⟨_, ?_, by rw [solve_of_root hφ z (j + t) c hrel 0 y hy', zero_smul, add_zero]⟩
    intro hx
    rw [Finset.sum_range] at hx
    have := Fintype.linearIndependent_iff.mp hli
      (fun i : Fin (j + t + 1) => (recPoly (p ^ e) c 0 i).eval y) hx ⟨j + t, by omega⟩
    exact hy0 (by simpa [hy'] using this)
end GroundTheory.PAdicHodge.SemilinearResidue
