-- Prove2me | solution 1 for OAI.PiExponent.eventual_log_jets_give_cofinal_truncated_minors
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:44:45.841107+00:00
-- url     : https://prove2.me/submissions/8621b038-5e30-4f75-b813-e01cd3b535be

import Definitions.Def_PiExponent_FiniteMinorComparison
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_surjective_iff_of_weight_filtered_shift
import Theorems.Thm_OAI_PiExponent_logJetSurjective_truncatedLogMatrix
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem solution
    (m K : ℕ) (w0 v0 theta : ℚ) (F : ℝ)
    (p : Fin m → ℤ) (q w : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 < F)
    (hFlarge : 2 / (theta : ℝ) < F)
    (hq : ∀ i, 2 ≤ q i)
    (hw : ∀ i, w i = Nat.ceil (Real.log (q i : ℝ)))
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 theta w
      (fun j i => (j.val : ℂ) *
        OAI.PiExponent.MatrixArithmetic.rationalCenters p q i)) :
    ∀ L : ℝ, ∃ H : ℕ, L ≤ (H : ℝ) ∧ 0 < H ∧
      ∃ selection :
        OAI.PiExponent.InterpolationMatrix.Row K (v0 : ℝ) (theta : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) (H : ℝ) →
        OAI.PiExponent.InterpolationMatrix.Column (w0 : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) (H : ℝ),
        (OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F (H : ℝ) p q selection).det ≠ 0 := by
  classical
  have hv : 0 < (v0 : ℝ) := by exact_mod_cast hv0
  have ht : 0 < (theta : ℝ) := by exact_mod_cast htheta
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have hqi : 1 < (q i : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) (hq i))
    rw [hw i]
    exact Nat.succ_le_iff.mp (Nat.one_le_ceil_iff.mpr (Real.log_pos hqi))
  have hweights : (fun i => (w i : ℝ)) = MatrixArithmetic.logWeights q := by
    funext i
    simp only [MatrixArithmetic.logWeights, hw i]
  have hWpos : ∀ i, 0 < MatrixArithmetic.logWeights q i := by
    intro i
    rw [← congrFun hweights i]
    exact_mod_cast hwpos i
  have hFone : 1 / (theta : ℝ) < F := by
    have hi : 0 < 1 / (theta : ℝ) := one_div_pos.mpr ht
    have he : 2 / (theta : ℝ) = 2 * (1 / (theta : ℝ)) := by
      simp only [div_eq_mul_inv, one_mul]
    rw [he] at hFlarge
    linarith
  obtain ⟨D, hD, H0, hjet⟩ := hjet
  intro L
  let S : ℝ := ∑ i, MatrixArithmetic.logWeights q i / (theta : ℝ)
  obtain ⟨n, hn⟩ := exists_nat_ge (max L (max (H0 : ℝ) S))
  let H : ℕ := D * (n + 1)
  have hn1H : n + 1 ≤ H := by
    dsimp [H]
    calc
      n + 1 = 1 * (n + 1) := by simp
      _ ≤ D * (n + 1) := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_iff.mpr hD)
  have hnH : n ≤ H := (Nat.le_succ n).trans hn1H
  have hHpos : 0 < H := (Nat.succ_pos n).trans_le hn1H
  have hbound : max L (max (H0 : ℝ) S) ≤ (H : ℝ) :=
    hn.trans (by exact_mod_cast hnH)
  have hHL : L ≤ (H : ℝ) := (le_max_left _ _).trans hbound
  have hH0R : (H0 : ℝ) ≤ (H : ℝ) :=
    (le_max_left (H0 : ℝ) S).trans ((le_max_right L _).trans hbound)
  have hH0 : H0 ≤ H := by exact_mod_cast hH0R
  have hHS : S ≤ (H : ℝ) :=
    (le_max_right (H0 : ℝ) S).trans ((le_max_right L _).trans hbound)
  have hDH : D ∣ H := ⟨n + 1, rfl⟩
  let N : ℕ := Nat.ceil ((H : ℝ) / (v0 : ℝ))
  let T : Fin m → ℕ := MatrixArithmetic.truncationOrders q F (v0 : ℝ)
  have hlong : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K
        (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (MatrixArithmetic.logWeights q)
        (H : ℝ) (MatrixArithmetic.rationalCenters p q) (fun _ => N)).mulVecLin := by
    rw [← hweights]
    exact OAI.PiExponent.logJetSurjective_truncatedLogMatrix m K w0 v0 theta w
      (MatrixArithmetic.rationalCenters p q) H hw0 hv0 htheta hwpos
      (hjet H hH0 hDH)
  have hcoeff : ∀ (i : Fin m) (k : ℕ),
      (v0 : ℝ) * (k : ℝ) < MatrixArithmetic.logWeights q i / (theta : ℝ) →
      (InterpolationMatrix.truncatedLog N).coeff k =
        (InterpolationMatrix.truncatedLog (T i)).coeff k := by
    intro i k hk
    have hcost : MatrixArithmetic.logWeights q i / (theta : ℝ) ≤ S := by
      exact Finset.single_le_sum
        (fun j _ => (div_pos (hWpos j) ht).le) (Finset.mem_univ i)
    have hkH : (v0 : ℝ) * (k : ℝ) < (H : ℝ) :=
      hk.trans_le (hcost.trans hHS)
    have hkNreal : (k : ℝ) < (H : ℝ) / (v0 : ℝ) :=
      (lt_div_iff₀ hv).mpr (by simpa only [mul_comm] using hkH)
    have hkN : k < N := by
      change k < Nat.ceil ((H : ℝ) / (v0 : ℝ))
      exact Nat.lt_ceil.mpr hkNreal
    have hcostF : MatrixArithmetic.logWeights q i / (theta : ℝ) <
        F * MatrixArithmetic.logWeights q i := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        (mul_lt_mul_of_pos_right hFone (hWpos i))
    have hkTreal : (k : ℝ) < F * MatrixArithmetic.logWeights q i / (v0 : ℝ) :=
      (lt_div_iff₀ hv).mpr (by simpa only [mul_comm] using hk.trans hcostF)
    have hkT : k < T i := by
      change k < Nat.ceil (F * MatrixArithmetic.logWeights q i / (v0 : ℝ))
      exact Nat.lt_ceil.mpr hkTreal
    change (PowerSeries.trunc N (PowerSeries.log ℂ)).coeff k =
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ)).coeff k
    simp only [PowerSeries.coeff_trunc, if_pos hkN, if_pos hkT]
  have hshort : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K
        (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (MatrixArithmetic.logWeights q)
        (H : ℝ) (MatrixArithmetic.rationalCenters p q) T).mulVecLin := by
    exact (InterpolationMatrix.surjective_iff_of_weight_filtered_shift K
      (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (MatrixArithmetic.logWeights q)
      (H : ℝ) (MatrixArithmetic.rationalCenters p q)
      (fun _ => InterpolationMatrix.truncatedLog N)
      (fun i => InterpolationMatrix.truncatedLog (T i)) hv ht hWpos hcoeff).mp hlong
  obtain ⟨selection, _, hdet⟩ :=
    InterpolationMatrix.exists_full_row_minor_of_surjective
      (InterpolationMatrix.truncatedLogMatrix K
        (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (MatrixArithmetic.logWeights q)
        (H : ℝ) (MatrixArithmetic.rationalCenters p q) T) hshort
  exact ⟨H, hHL, hHpos, selection, hdet⟩
