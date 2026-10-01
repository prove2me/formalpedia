-- Prove2me | solution 1 for JewellMRP.InfiniteStep.bias_formula
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:10:41.212624+00:00
-- url     : https://prove2.me/submissions/1a93b9b5-6a34-4aca-9adc-b86f0d883fae

import Definitions.Def_JewellMRP_InfiniteStep_Model
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open JewellMRP.InfiniteStep Matrix Finset

namespace CInfinite

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem superharmonic_constant (P : Matrix (S) (S) ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (hP : P.IsIrreducible)
    (v : S → ℝ) (hv : ∀ i, (P *ᵥ v) i ≤ v i) : ∀ i j, v i = v j := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hp1 (n : ℕ) : P^n *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      ext k
      simpa [Matrix.mulVec, dotProduct] using hrow k
  have hpow (n : ℕ) : ∀ j, (P^n *ᵥ v) j ≤ v j := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro j
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact (Finset.sum_le_sum (s := Finset.univ) (fun k _ => mul_le_mul_of_nonneg_left (ih k) (hn j k))).trans (hv j)
  have heq (j : S) : v i = v j := by
    obtain ⟨n, hn0, hnpos⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hn).mp hP i j
    have hnon (k : S) : 0 ≤ (P^n) i k * (v k-v i) :=
      mul_nonneg (Matrix.pow_apply_nonneg hn n i k) (sub_nonneg.mpr (hmin k (Finset.mem_univ _)))
    have hr : ∑ k, (P^n) i k = 1 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun (hp1 n) i
    have hs : ∑ k, (P^n) i k * (v k-v i) ≤ 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hr, one_mul]
      exact sub_nonpos.mpr (hpow n i)
    have hj := (Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)).trans hs
    have hz := le_antisymm hj (hnon j)
    have := (mul_eq_zero.mp hz).resolve_left hnpos.ne'
    linarith
  exact fun k j => (heq k).symm.trans (heq j)


theorem constant_fixed (P : Matrix S S ℝ) (hP : IsErgodic P)
    (v : S → ℝ) (hv : ∀ i j, v i = v j) : P *ᵥ v = v := by
  ext i
  change ∑ j, P i j * v j = v i
  simp_rw [hv _ i]
  rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP.1, one_mul]

theorem pow_constant_fixed (P : Matrix S S ℝ) (hP : IsErgodic P)
    (v : S → ℝ) (hv : ∀ i j, v i = v j) (n : ℕ) : P^n *ᵥ v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, constant_fixed P hP v hv]

theorem return_closed (P : Matrix S S ℝ) (ρ V0 : S → ℝ) (n : ℕ) :
    stepReturn P ρ V0 n = (∑ k ∈ Finset.range n, P^k *ᵥ ρ) + P^n *ᵥ V0 := by
  induction n with
  | zero => simp [stepReturn]
  | succ n ih =>
    rw [stepReturn, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Finset.sum_range_succ']
    simp_rw [Matrix.mulVec_mulVec, ← pow_succ']
    simp
    abel

theorem return_increment (P : Matrix S S ℝ) (hP : IsErgodic P) (ρ V0 : S → ℝ)
    (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    stepReturn P ρ V0 n - stepReturn P ρ V0 (n-1) = P^(n-1) *ᵥ ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel, return_closed, pow_constant_fixed P hP V0 hV0,
    Finset.sum_range_succ]
  abel

theorem limit_mul_vec (π ρ : S → ℝ) : limitMatrix π *ᵥ ρ = fun _ => gain π ρ := rfl

theorem bias_closed (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (ρ V0 : S → ℝ) (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    biasSeq P π ρ V0 n =
      (1 + ∑ j ∈ Finset.Ico 1 n, (P^j-limitMatrix π)-limitMatrix π) *ᵥ ρ + V0 := by
  have hr : (∑ k ∈ Finset.range n, P^k) = 1 + ∑ k ∈ Finset.Ico 1 n, P^k := by
    rw [← Finset.sum_range_add_sum_Ico _ hn]
    simp
  have hc : (Finset.Ico 1 n).card = n-1 := by simp
  unfold biasSeq
  rw [return_closed, pow_constant_fixed P hP V0 hV0, ← Matrix.sum_mulVec, hr]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, hc, Matrix.sub_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, limit_mul_vec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  have hncast : ((n-1 : ℕ) : ℝ) = (n:ℝ)-1 := by norm_cast
  rw [hncast]
  ring

end CInfinite

theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    biasSeq P π ρ V0 n =
      (1 + ∑ j ∈ Finset.Ico 1 n, (P ^ j - limitMatrix π) - limitMatrix π) *ᵥ ρ + V0 := by
  exact CInfinite.bias_closed P hP π ρ V0 hV0 n hn

