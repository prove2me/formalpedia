-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_S3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:33:11.427271+00:00
-- url     : https://prove2.me/submissions/93621248-7ad5-4eed-ae32-fb5487abbee0

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_PLB

open Matrix

namespace LuoSunLiu.DIP.S3Aux
open LuoSunLiu.DIP

theorem sparse_mul {d : ℕ} (a : Fin d → ℝ) (ha : IsOneSparse a) (k l : Fin d) (hkl : k ≠ l) :
    a k * a l = 0 := by
  obtain ⟨j, c, -, rfl⟩ := ha
  by_cases hk : k = j
  · subst hk; rw [Pi.single_eq_of_ne (Ne.symm hkl)]; ring
  · rw [Pi.single_eq_of_ne hk]; ring

theorem sparse_dot {d : ℕ} (a v : Fin d → ℝ) (ha : IsOneSparse a) (i : Fin d) :
    (a ⬝ᵥ v) * a i = a i ^ 2 * v i := by
  obtain ⟨j, c, -, rfl⟩ := ha
  rw [single_dotProduct]
  by_cases hi : i = j
  · subst hi; rw [Pi.single_eq_same]; ring
  · rw [Pi.single_eq_of_ne hi]; ring

theorem sum_range_Icc (t : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range t, f (s + 1) = ∑ s ∈ Finset.Icc 1 t, f s := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun s _ => by rw [add_comm]

theorem V_posDef {d : ℕ} {Ω : Type*} (lam : ℝ) (hlam : 0 < lam) (A : ℕ → Ω → Fin d → ℝ)
    (n : ℕ) (ω : Ω) : (BanditAlgorithm.regularizedDesignMatrix d lam A n ω).PosDef := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  refine (Matrix.PosDef.one.smul hlam).add_posSemidef (Matrix.posSemidef_sum _ fun s _ => ?_)
  simpa using Matrix.posSemidef_vecMulVec_self_star (A (s + 1) ω)

end LuoSunLiu.DIP.S3Aux

open LuoSunLiu.DIP LuoSunLiu.DIP.S3Aux in
theorem solution {d : ℕ} {Ω : Type*} (A ξ : ℕ → Ω → Fin d → ℝ) (C1 lam : ℝ)
    (hC1 : 0 ≤ C1) (hlam : 0 < lam) (t : ℕ) (ω : Ω)
    (hA : ∀ s ∈ Finset.Icc 1 t, IsOneSparse (A s ω))
    (hξ : ∀ s ∈ Finset.Icc 1 t, ∀ i, |ξ s ω i| ≤ C1) :
    mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)
        (shadowParam A ξ (t + 1) ω -
          (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
            ∑ s ∈ Finset.Icc 1 t, (A s ω ⬝ᵥ ξ s ω) • A s ω) ≤
      C1 * Real.sqrt (lam * d) := by
  set N : Fin d → ℝ := fun i => ∑ s ∈ Finset.Icc 1 t, A s ω i ^ 2 with hN
  set S : Fin d → ℝ := fun i => ∑ s ∈ Finset.Icc 1 t, A s ω i ^ 2 * ξ s ω i with hS
  have hN0 : ∀ i, 0 ≤ N i := fun i => Finset.sum_nonneg fun s _ => sq_nonneg _
  have hD : ∀ i, 0 < lam + N i := fun i => by linarith [hN0 i]
  have hSN : ∀ i, |S i| ≤ C1 * N i := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hN, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hξ s hs i) (sq_nonneg _)
  set V := BanditAlgorithm.regularizedDesignMatrix d lam A t ω with hVdef
  have hVd : V = diagonal (fun i => lam + N i) := by
    ext k l
    simp only [hVdef, BanditAlgorithm.regularizedDesignMatrix, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply, vecMulVec_apply, diagonal_apply,
      smul_eq_mul]
    rw [sum_range_Icc t (fun s => A s ω k * A s ω l)]
    by_cases hkl : k = l
    · subst hkl; simp only [if_true, mul_one, hN]
      congr 1; exact Finset.sum_congr rfl fun s _ => by ring
    · simp only [if_neg hkl, mul_zero, zero_add]
      exact Finset.sum_eq_zero fun s hs => sparse_mul _ (hA s hs) k l hkl
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 (V_posDef lam hlam A t ω).isUnit
  have hinv : ∀ r : Fin d → ℝ, V⁻¹ *ᵥ r = fun k => r k / (lam + N k) := by
    intro r
    have hw : V *ᵥ (fun k => r k / (lam + N k)) = r := by
      rw [hVd]; funext k; rw [mulVec_diagonal]; field_simp [(hD k).ne']
    conv_lhs => rw [← hw]
    rw [mulVec_mulVec, nonsing_inv_mul V hdet, one_mulVec]
  have hsum : ∑ s ∈ Finset.Icc 1 t, (A s ω ⬝ᵥ ξ s ω) • A s ω = S := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hS]
    exact Finset.sum_congr rfl fun s hs => sparse_dot _ _ (hA s hs) i
  have hshadow : shadowParam A ξ (t + 1) ω = fun i => S i / N i := by
    funext i; simp only [shadowParam, Nat.add_sub_cancel, hS, hN]
  rw [hsum, hinv S, hshadow]
  set diff : Fin d → ℝ := (fun i => S i / N i) - fun k => S k / (lam + N k) with hdiff
  have hterm : ∀ i, diff i * ((lam + N i) * diff i) ≤ lam * C1 ^ 2 := by
    intro i
    simp only [hdiff, Pi.sub_apply]
    have hDi := hD i
    rcases (hN0 i).lt_or_eq with hNi | hNi
    · have e : S i / N i - S i / (lam + N i) = lam * S i / (N i * (lam + N i)) := by
        field_simp; ring
      rw [e]
      have hS2 : S i ^ 2 ≤ (C1 * N i) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hSN i) 2
      have e2 : lam * S i / (N i * (lam + N i)) * ((lam + N i) * (lam * S i / (N i * (lam + N i))))
          = lam ^ 2 * S i ^ 2 / (N i ^ 2 * (lam + N i)) := by
        field_simp
      rw [e2, div_le_iff₀ (by positivity)]
      have : lam ^ 2 * S i ^ 2 ≤ lam ^ 2 * (C1 * N i) ^ 2 :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
      have h3 : lam ^ 2 * (C1 * N i) ^ 2 ≤ lam * C1 ^ 2 * (N i ^ 2 * (lam + N i)) := by
        have : 0 ≤ lam * C1 ^ 2 * N i ^ 3 := by positivity
        nlinarith
      linarith
    · have hS0 : S i = 0 := by
        have := hSN i
        rw [← hNi, mul_zero] at this
        exact abs_nonpos_iff.1 this
      rw [hS0]; simp; positivity
  unfold mNorm
  rw [hVd]
  have hdot : diff ⬝ᵥ diagonal (fun i => lam + N i) *ᵥ diff =
      ∑ i, diff i * ((lam + N i) * diff i) := by
    simp only [dotProduct, mulVec_diagonal]
  rw [hdot]
  calc Real.sqrt (∑ i, diff i * ((lam + N i) * diff i)) ≤ Real.sqrt (∑ _i : Fin d, lam * C1 ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hterm i)
    _ = C1 * Real.sqrt (lam * d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show (d : ℝ) * (lam * C1 ^ 2) = C1 ^ 2 * (lam * d) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC1]
