-- Prove2me | solution 2 for LimitedBFGS.SQN.specialH_posDef
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:27:23.421754+00:00
-- url     : https://prove2.me/submissions/98a07098-4140-45df-9a7e-50e753fbf60a

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix
open LimitedBFGS.SQN

/-- `vecMulVec y s *ᵥ x` is the rank-one action `sᵀx · y`. -/
theorem vecMulVec_ys_mulVec {n : ℕ} (y s x : Fin n → ℝ) :
    vecMulVec y s *ᵥ x = (s ⬝ᵥ x) • y := by
  rw [← transpose_vecMulVec, mulVec_transpose, vecMul_vecMulVec, dotProduct_comm]

/-- The quadratic form of `ρ • s sᵀ` is `ρ (xᵀs)²`. -/
theorem dot_smul_vecMulVec {n : ℕ} (ρ : ℝ) (s x : Fin n → ℝ) :
    star x ⬝ᵥ ((ρ • vecMulVec s s) *ᵥ x) = ρ * (x ⬝ᵥ s) * (x ⬝ᵥ s) := by
  rw [smul_mulVec, dotProduct_smul, dotProduct_mulVec, vecMul_vecMulVec, dotProduct_comm,
    star_trivial, dotProduct_smul, smul_smul, smul_eq_mul, mul_assoc]

/-- One BFGS product-form step preserves positive definiteness. -/
theorem bfgsStep_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (s y : Fin n → ℝ) (hys : 0 < y ⬝ᵥ s) : (bfgsStep H s y).PosDef := by
  have hρ : 0 < bfgsRho s y := by
    rw [bfgsRho]
    positivity
  have hV : PosSemidef ((bfgsV s y)ᵀ * H * bfgsV s y) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hH.posSemidef.conjTranspose_mul_mul_same (B := bfgsV s y)
  have hW : PosSemidef (bfgsRho s y • vecMulVec s s) := by
    simpa only [star_trivial] using
      (posSemidef_vecMulVec_star_self (R := ℝ) (n := Fin n) s).smul hρ.le
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hV.isHermitian.add hW.isHermitian, ?_⟩
  intro x hx
  have e1 : star x ⬝ᵥ (((bfgsV s y)ᵀ * H * bfgsV s y) *ᵥ x)
      = star (bfgsV s y *ᵥ x) ⬝ᵥ (H *ᵥ (bfgsV s y *ᵥ x)) := by
    simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul,
      conjTranspose_eq_transpose_of_trivial]
  have hnonneg : 0 ≤ star x ⬝ᵥ (((bfgsV s y)ᵀ * H * bfgsV s y) *ᵥ x) := by
    rw [e1]
    exact hH.posSemidef.dotProduct_mulVec_nonneg (bfgsV s y *ᵥ x)
  have hWnonneg : 0 ≤ star x ⬝ᵥ ((bfgsRho s y • vecMulVec s s) *ᵥ x) := by
    rw [dot_smul_vecMulVec]
    nlinarith [sq_nonneg (x ⬝ᵥ s)]
  rw [bfgsStep, add_mulVec, dotProduct_add]
  by_cases hv : bfgsV s y *ᵥ x = 0
  · have hVeq : bfgsV s y *ᵥ x = x - bfgsRho s y • ((s ⬝ᵥ x) • y) := by
      rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_ys_mulVec]
    have hz : x = bfgsRho s y • ((s ⬝ᵥ x) • y) := sub_eq_zero.mp (hVeq ▸ hv)
    have hxy : ∃ c : ℝ, x = c • y := ⟨_, hz.trans (by rw [smul_smul])⟩
    obtain ⟨c, hxc⟩ := hxy
    have hne : x ⬝ᵥ s ≠ 0 := by
      intro h0
      apply hx
      have hcs : c * (y ⬝ᵥ s) = 0 := by
        calc c * (y ⬝ᵥ s) = c • (y ⬝ᵥ s) := (smul_eq_mul _ _).symm
          _ = (c • y) ⬝ᵥ s := (smul_dotProduct c y s).symm
          _ = x ⬝ᵥ s := by rw [hxc]
          _ = 0 := h0
      rcases mul_eq_zero.mp hcs with hc | hys0
      · rw [hc, zero_smul] at hxc
        exact hxc
      · exact absurd hys0 (ne_of_gt hys)
    rw [e1, hv, star_zero, zero_dotProduct, dot_smul_vecMulVec, zero_add, mul_assoc]
    exact mul_pos hρ (mul_self_pos.mpr hne)
  · have hpos : 0 < star x ⬝ᵥ (((bfgsV s y)ᵀ * H * bfgsV s y) *ᵥ x) := by
      rw [e1]
      exact hH.dotProduct_mulVec_pos (x := bfgsV s y *ᵥ x) hv
    exact add_pos_of_pos_of_nonneg hpos hWnonneg

theorem specialHList_posDef {n : ℕ} {H₀ : Matrix (Fin n) (Fin n) ℝ}
    {pairs : List ((Fin n → ℝ) × (Fin n → ℝ))} (hH₀ : H₀.PosDef)
    (hall : ∀ p ∈ pairs, 0 < p.2 ⬝ᵥ p.1) : (specialHList H₀ pairs).PosDef := by
  induction pairs generalizing H₀ with
  | nil => simpa [specialHList] using hH₀
  | cons p ps ih =>
      have hp : 0 < p.2 ⬝ᵥ p.1 := hall p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q.2 ⬝ᵥ q.1 := fun q hq => hall q (by simp [hq])
      rw [specialHList, List.foldl_cons]
      exact ih (bfgsStep_posDef H₀ hH₀ p.1 p.2 hp) hrest

theorem solution {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ)
    (s y : ℕ → Fin n → ℝ) (hys : ∀ i, 0 < y i ⬝ᵥ s i) (K : ℕ) :
    (specialH H₀ m s y K).PosDef := by
  refine specialHList_posDef hH₀ ?_
  intro p hp
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hp
  have hi' : i < min K m := List.mem_range.mp hi
  have hmin : min K m ≤ K := Nat.min_le_left K m
  have heq2 : K - min K m + i = K - (min K m - i) := by omega
  rw [← heq, heq2]
  simp only [Prod.fst, Prod.snd]
  exact hys _
