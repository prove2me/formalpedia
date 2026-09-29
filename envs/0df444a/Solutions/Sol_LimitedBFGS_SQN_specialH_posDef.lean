-- Prove2me | solution 1 for LimitedBFGS.SQN.specialH_posDef
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:22:56.519453+00:00
-- url     : https://prove2.me/submissions/6e7a2331-b54e-4468-8cea-425c1057ec8f

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix
open LimitedBFGS.SQN

theorem dot_smul {n : ℕ} (c : ℝ) (v w : Fin n → ℝ) :
    (c • v) ⬝ᵥ w = c * (v ⬝ᵥ w) := by
  rw [smul_dotProduct, smul_eq_mul]

theorem dot_smul' {n : ℕ} (c : ℝ) (v w : Fin n → ℝ) :
    v ⬝ᵥ (c • w) = c * (v ⬝ᵥ w) := by
  rw [dotProduct_smul, smul_eq_mul]

/-- `vecMulVec y s *ᵥ x` is the rank-one action `sᵀx · y`. -/
theorem vecMulVec_ys_mulVec {n : ℕ} (y s x : Fin n → ℝ) :
    vecMulVec y s *ᵥ x = (s ⬝ᵥ x) • y := by
  rw [← transpose_vecMulVec, mulVec_transpose, vecMul_vecMulVec, dotProduct_comm]

/-- The quadratic form of `ρ • s sᵀ` is `ρ (xᵀs)²`. -/
theorem dot_smul_vecMulVec {n : ℕ} (ρ : ℝ) (s x : Fin n → ℝ) :
    star x ⬝ᵥ ((ρ • vecMulVec s s) *ᵥ x) = ρ * (x ⬝ᵥ s) * (x ⬝ᵥ s) := by
  rw [smul_mulVec, dot_smul', dotProduct_mulVec, vecMul_vecMulVec, dot_smul,
    star_trivial, dotProduct_comm, mul_assoc]

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
  rw [bfgsStep, add_mulVec, dotProduct_add]
  by_cases hv : bfgsV s y *ᵥ x = 0
  · have hVeq : bfgsV s y *ᵥ x = x - bfgsRho s y • ((s ⬝ᵥ x) • y) := by
      rw [bfgsV, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_ys_mulVec]
    -- `V x = 0` reads off `x = ρ • ((sᵀx) • y)` as a *symmetric* rewrite:
    -- `hVeq ▸ hv` substitutes the `V x` end and leaves `sub_eq_zero.mp`
    -- needing the goal to be syntactically `V x = 0`, which it is here, so
    -- build the hypothesis directly instead of relying on `▸` position.
    have hx_eq : x - bfgsRho s y • ((s ⬝ᵥ x) • y) = 0 := by
      rw [← hVeq, hv]
    have hdotne : x ⬝ᵥ s ≠ 0 := by
      intro hxs
      apply hx
      -- `sub_eq_zero.mp hx_eq : x = (ρ • (sᵀx)) • y` (the remote error context
      -- shows `smul_mulVec` distributes the *outer* scalar, giving this
      -- association rather than `ρ • ((sᵀx) • y)`).  The goal therefore becomes
      -- `(ρ • (sᵀx)) • y = 0`, and `hxs : xᵀs = 0` must be turned into
      -- `sᵀx = 0` by symmetry of the inner product *before* it can fire.
      have hsx : s ⬝ᵥ x = 0 := by rw [← dotProduct_comm]; exact hxs
      rw [sub_eq_zero.mp hx_eq, hsx]
      simp
    rw [e1, hv, star_zero, zero_dotProduct, dot_smul_vecMulVec]
    -- goal: `0 < 0 + ρ * (xᵀs) * (xᵀs)`
    rw [zero_add]
    -- `ρ * a * a` parses as `(ρ * a) * a`, so reassociate to `ρ * (a * a)`
    -- and use `mul_self_pos : 0 < a * a ↔ a ≠ 0` for the square factor.
    rw [mul_assoc]
    have hsq : 0 < (x ⬝ᵥ s) * (x ⬝ᵥ s) := mul_self_pos.mpr hdotne
    exact mul_pos hρ hsq
  · have hpos : 0 < star x ⬝ᵥ (((bfgsV s y)ᵀ * H * bfgsV s y) *ᵥ x) := by
      rw [e1]
      exact hH.dotProduct_mulVec_pos (x := bfgsV s y *ᵥ x) hv
    -- `linarith` cannot see the `ρ ssᵀ` term through the abstract `hW`; name
    -- its explicit nonnegativity `ρ (xᵀs)² ≥ 0` and add it to the strict
    -- positivity of the first term.
    have hWnn : 0 ≤ star x ⬝ᵥ ((bfgsRho s y • vecMulVec s s) *ᵥ x) := by
      -- `dot_smul_vecMulVec` rewrites the *goal* into `ρ (xᵀs)² ≥ 0`, which is
      -- a product of three reals, not literally a square: the theorem states
      -- `ρ * (xᵀs) * (xᵀs)`, which parses as `(ρ * (xᵀs)) * (xᵀs)`.  `positivity`
      -- cannot reassociate to see `ρ ≥ 0`, so do it explicitly with `mul_nonneg`
      -- and `sq_nonneg`.
      rw [dot_smul_vecMulVec]
      rw [mul_assoc]
      nlinarith [sq_nonneg (x ⬝ᵥ s)]
    linarith

theorem specialHList_posDef {n : ℕ} {H₀ : Matrix (Fin n) (Fin n) ℝ} (hH₀ : H₀.PosDef)
    {pairs : List ((Fin n → ℝ) × (Fin n → ℝ))}
    (hall : ∀ p ∈ pairs, 0 < p.2 ⬝ᵥ p.1) : (specialHList H₀ pairs).PosDef := by
  induction pairs generalizing H₀ with
  | nil => simpa [specialHList] using hH₀
  | cons p ps ih =>
      have hp : 0 < p.2 ⬝ᵥ p.1 := hall p (by simp)
      have hrest : ∀ q ∈ ps, 0 < q.2 ⬝ᵥ q.1 := fun q hq => hall q (by simp [hq])
      rw [specialHList, List.foldl_cons]
      -- `induction ... generalizing H₀` reverts `H₀` and the hypothesis
      -- `hH₀` depending on it.  `H₀` is an *implicit* argument of the theorem,
      -- so after reverting it `ih` exposes only the two explicit arguments
      -- (the `PosDef` proof and the tail condition); naming the matrix as a
      -- positional argument is a type error.
      exact ih (bfgsStep_posDef H₀ hH₀ p.1 p.2 hp) hrest

theorem solution {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ)
    (s y : ℕ → Fin n → ℝ) (hys : ∀ i, 0 < y i ⬝ᵥ s i) (K : ℕ) :
    (specialH H₀ m s y K).PosDef := by
  -- `specialHList_posDef` takes `hH₀` then `hall`; there is no extra explicit
  -- argument, so apply the hypothesis directly and open `hall` with a goal.
  refine specialHList_posDef hH₀ ?_
  intro p hp
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hp
  have hi' : i < min K m := List.mem_range.mp hi
  have hmin : min K m ≤ K := Nat.min_le_left K m
  have heq2 : K - min K m + i = K - (min K m - i) := by omega
  rw [← heq, heq2]
  simp only [Prod.fst, Prod.snd]
  exact hys _
