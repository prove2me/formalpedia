-- Prove2me | solution 1 for MayersBC.effectProb_sub_le_two_norm_sub
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:25:16.679657+00:00
-- url     : https://prove2.me/submissions/cbfb45c9-7fec-489d-a8d1-b7325d6576a6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate

namespace MayersBCPerturbAux

/-- `Tr(M |φ⟩⟨φ|) = ⟨φ|M|φ⟩`, written with `dotProduct`. -/
lemma trace_mul_pureDensity' {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) :
    (M * pureDensity φ).trace = star (WithLp.ofLp φ) ⬝ᵥ (M *ᵥ WithLp.ofLp φ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- If `G = Bᴴ B`, then `⟨φ|G|φ⟩ = ‖B φ‖²`. -/
lemma effectProb_eq_normSq {ι : Type} [Fintype ι] (B : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) :
    effectProb (Bᴴ * B) (pureDensity φ) =
      ‖(WithLp.toLp 2 (B *ᵥ WithLp.ofLp φ) : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [effectProb, trace_mul_pureDensity', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star, ← inner_self_eq_norm_sq (𝕜 := ℂ),
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

/-- An effect accepts `φ` with "probability" at most `‖φ‖²`. -/
lemma effectProb_le_normSq {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ}
    (hG : IsEffect G) (φ : EuclideanSpace ℂ ι) : effectProb G (pureDensity φ) ≤ ‖φ‖ ^ 2 := by
  have h1 : 0 ≤ (star (WithLp.ofLp φ) ⬝ᵥ ((1 - G) *ᵥ WithLp.ofLp φ)).re :=
    (Complex.nonneg_iff.mp (hG.2.dotProduct_mulVec_nonneg _)).1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h1
  have h2 : (star (WithLp.ofLp φ) ⬝ᵥ WithLp.ofLp φ).re = ‖φ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
    rfl
  rw [effectProb, trace_mul_pureDensity']
  linarith

end MayersBCPerturbAux

open MayersBCPerturbAux in
theorem solution {κ : Type} [Fintype κ] [DecidableEq κ]
    (φ0 φ1 : EuclideanSpace ℂ κ) (h0 : IsState φ0) (h1 : IsState φ1) (G : Matrix κ κ ℂ)
    (hG : IsEffect G) (ε : ℝ) (hov : 1 - 2 * ε ≤ (inner ℂ φ0 φ1).re) :
    |effectProb G (pureDensity φ0) - effectProb G (pureDensity φ1)| ≤
        2 * Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) ∧
      Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) ≤ ‖φ0 - φ1‖ ∧
      ‖φ0 - φ1‖ = Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ∧
      2 * Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ≤ 4 * Real.sqrt ε := by
  have hn0 : ‖φ0‖ = 1 := h0
  have hn1 : ‖φ1‖ = 1 := h1
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.1.nonneg
  have hBG : G = Bᴴ * B := hB
  -- `u = B φ0`, `v = B φ1`
  set u : EuclideanSpace ℂ κ := WithLp.toLp 2 (B *ᵥ WithLp.ofLp φ0) with hu
  set v : EuclideanSpace ℂ κ := WithLp.toLp 2 (B *ᵥ WithLp.ofLp φ1) with hv
  have hφ0 : effectProb G (pureDensity φ0) = ‖u‖ ^ 2 := by rw [hBG, effectProb_eq_normSq]
  have hφ1 : effectProb G (pureDensity φ1) = ‖v‖ ^ 2 := by rw [hBG, effectProb_eq_normSq]
  have hδ : effectProb G (pureDensity (φ0 - φ1)) = ‖u - v‖ ^ 2 := by
    rw [hBG, effectProb_eq_normSq, hu, hv, WithLp.ofLp_sub, Matrix.mulVec_sub, WithLp.toLp_sub]
  have hu1 : ‖u‖ ≤ 1 := by
    have := effectProb_le_normSq hG φ0
    rw [hφ0, hn0] at this
    nlinarith [norm_nonneg u]
  have hv1 : ‖v‖ ≤ 1 := by
    have := effectProb_le_normSq hG φ1
    rw [hφ1, hn1] at this
    nlinarith [norm_nonneg v]
  have hsqrtδ : Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) = ‖u - v‖ := by
    rw [hδ, Real.sqrt_sq (norm_nonneg _)]
  -- `‖φ0 - φ1‖² = 2 - 2 Re ⟨φ0|φ1⟩`
  have hdist : ‖φ0 - φ1‖ ^ 2 = 2 * (1 - (inner ℂ φ0 φ1).re) := by
    rw [@norm_sub_sq ℂ, hn0, hn1]
    simp only [RCLike.re_to_complex]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- reverse triangle inequality: `|‖u‖² - ‖v‖²| ≤ ‖u - v‖ (‖u‖ + ‖v‖) ≤ 2 ‖u - v‖`
    rw [hφ0, hφ1, hsqrtδ]
    have htri : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
    have hfac : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ + ‖v‖)]
    have hsum : ‖u‖ + ‖v‖ ≤ 2 := by linarith
    calc |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
          mul_le_mul_of_nonneg_right htri (by positivity)
      _ ≤ ‖u - v‖ * 2 := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = 2 * ‖u - v‖ := by ring
  · -- `⟨δ|G|δ⟩ ≤ ‖δ‖²`
    have := effectProb_le_normSq hG (φ0 - φ1)
    calc Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) ≤ Real.sqrt (‖φ0 - φ1‖ ^ 2) :=
          Real.sqrt_le_sqrt this
      _ = ‖φ0 - φ1‖ := Real.sqrt_sq (norm_nonneg _)
  · rw [← hdist, Real.sqrt_sq (norm_nonneg _)]
  · -- `2 (1 - Re⟨φ0|φ1⟩) ≤ 4 ε`
    have h4 : 2 * (1 - (inner ℂ φ0 φ1).re) ≤ 4 * ε := by linarith
    have hs : Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ≤ 2 * Real.sqrt ε := by
      calc Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ≤ Real.sqrt (4 * ε) := Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt ε := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    linarith
