-- Prove2me | solution 1 for MayersQBC.effectProb_ge_normSq_inner
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T20:54:57.951261+00:00
-- url     : https://prove2.me/submissions/97380b8f-ca13-495e-9ab3-d6bf89d11071

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate

/-- `Tr(M |φ⟩⟨φ|) = ⟨φ|M|φ⟩`, written with `dotProduct`. -/
private lemma trace_mul_pureDensity' {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) :
    (M * pureDensity φ).trace = star (WithLp.ofLp φ) ⬝ᵥ (M *ᵥ WithLp.ofLp φ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- For a positive semidefinite `A`, the quadratic form `⟨x|A|x⟩` is a nonnegative real number. -/
private lemma quadForm_im_zero {ι : Type} [Fintype ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (x : ι → ℂ) : (star x ⬝ᵥ A *ᵥ x).im = 0 :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).2.symm

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (hE : IsEffect E) (ψ φ : EuclideanSpace ℂ ι) (hψ : IsState ψ)
    (hacc : effectProb E (pureDensity ψ) = 1) :
    ‖inner ℂ φ ψ‖ ^ 2 ≤ effectProb E (pureDensity φ) := by
  set x : ι → ℂ := WithLp.ofLp ψ with hxdef
  set y : ι → ℂ := WithLp.ofLp φ with hydef
  -- `⟨ψ|E|ψ⟩ = 1` as a complex number
  have hEx_re : (star x ⬝ᵥ E *ᵥ x).re = 1 := by
    have := hacc
    rw [effectProb, trace_mul_pureDensity'] at this
    exact this
  have hEx : star x ⬝ᵥ E *ᵥ x = 1 :=
    Complex.ext (by simpa using hEx_re) (by simpa using quadForm_im_zero hE.1 x)
  -- `⟨ψ|ψ⟩ = 1`
  have hxx : star x ⬝ᵥ x = 1 := by
    have h1 : (inner ℂ ψ ψ : ℂ) = x ⬝ᵥ star x := EuclideanSpace.inner_eq_star_dotProduct ψ ψ
    have h2 : (inner ℂ ψ ψ : ℂ) = ((‖ψ‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K ψ
    have hn : ‖ψ‖ = 1 := hψ
    rw [dotProduct_comm, ← h1, h2, hn]
    simp
  -- Step 1: `E ψ = ψ`, because `⟨ψ|(I - E)|ψ⟩ = 0` and `I - E ⪰ 0`.
  have hfix : E *ᵥ x = x := by
    have h0 : star x ⬝ᵥ (1 - E) *ᵥ x = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hxx, hEx, sub_self]
    have := (hE.2.dotProduct_mulVec_zero_iff x).mp h0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  -- Step 2: write `E = Bᴴ B` and apply Cauchy–Schwarz to `B φ` and `B ψ`.
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.1.nonneg
  have hBE : E = Bᴴ * B := hB
  -- the quadratic form of `E` is the squared norm of `B ·`
  have hquad : ∀ v : ι → ℂ, star v ⬝ᵥ E *ᵥ v = star (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
    intro v
    rw [hBE, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hnormsq : ∀ v : ι → ℂ,
      ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ ι)‖ ^ 2 = (star v ⬝ᵥ E *ᵥ v).re := by
    intro v
    rw [hquad, ← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm]
    rfl
  -- the overlap `⟨φ|ψ⟩` equals `⟨Bφ|Bψ⟩`
  have hov : (inner ℂ φ ψ : ℂ) = inner ℂ (WithLp.toLp 2 (B *ᵥ y) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (B *ᵥ x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_toLp_toLp,
      dotProduct_comm, dotProduct_comm (B *ᵥ x)]
    rw [← hxdef, ← hydef]
    conv_lhs => rw [← hfix]
    rw [hBE, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (B *ᵥ y) : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 (B *ᵥ x))
  have hφq : effectProb E (pureDensity φ) = (star y ⬝ᵥ E *ᵥ y).re := by
    rw [effectProb, trace_mul_pureDensity']
  have hx1 : ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ ι)‖ ^ 2 = 1 := by
    rw [hnormsq, hEx]; simp
  have hx1' : ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ ι)‖ = 1 := by
    have h0 : 0 ≤ ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ ι)‖ := norm_nonneg _
    nlinarith [hx1]
  rw [hov, hφq, ← hnormsq]
  have hnn : 0 ≤ ‖inner ℂ (WithLp.toLp 2 (B *ᵥ y) : EuclideanSpace ℂ ι)
      (WithLp.toLp 2 (B *ᵥ x))‖ := norm_nonneg _
  rw [hx1', mul_one] at hcs
  exact pow_le_pow_left₀ hnn hcs 2
