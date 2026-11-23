-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_boundary_gaussian_bessel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:45:09.230809+00:00
-- url     : https://prove2.me/submissions/b743bad0-1307-4418-adb4-eb2b5376fe32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_gaussian_hermite_diagonal_bessel
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_mixed_hermite_identity

open GrothendieckLB.Supplement MeasureTheory ProbabilityTheory
set_option maxHeartbeats 900000

theorem solution :
    ∀ θ : ℝ,
      let K := CQBoundary.phiThree (CQBoundary.unitPoint θ)
      let μ := gaussianReal 0 1
      let d := fun n : ℕ => ∫ x : ℝ, ∫ y : ℝ, K x y * ↑(QuadSDE.hermiteN n x * QuadSDE.hermiteN n y) ∂μ ∂μ
      let u := ∫ x : ℝ, ∫ y : ℝ, ‖K x y‖^2 ∂μ ∂μ
      let v := ∫ x : ℝ, ∫ y : ℝ, ‖CQBoundary.mixed K x y‖^2 ∂μ ∂μ
      u+4*v=CQBoundary.energy θ ∧ ‖d 0‖^2≤u ∧
        ∀ N : ℕ, (∑ k ∈ Finset.range N, ((k:ℝ)+1)^2*‖d (k+1)‖^2)≤v := by
  intro θ
  let μ := gaussianReal 0 1
  let K := CQBoundary.phiThree (CQBoundary.unitPoint θ)
  let F (p : ℝ×ℝ) := K p.1 p.2
  let L (p : ℝ×ℝ) := CQBoundary.mixed K p.1 p.2
  let d (n : ℕ) : ℂ := ∫ x : ℝ, ∫ y : ℝ, K x y * Complex.ofReal
    (QuadSDE.hermiteN n x * QuadSDE.hermiteN n y) ∂μ ∂μ
  let U := ∫ p : ℝ×ℝ, ‖F p‖^2 ∂μ.prod μ
  let V := ∫ p : ℝ×ℝ, ‖L p‖^2 ∂μ.prod μ
  obtain ⟨hF,hL,hid⟩ := cq_boundary_mixed_hermite_identity θ
  change MemLp F 2 (μ.prod μ) at hF
  change MemLp L 2 (μ.prod μ) at hL
  have hu := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hv := (memLp_two_iff_integrable_sq_norm hL.1).mp hL
  have hU := integral_prod _ hu
  have hV := integral_prod _ hv
  change U=_ at hU
  change V=_ at hV
  change _+4*_=CQBoundary.energy θ ∧ ‖d 0‖^2≤_ ∧ _
  constructor
  · calc _ = U+4*V := by rw [hU,hV]
         _ = ∫ p : ℝ×ℝ, ‖F p‖^2+4*‖L p‖^2 ∂μ.prod μ := by
           rw [integral_add hu (hv.const_mul 4),integral_const_mul]
         _ = _ := integral_prod _ (hu.add (hv.const_mul 4))
  constructor
  · have h0 (x : ℝ) : QuadSDE.hermiteN 0 x=1 := by simp [QuadSDE.hermiteN,Polynomial.hermite_zero]
    have hi : Integrable F (μ.prod μ) := hF.integrable (by norm_num)
    have hd : d 0=∫ p : ℝ×ℝ, F p ∂μ.prod μ := by
      simp only [d,h0,mul_one,Complex.ofReal_one]
      exact (integral_prod _ hi).symm
    have B := gaussian_hermite_diagonal_bessel F hF {0}
    simp only [Finset.sum_singleton,h0,one_mul,Complex.ofReal_one,mul_one] at B
    rw [hd,← hU]
    exact B
  · intro N
    have B := gaussian_hermite_diagonal_bessel L hL (Finset.range N)
    rw [← hV]
    apply le_trans ?_ B
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro k _
    change ((k:ℝ)+1)^2*‖d (k+1)‖^2 = ‖∫ p : ℝ×ℝ, L p * Complex.ofReal
      (QuadSDE.hermiteN k p.1*QuadSDE.hermiteN k p.2) ∂μ.prod μ‖^2
    have he := hid k
    change (∫ p : ℝ×ℝ, L p * Complex.ofReal (QuadSDE.hermiteN k p.1*QuadSDE.hermiteN k p.2) ∂μ.prod μ) = ((k:ℂ)+1)*d (k+1) at he
    rw [he,norm_mul,mul_pow,show ((k:ℂ)+1)=Complex.ofReal ((k:ℝ)+1) by push_cast; rfl,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
