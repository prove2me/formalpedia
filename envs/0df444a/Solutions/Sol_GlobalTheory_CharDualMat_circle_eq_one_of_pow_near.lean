-- Prove2me | solution 1 for GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:38.343197+00:00
-- url     : https://prove2.me/submissions/68e8047d-22e9-451d-8b1b-447f0ede5b21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
namespace GlobalTheory.CharDualMat
open ValuativeRel Matrix in
private lemma half_lt_re_of_norm_eq_one_of_norm_sub_one_lt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1) :
    1 / 2 < w.re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have h2 : (w.re - 1) ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm (w - 1)
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    have h0 : ‖w - 1‖ ^ 2 < 1 := by
      have := norm_nonneg (w - 1)
      nlinarith
    nlinarith
  nlinarith
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CharDualMat
end
end

set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
open ValuativeRel Matrix
namespace GlobalTheory.CharDualMat
namespace _root_.GlobalTheory.CharDualMat
theorem _root_.solution (z : Circle) (h : ∀ n : ℕ, ‖(z : ℂ) ^ n - 1‖ < 1) :
    z = 1 := by
  have hnorm : ∀ m : ℕ, ‖(z : ℂ) ^ (2 ^ m)‖ = 1 := fun m => by
    rw [norm_pow, Circle.norm_coe, one_pow]
  have hre : ∀ m : ℕ, 1 / 2 < ((z : ℂ) ^ (2 ^ m)).re := fun m =>
    half_lt_re_of_norm_eq_one_of_norm_sub_one_lt (hnorm m) (h _)
  have hsq : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ m)).re ^ 2 + ((z : ℂ) ^ (2 ^ m)).im ^ 2 = 1 := fun m => by
    have := Complex.sq_norm ((z : ℂ) ^ (2 ^ m))
    rw [hnorm m, Complex.normSq_apply] at this
    nlinarith
  have hstep : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ (m + 1))).re =
      ((z : ℂ) ^ (2 ^ m)).re ^ 2 - ((z : ℂ) ^ (2 ^ m)).im ^ 2 := fun m => by
    rw [pow_succ, pow_mul, sq, Complex.mul_re]
    ring
  have hgrow : ∀ m : ℕ, 3 ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z : ℂ) ^ (2 ^ m)).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hstep m, pow_succ]
      have hr := hre m
      have hs := hsq m
      have hle : ((z : ℂ) ^ (2 ^ m)).re ≤ 1 := by nlinarith [sq_nonneg ((z : ℂ) ^ (2 ^ m)).im]
      nlinarith
  have hd0 : (z : ℂ).re = 1 := by
    have hle : (z : ℂ).re ≤ 1 := by
      have := hsq 0
      simp only [pow_zero, pow_one] at this
      nlinarith [sq_nonneg (z : ℂ).im]
    by_contra hne
    have hpos : 0 < 1 - (z : ℂ).re := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · linarith
      · exact absurd heq hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := hgrow n
    have h2 := hre n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have him : (z : ℂ).im = 0 := by
    have := hsq 0
    simp only [pow_zero, pow_one, hd0] at this
    nlinarith [sq_nonneg (z : ℂ).im]
  apply Circle.ext_iff.mpr
  apply Complex.ext <;> simp [hd0, him]
end _root_.GlobalTheory.CharDualMat
end GlobalTheory.CharDualMat
