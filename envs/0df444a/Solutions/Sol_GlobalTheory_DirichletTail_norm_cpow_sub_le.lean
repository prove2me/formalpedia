-- Prove2me | solution 1 for GlobalTheory.DirichletTail.norm_cpow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:43.908104+00:00
-- url     : https://prove2.me/submissions/f7d2627e-bb8e-40a6-958a-20a1d2f0836f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {a b δ : ℝ} {s : ℂ} (ha : 1 ≤ a) (hab : a ≤ b) (hδ : 0 < δ)
    (hs : δ ≤ s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ / δ * (a ^ (-δ) - b ^ (-δ)) := by
  have hσ : 0 < s.re := lt_of_lt_of_le hδ hs
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h, Complex.zero_re] at hσ
    exact lt_irrefl _ hσ
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht ↦ lt_of_lt_of_le one_pos (ha.trans ht.1)
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt (fun x : ℝ ↦ (a : ℂ) ^ (-s) - (x : ℂ) ^ (-s))
      (-(-s * (t : ℂ) ^ (-s - 1))) t :=
    fun t ht ↦ (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' hs0).const_sub _
  have hB : ∀ t ∈ Set.Icc a b, HasDerivAt (fun x : ℝ ↦ ‖s‖ / δ * (a ^ (-δ) - x ^ (-δ)))
      (‖s‖ / δ * -((-δ) * t ^ (-δ - 1))) t :=
    fun t ht ↦ ((Real.hasDerivAt_rpow_const (Or.inl (hpos t ht).ne')).const_sub _).const_mul _
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun x : ℝ ↦ (a : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) (a := a) (b := b)
    (f' := fun t ↦ -(-s * (t : ℂ) ^ (-s - 1)))
    (B := fun x : ℝ ↦ ‖s‖ / δ * (a ^ (-δ) - x ^ (-δ)))
    (B' := fun t ↦ ‖s‖ / δ * -((-δ) * t ^ (-δ - 1)))
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hf t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp)
    (fun t ht ↦ (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hB t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    ?_ (Set.right_mem_Icc.mpr hab)
  intro t ht
  have ht1 : 1 ≤ t := ha.trans ht.1
  have htp : 0 < t := lt_of_lt_of_le one_pos ht1
  rw [norm_neg, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos htp]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  have h1 : t ^ (-s.re - 1) ≤ t ^ (-δ - 1) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have h2 : ‖s‖ / δ * -((-δ) * t ^ (-δ - 1)) = ‖s‖ * t ^ (-δ - 1) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
end GlobalTheory.DirichletTail
