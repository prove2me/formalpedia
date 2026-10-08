-- Prove2me | solution 1 for Helfgott.etaTwo_compact_fourier_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T10:38:02.87023+00:00
-- url     : https://prove2.me/submissions/7ad9b039-454c-4b3a-a0b8-a63037fec2c8

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Ring

section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

lemma unit_geometric_interval_bound (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, z^n‖ ≤ min ((B-A : ℕ) : ℝ) (2/‖z-1‖) := by
  apply le_min
  · calc
      ‖∑ n ∈ Finset.Ico A B, z^n‖ ≤ ∑ n ∈ Finset.Ico A B, ‖z^n‖ := norm_sum_le _ _
      _ = ((B-A : ℕ) : ℝ) := by simp [norm_pow,hz]
  · by_cases hAB : A ≤ B
    · rw [geom_sum_Ico hz1 hAB,norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      calc
        ‖z^B-z^A‖ ≤ ‖z^B‖+‖z^A‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow,hz];norm_num
    · have hBA : B ≤ A := le_of_lt (lt_of_not_ge hAB)
      simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
      positivity

lemma fourier_nat_power (α : AddCircle (1 : ℝ)) (n : ℕ) :
    fourier (n : ℤ) α = (fourier 1 α)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,fourier_zero,pow_zero]
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

lemma circle_chord_lower (α : AddCircle (1 : ℝ)) : 4*‖α‖ ≤ ‖fourier 1 α-1‖ := by
  let r : ℝ := AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α
  have hr : r ∈ Set.Ico (-(1/2 : ℝ)) (-(1/2 : ℝ)+1) :=
    (AddCircle.equivIco (1 : ℝ) (-(1/2 : ℝ)) α).property
  have hrabs : |r| ≤ 1/2 := by
    apply abs_le.mpr
    constructor
    · exact hr.1
    · linarith [hr.2]
  have hrα : (r : AddCircle (1 : ℝ)) = α := AddCircle.coe_equivIco
  have hnorm : ‖α‖ = |r| := by
    rw [← hrα]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hrabs)
  have he : fourier 1 α = Complex.exp (Complex.I*((2*Real.pi*r : ℝ) : ℂ)) := by
    rw [← hrα,fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*r) (by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs' : 2*|r| ≤ |Real.sin (Real.pi*r)| := by
    rw [abs_mul,abs_of_pos Real.pi_pos] at hs
    have hc : 2/Real.pi*(Real.pi*|r|) = 2*|r| := by field_simp
    rwa [hc] at hs
  rw [hnorm,he,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hc : (2*Real.pi*r)/2 = Real.pi*r := by ring
  rw [hc,Real.norm_eq_abs,abs_mul]
  norm_num
  linarith

theorem fourier_interval_cancellation (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, fourier (n : ℤ) α‖ ≤
      min ((B-A : ℕ) : ℝ) (1/(2*‖α‖)) := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hz : ‖fourier 1 α‖ = 1 := Circle.norm_coe _
  have hc := circle_chord_lower α
  have hz1 : fourier 1 α ≠ 1 := by
    intro h
    rw [h,sub_self,norm_zero] at hc
    linarith
  have hb := unit_geometric_interval_bound (fourier 1 α) hz hz1 A B
  simp only [← fourier_nat_power] at hb
  apply hb.trans
  apply min_le_min_left
  calc
    2/‖fourier 1 α-1‖ ≤ 2/(4*‖α‖) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hc
    _ = 1/(2*‖α‖) := by field_simp;ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Finset
open scoped BigOperators Classical

namespace Helfgott

lemma weighted_range_prefix_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ k ≤ N, ‖∑ i ∈ Finset.range k, g i‖ ≤ C) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ ≤
      (|f (N-1)|+∑ i ∈ Finset.range (N-1), |f (i+1)-f i|)*C := by
  rw [Finset.sum_range_by_parts]
  calc
    ‖f (N-1) • (∑ i ∈ Finset.range N,g i)-
        ∑ i ∈ Finset.range (N-1),(f (i+1)-f i) • (∑ j ∈ Finset.range (i+1),g j)‖ ≤
      ‖f (N-1) • (∑ i ∈ Finset.range N,g i)‖+
        ∑ i ∈ Finset.range (N-1),‖(f (i+1)-f i) • (∑ j ∈ Finset.range (i+1),g j)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ |f (N-1)| *C+∑ i ∈ Finset.range (N-1),|f (i+1)-f i| *C := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul,Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact hg (i+1) (by have := Finset.mem_range.mp hi;omega)
    _ = _ := by rw [← Finset.sum_mul];ring

lemma weighted_range_antitone_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ k ≤ N, ‖∑ i ∈ Finset.range k,g i‖ ≤ C)
    (hf : ∀ i ≤ N, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f j ≤ f i) :
    ‖∑ i ∈ Finset.range N,f i • g i‖ ≤ f 0*C := by
  by_cases hN : N=0
  · simp only [hN,Finset.range_zero,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf 0 (by omega)) hC
  · have hlast : N-1 < N := by omega
    have hd : (∑ i ∈ Finset.range (N-1), |f (i+1)-f i|) = f 0-f (N-1) := by
      calc
        _ = ∑ i ∈ Finset.range (N-1), (f i-f (i+1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hm := hmono i (i+1) (by omega) (by have := Finset.mem_range.mp hi;omega)
          rw [abs_of_nonpos (sub_nonpos.mpr hm)]
          ring
        _ = _ := Finset.sum_range_sub' f (N-1)
    have hh := weighted_range_prefix_norm_bound f g N C hC hg
    rwa [abs_of_nonneg (hf (N-1) (by omega)),hd,add_sub_cancel] at hh

lemma sum_range_by_parts_tail (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ Finset.range N,f i • g i) =
      f 0 • (∑ i ∈ Finset.range N,g i)+
      ∑ i ∈ Finset.range (N-1),(f (i+1)-f i) •
        ((∑ j ∈ Finset.range N,g j)-(∑ j ∈ Finset.range (i+1),g j)) := by
  rw [Finset.sum_range_by_parts]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_smul,Finset.sum_range_sub,sub_smul]
  abel

lemma weighted_range_monotone_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ k ≤ N, ‖(∑ i ∈ Finset.range N,g i)-(∑ i ∈ Finset.range k,g i)‖ ≤ C)
    (hf : ∀ i ≤ N, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) :
    ‖∑ i ∈ Finset.range N,f i • g i‖ ≤ f (N-1)*C := by
  rw [sum_range_by_parts_tail]
  calc
    _ ≤ ‖f 0 • (∑ i ∈ Finset.range N,g i)‖+
        ∑ i ∈ Finset.range (N-1),‖(f (i+1)-f i) •
          ((∑ j ∈ Finset.range N,g j)-(∑ j ∈ Finset.range (i+1),g j))‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ f 0*C+∑ i ∈ Finset.range (N-1),(f (i+1)-f i)*C := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hf 0 (by omega))]
        exact mul_le_mul_of_nonneg_left (by simpa using hg 0 (by omega)) (hf 0 (by omega))
      · apply Finset.sum_le_sum
        intro i hi
        have hiN : i+1 < N := by have := Finset.mem_range.mp hi;omega
        have hd : 0 ≤ f (i+1)-f i := sub_nonneg.mpr (hmono i (i+1) (by omega) hiN)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by omega)) hd
    _ = _ := by rw [← Finset.sum_mul,Finset.sum_range_sub];ring

lemma sum_range_shift_Ico (g : ℕ → ℂ) (A k : ℕ) :
    (∑ i ∈ Finset.range k,g (A+i)) = ∑ i ∈ Finset.Ico A (A+k),g i := by
  simpa only [Finset.range_eq_Ico,zero_add,add_zero,Nat.add_comm k A] using Finset.sum_Ico_add g 0 k A

theorem monotone_weighted_fourier_interval_bound (f : ℕ → ℝ)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ)
    (hf : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, A ≤ i → i ≤ j → j < B → f i ≤ f j) :
    ‖∑ i ∈ Finset.Ico A B,f i • fourier (i : ℤ) α‖ ≤ f (B-1)/(2*‖α‖) := by
  have hC : 0 ≤ 1/(2*‖α‖) := by positivity
  by_cases hAB : A < B
  · have hshift : A+(B-A) = B := by omega
    have hg : ∀ k ≤ B-A,
        ‖(∑ i ∈ Finset.range (B-A),fourier ((A+i : ℕ) : ℤ) α)-
          (∑ i ∈ Finset.range k,fourier ((A+i : ℕ) : ℤ) α)‖ ≤ 1/(2*‖α‖) := by
      intro k hk
      rw [sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A (B-A),sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A k,hshift]
      have hsum := Finset.sum_Ico_consecutive (fun i => fourier (i : ℤ) α)
        (show A ≤ A+k by omega) (show A+k ≤ B by omega)
      rw [← hsum,add_sub_cancel_left]
      exact (fourier_interval_cancellation α hα (A+k) B).trans (min_le_right _ _)
    have hh := weighted_range_monotone_norm_bound (fun i => f (A+i))
      (fun i => fourier ((A+i : ℕ) : ℤ) α) (B-A) (1/(2*‖α‖)) hC hg
      (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • fourier (i : ℤ) α),hshift] at hh
    have hlast : A+(B-A-1) = B-1 := by omega
    simpa only [hlast,div_eq_mul_inv,one_mul] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact div_nonneg (hf _) (by positivity)

theorem antitone_weighted_fourier_interval_bound (f : ℕ → ℝ)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ)
    (hf : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, A ≤ i → i ≤ j → j < B → f j ≤ f i) :
    ‖∑ i ∈ Finset.Ico A B,f i • fourier (i : ℤ) α‖ ≤ f A/(2*‖α‖) := by
  have hC : 0 ≤ 1/(2*‖α‖) := by positivity
  by_cases hAB : A ≤ B
  · have hshift : A+(B-A) = B := by omega
    have hg : ∀ k ≤ B-A,
        ‖∑ i ∈ Finset.range k,fourier ((A+i : ℕ) : ℤ) α‖ ≤ 1/(2*‖α‖) := by
      intro k hk
      rw [sum_range_shift_Ico (fun i => fourier (i : ℤ) α) A k]
      exact (fourier_interval_cancellation α hα A (A+k)).trans (min_le_right _ _)
    have hh := weighted_range_antitone_norm_bound (fun i => f (A+i))
      (fun i => fourier ((A+i : ℕ) : ℤ) α) (B-A) (1/(2*‖α‖)) hC hg
      (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • fourier (i : ℤ) α),hshift] at hh
    simpa only [add_zero,div_eq_mul_inv,one_mul] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact div_nonneg (hf _) (by positivity)

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

lemma etaTwo_monotone_lower (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1/2) :
    etaTwo s ≤ etaTwo t := by
  by_cases hs : 0 < s
  · have ht0 : 0 < t := hs.trans_le hst
    have hls : Real.log (2*s) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlt : Real.log (2*t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
    simp only [etaTwo,if_pos hs,if_pos ht0,abs_of_nonpos hls,abs_of_nonpos hlt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply max_le_max_right
    linarith
  · simpa [etaTwo,hs] using etaTwo_nonneg t

lemma etaTwo_antitone_upper (s t : ℝ) (hst : s ≤ t) (hs : 1/2 ≤ s) :
    etaTwo t ≤ etaTwo s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hls : 0 ≤ Real.log (2*s) := Real.log_nonneg (by linarith)
  have hlt : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
  simp only [etaTwo,if_pos hs0,if_pos ht0,abs_of_nonneg hls,abs_of_nonneg hlt]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le_max_right
  linarith

theorem etaTwo_fourier_interval_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖ := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  by_cases hAB : A ≤ B
  · let K := min B (max A (Nat.floor (y/2)+1))
    have hAK : A ≤ K := le_min hAB (le_max_left _ _)
    have hKB : K ≤ B := min_le_left _ _
    have hl := monotone_weighted_fourier_interval_bound (fun n => etaTwo ((n : ℝ)/y)) α hα A K
      (fun n => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_monotone_lower
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hjf : j ≤ Nat.floor (y/2) := by dsimp [K] at hj;omega
          have hjcast : (j : ℝ) ≤ (Nat.floor (y/2) : ℝ) := by exact_mod_cast hjf
          have hjreal : (j : ℝ) ≤ y/2 := hjcast.trans (Nat.floor_le (by positivity))
          apply (div_le_iff₀ hy).mpr
          linarith)
    have hu := antitone_weighted_fourier_interval_bound (fun n => etaTwo ((n : ℝ)/y)) α hα K B
      (fun n => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_antitone_upper
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hfi : Nat.floor (y/2)+1 ≤ i := by dsimp [K] at hi;omega
          have hir : y/2 ≤ (i : ℝ) := by
            have hh := Nat.lt_floor_add_one (y/2)
            exact hh.le.trans (by exact_mod_cast hfi)
          apply (le_div_iff₀ hy).mpr
          linarith)
    have hs := Finset.sum_Ico_consecutive
      (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) hAK hKB
    rw [← hs]
    have hl' : ‖∑ n ∈ Finset.Ico A K,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
        4*Real.log 2/(2*‖α‖) := by
      simp only [Complex.real_smul] at hl
      exact hl.trans (div_le_div_of_nonneg_right (etaTwo_le _) (by positivity))
    have hu' : ‖∑ n ∈ Finset.Ico K B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
        4*Real.log 2/(2*‖α‖) := by
      simp only [Complex.real_smul] at hu
      exact hu.trans (div_le_div_of_nonneg_right (etaTwo_le _) (by positivity))
    calc
      _ ≤ ‖∑ n ∈ Finset.Ico A K,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖+
        ‖∑ n ∈ Finset.Ico K B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ := norm_add_le _ _
      _ ≤ 4*Real.log 2/(2*‖α‖)+4*Real.log 2/(2*‖α‖) := add_le_add hl' hu'
      _ = _ := by field_simp;ring
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    positivity

theorem etaTwo_log_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (B : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖ := by
  let f : ℕ → ℝ := fun i => max (Real.log ((1+i : ℕ) : ℝ)) 0
  let g : ℕ → ℂ := fun i => (etaTwo (((1+i : ℕ) : ℝ)/y) : ℂ)*fourier ((1+i : ℕ) : ℤ) α
  have hC : 0 ≤ 4*Real.log 2/‖α‖ := by positivity
  have hg : ∀ k ≤ B,
      ‖(∑ i ∈ Finset.range B,g i)-(∑ i ∈ Finset.range k,g i)‖ ≤ 4*Real.log 2/‖α‖ := by
    intro k hk
    dsimp only [g]
    rw [sum_range_shift_Ico (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) 1 B,
      sum_range_shift_Ico (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α) 1 k]
    have hs := Finset.sum_Ico_consecutive
      (fun n => (etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α)
      (show 1 ≤ 1+k by omega) (show 1+k ≤ 1+B by omega)
    rw [← hs,add_sub_cancel_left]
    exact etaTwo_fourier_interval_cancellation y hy α hα _ _
  have hf : ∀ i ≤ B,0 ≤ f i := by intro i hi;exact le_max_right _ _
  have hm : ∀ i j,i ≤ j → j < B → f i ≤ f j := by
    intro i j hij hj
    apply max_le_max_right
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_left hij 1)
  have hh := weighted_range_monotone_norm_bound f g B (4*Real.log 2/‖α‖) hC hg hf hm
  by_cases hB : B=0
  · simp [hB]
  · have hlast : 1+(B-1) = B := by omega
    have heq : (∑ i ∈ Finset.range B,f i • g i) =
        ∑ n ∈ Finset.Icc 1 B,
          ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
      have hf' : ∀ i, f i = Real.log ((1+i : ℕ) : ℝ) := by
        intro i
        apply max_eq_left
        exact Real.log_nonneg (by
          have hi : (1 : ℕ) ≤ 1+i := by omega
          exact_mod_cast hi)
      simp only [hf',g,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul]
      rw [sum_range_shift_Ico (fun n => ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*
        fourier (n : ℤ) α)]
      rw [Nat.add_comm 1 B,Finset.Ico_add_one_right_eq_Icc]
    rw [heq] at hh
    dsimp only [f] at hh
    rw [hlast] at hh
    convert hh using 1 <;> ring

theorem etaTwo_compact_fourier_cancellation_complete (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    (‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖) ∧
    (‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖) :=
  ⟨etaTwo_fourier_interval_cancellation y hy α hα A B,etaTwo_log_fourier_cancellation y hy α hα B⟩

end Helfgott
end

open Helfgott

theorem solution (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    (‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖) ∧
    (‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖) := Helfgott.etaTwo_compact_fourier_cancellation_complete y hy α hα A B

#print axioms solution
