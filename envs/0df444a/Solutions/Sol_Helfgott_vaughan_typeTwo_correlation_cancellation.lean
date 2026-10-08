-- Prove2me | solution 1 for Helfgott.vaughan_typeTwo_correlation_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T11:20:08.774975+00:00
-- url     : https://prove2.me/submissions/15dec8d1-60a2-4611-9b06-49eb564af5ed

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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Floor.Semifield

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

theorem etaTwo_compact_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    (‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖) ∧
    (‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖) :=
  ⟨etaTwo_fourier_interval_cancellation y hy α hα A B,etaTwo_log_fourier_cancellation y hy α hα B⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Finset
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma finite_complex_cauchy_square {ι : Type*} (s : Finset ι) (a F : ι → ℂ) :
    ‖∑ d ∈ s,a d*F d‖^2 ≤ (∑ d ∈ s,‖a d‖^2)*(∑ d ∈ s,‖F d‖^2) := by
  have ht : ‖∑ d ∈ s,a d*F d‖ ≤ ∑ d ∈ s,‖a d‖*‖F d‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun d => a d*F d)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans (sum_mul_sq_le_sq_mul_sq s (fun d => ‖a d‖) (fun d => ‖F d‖))

lemma finite_correlation_energy_identity {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) :
    ((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ) =
      ∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n)) := by
  have hz (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z*conj z := by
    rw [Complex.sq_norm,Complex.mul_conj]
  simp_rw [Complex.ofReal_sum,hz,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma finite_correlation_energy_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    (∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2) ≤
      ∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n := by
  have h0 : 0 ≤ ∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ = ‖((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ = ‖∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      rw [finite_correlation_energy_identity]
    _ ≤ ∑ m ∈ M,∑ n ∈ M,‖b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul,Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC m hm n hn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma finite_bilinear_correlation_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    ‖∑ d ∈ D,∑ m ∈ M,a d*b m*K d m‖^2 ≤
      (∑ d ∈ D,‖a d‖^2)*(∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n) := by
  have hc := finite_complex_cauchy_square D a (fun d => ∑ m ∈ M,b m*K d m)
  have he : (∑ d ∈ D,a d*(∑ m ∈ M,b m*K d m)) =
      ∑ d ∈ D,∑ m ∈ M,a d*b m*K d m := by
    simp_rw [Finset.mul_sum,mul_assoc]
  rw [he] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (finite_correlation_energy_bound D M b K C hC)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma fourier_product_correlation (α : AddCircle (1 : ℝ)) (d m n : ℕ) :
    fourier ((d*m : ℕ) : ℤ) α*conj (fourier ((d*n : ℕ) : ℤ) α) =
      fourier (d : ℤ) (((m : ℤ)-(n : ℤ)) • α) := by
  rw [←fourier_neg,←fourier_add]
  have he : ((d*m : ℕ) : ℤ)+ -((d*n : ℕ) : ℤ) = (d : ℤ)*((m : ℤ)-(n : ℤ)) := by
    push_cast
    ring
  rw [he]
  simp only [fourier_apply,smul_smul]

theorem rectangular_bilinear_fourier_cancellation (α : AddCircle (1 : ℝ))
    (A B : ℕ) (M : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ M,a d*b m*fourier ((d*m : ℕ) : ℤ) α‖^2 ≤
      (∑ d ∈ Finset.Ico A B,‖a d‖^2)*
      (∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (1/(2*‖((m : ℤ)-(n : ℤ)) • α‖)))) := by
  apply finite_bilinear_correlation_bound
  intro m hm n hn
  simp_rw [fourier_product_correlation]
  by_cases hz : ((m : ℤ)-(n : ℤ)) • α = 0
  · simp [hz,fourier_eval_zero]
  · rw [if_neg hz]
    exact fourier_interval_cancellation _ hz A B

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Real
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma monotone_weighted_interval_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ)
    (A B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ P Q,‖∑ i ∈ Finset.Ico P Q,g i‖ ≤ C)
    (hf : ∀ i,0 ≤ f i)
    (hmono : ∀ i j,A ≤ i → i ≤ j → j < B → f i ≤ f j) :
    ‖∑ i ∈ Finset.Ico A B,f i • g i‖ ≤ f (B-1)*C := by
  by_cases hAB : A < B
  · have hshift : A+(B-A) = B := by omega
    have hhg : ∀ k ≤ B-A,
        ‖(∑ i ∈ Finset.range (B-A),g (A+i))-(∑ i ∈ Finset.range k,g (A+i))‖ ≤ C := by
      intro k hk
      rw [sum_range_shift_Ico g A (B-A),sum_range_shift_Ico g A k,hshift]
      have hs := Finset.sum_Ico_consecutive g (show A ≤ A+k by omega) (show A+k ≤ B by omega)
      rw [←hs,add_sub_cancel_left]
      exact hg (A+k) B
    have hh := weighted_range_monotone_norm_bound (fun i => f (A+i))
      (fun i => g (A+i)) (B-A) C hC hhg (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • g i),hshift] at hh
    have hlast : A+(B-A-1) = B-1 := by omega
    simpa only [hlast] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf _) hC

lemma antitone_weighted_interval_norm_bound (f : ℕ → ℝ) (g : ℕ → ℂ)
    (A B : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ P Q,‖∑ i ∈ Finset.Ico P Q,g i‖ ≤ C)
    (hf : ∀ i,0 ≤ f i)
    (hmono : ∀ i j,A ≤ i → i ≤ j → j < B → f j ≤ f i) :
    ‖∑ i ∈ Finset.Ico A B,f i • g i‖ ≤ f A*C := by
  by_cases hAB : A ≤ B
  · have hshift : A+(B-A) = B := by omega
    have hhg : ∀ k ≤ B-A,‖∑ i ∈ Finset.range k,g (A+i)‖ ≤ C := by
      intro k hk
      rw [sum_range_shift_Ico g A k]
      exact hg A (A+k)
    have hh := weighted_range_antitone_norm_bound (fun i => f (A+i))
      (fun i => g (A+i)) (B-A) C hC hhg (fun i _ => hf _) (by
        intro i j hij hj
        exact hmono (A+i) (A+j) (by omega) (by omega) (by omega))
    rw [sum_range_shift_Ico (fun i => f i • g i),hshift] at hh
    simpa only [add_zero] using hh
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    exact mul_nonneg (hf _) hC

theorem etaTwo_pair_fourier_interval_cancellation (y z : ℝ) (hy : 0 < y) (hz : 0 < z)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ 2*(4*Real.log 2)^2/‖α‖ := by
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  let g : ℕ → ℂ := fun d => (etaTwo ((d : ℝ)/z) : ℂ)*fourier (d : ℤ) α
  have hg : ∀ P Q,‖∑ d ∈ Finset.Ico P Q,g d‖ ≤ 4*Real.log 2/‖α‖ :=
    fun P Q => etaTwo_fourier_interval_cancellation z hz α hα P Q
  have hC : 0 ≤ 4*Real.log 2/‖α‖ := by positivity
  by_cases hAB : A ≤ B
  · let K := min B (max A (Nat.floor (y/2)+1))
    have hAK : A ≤ K := le_min hAB (le_max_left _ _)
    have hKB : K ≤ B := min_le_left _ _
    have hl := monotone_weighted_interval_norm_bound (fun d => etaTwo ((d : ℝ)/y)) g A K _ hC hg
      (fun d => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_monotone_lower
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hjf : j ≤ Nat.floor (y/2) := by dsimp [K] at hj;omega
          have hjcast : (j : ℝ) ≤ (Nat.floor (y/2) : ℝ) := by exact_mod_cast hjf
          have hjreal : (j : ℝ) ≤ y/2 := hjcast.trans (Nat.floor_le (by positivity))
          apply (div_le_iff₀ hy).mpr
          linarith)
    have hu := antitone_weighted_interval_norm_bound (fun d => etaTwo ((d : ℝ)/y)) g K B _ hC hg
      (fun d => etaTwo_nonneg _) (by
        intro i j hi hij hj
        apply etaTwo_antitone_upper
        · exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hy.le
        · have hfi : Nat.floor (y/2)+1 ≤ i := by dsimp [K] at hi;omega
          have hir : y/2 ≤ (i : ℝ) := (Nat.lt_floor_add_one (y/2)).le.trans (by exact_mod_cast hfi)
          apply (le_div_iff₀ hy).mpr
          linarith)
    have hs := Finset.sum_Ico_consecutive (fun d => etaTwo ((d : ℝ)/y) • g d) hAK hKB
    have he (P Q : ℕ) : (∑ d ∈ Finset.Ico P Q,etaTwo ((d : ℝ)/y) • g d) =
        ∑ d ∈ Finset.Ico P Q,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*fourier (d : ℤ) α := by
      simp only [g,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul]
    have hl' := hl.trans (mul_le_mul_of_nonneg_right (etaTwo_le _) hC)
    have hu' := hu.trans (mul_le_mul_of_nonneg_right (etaTwo_le _) hC)
    rw [←he A B,←hs]
    calc
      _ ≤ ‖∑ d ∈ Finset.Ico A K,etaTwo ((d : ℝ)/y) • g d‖+
        ‖∑ d ∈ Finset.Ico K B,etaTwo ((d : ℝ)/y) • g d‖ := norm_add_le _ _
      _ ≤ (4*Real.log 2)*(4*Real.log 2/‖α‖)+(4*Real.log 2)*(4*Real.log 2/‖α‖) := add_le_add hl' hu'
      _ = _ := by ring
  · have hBA : B ≤ A := by omega
    simp only [Finset.Ico_eq_empty_of_le hBA,Finset.sum_empty,norm_zero]
    positivity

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Real
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma etaTwo_pair_fourier_all_frequencies (y z : ℝ) (hy : 0 < y) (hz : 0 < z)
    (α : AddCircle (1 : ℝ)) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ (4*Real.log 2)^2*
        (if α = 0 then ((B-A : ℕ) : ℝ) else min ((B-A : ℕ) : ℝ) (2/‖α‖)) := by
  have hM : 0 ≤ 4*Real.log (2 : ℝ) := by positivity
  have htrivial : ‖∑ d ∈ Finset.Ico A B,((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*
      fourier (d : ℤ) α‖ ≤ (4*Real.log 2)^2*((B-A : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Ico A B,‖((etaTwo ((d : ℝ)/y)*etaTwo ((d : ℝ)/z) : ℝ) : ℂ)*fourier (d : ℤ) α‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Ico A B,(4*Real.log 2)^2 := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (etaTwo_nonneg _) (etaTwo_nonneg _)),
          show ‖fourier (d : ℤ) α‖ = 1 from Circle.norm_coe _,mul_one]
        simpa only [pow_two] using mul_le_mul (etaTwo_le _) (etaTwo_le _) (etaTwo_nonneg _) hM
      _ = _ := by simp [mul_comm]
  by_cases hα : α = 0
  · simpa only [if_pos hα] using htrivial
  · rw [if_neg hα,mul_min_of_nonneg _ _ (sq_nonneg _)]
    apply le_min htrivial
    calc
      _ ≤ 2*(4*Real.log 2)^2/‖α‖ := etaTwo_pair_fourier_interval_cancellation y z hy hz α hα A B
      _ = (4*Real.log 2)^2*(2/‖α‖) := by ring

lemma compact_bilinear_kernel_correlation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (A B m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ‖∑ d ∈ Finset.Ico A B,
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
      conj ((etaTwo (((d*n : ℕ) : ℝ)/y) : ℂ)*fourier ((d*n : ℕ) : ℤ) α)‖ ≤
      (4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have he (d : ℕ) :
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
      conj ((etaTwo (((d*n : ℕ) : ℝ)/y) : ℂ)*fourier ((d*n : ℕ) : ℤ) α) =
      ((etaTwo ((d : ℝ)/(y/(m : ℝ)))*etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℝ) : ℂ)*
        fourier (d : ℤ) (((m : ℤ)-(n : ℤ)) • α) := by
    have hem : ((d*m : ℕ) : ℝ)/y = (d : ℝ)/(y/(m : ℝ)) := by
      push_cast
      field_simp
    have hen : ((d*n : ℕ) : ℝ)/y = (d : ℝ)/(y/(n : ℝ)) := by
      push_cast
      field_simp
    rw [map_mul,Complex.conj_ofReal,hem,hen,Complex.ofReal_mul]
    rw [show ((etaTwo ((d : ℝ)/(y/(m : ℝ))) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)*
        ((etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℂ)*conj (fourier ((d*n : ℕ) : ℤ) α)) =
        ((etaTwo ((d : ℝ)/(y/(m : ℝ))) : ℂ)*(etaTwo ((d : ℝ)/(y/(n : ℝ))) : ℂ))*
          (fourier ((d*m : ℕ) : ℤ) α*conj (fourier ((d*n : ℕ) : ℤ) α)) by ring]
    rw [fourier_product_correlation]
  simp_rw [he]
  exact etaTwo_pair_fourier_all_frequencies (y/(m : ℝ)) (y/(n : ℝ))
    (div_pos hy hm0) (div_pos hy hn0) _ A B

theorem compact_bilinear_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (A B : ℕ) (M : Finset ℕ)
    (hM : ∀ m ∈ M,0 < m) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ M,a d*b m*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (∑ d ∈ Finset.Ico A B,‖a d‖^2)*
      (∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*((4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((B-A : ℕ) : ℝ)
         else min ((B-A : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)))) := by
  apply finite_bilinear_correlation_bound
  intro m hm n hn
  exact compact_bilinear_kernel_correlation y hy α A B m n (hM m hm) (hM n hn)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open ArithmeticFunction MeasureTheory Set Finset
open scoped BigOperators Classical

namespace Helfgott

lemma arithmeticCutoff_add_tail (U : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff U f+arithmeticTail U f = f := by
  unfold arithmeticTail
  abel

theorem vaughan_arithmetic_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) = vaughanTypeOne U-vaughanCorrection U V+
      arithmeticCutoff V vonMangoldt+vaughanTypeTwo U V := by
  let ml : ArithmeticFunction ℝ := arithmeticCutoff U (moebius : ArithmeticFunction ℝ)
  let mh : ArithmeticFunction ℝ := arithmeticTail U (moebius : ArithmeticFunction ℝ)
  let ll : ArithmeticFunction ℝ := arithmeticCutoff V vonMangoldt
  let lh : ArithmeticFunction ℝ := arithmeticTail V vonMangoldt
  have hm : ml+mh = (moebius : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail U _
  have hl : ll+lh = (vonMangoldt : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail V _
  have hz : (ml+mh)*(zeta : ArithmeticFunction ℝ) = 1 := by
    rw [hm,coe_moebius_mul_coe_zeta]
  change (vonMangoldt : ArithmeticFunction ℝ) = ml*log-ml*ll*zeta+ll+mh*lh*zeta
  rw [←vonMangoldt_mul_zeta,←hl]
  calc
    ll+lh = ll+((ml+mh)*zeta)*lh := by rw [hz,one_mul]
    _ = _ := by ring

lemma etaTwo_arithmetic_eq_zero (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 (Nat.floor y)) : f n*etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : Nat.floor y < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have hh := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_arithmetic_summable (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 (Nat.floor y))
  intro n hn
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

lemma etaTwo_arithmetic_expSum_finite (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor y), ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  dsimp only
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

theorem vaughan_etaTwo_expSum_identity (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α-
      expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((arithmeticCutoff V vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α := by
  simp_rw [etaTwo_arithmetic_expSum_finite _ y hy α]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_arithmetic_identity U V)
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply] at hn
  rw [hn]
  push_cast
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators Classical

namespace Helfgott

theorem truncated_divisor_sum_complex (B : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

lemma etaTwo_convolution_expSum_hyperbola (f g : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => (((f*g) n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (Nat.floor y), ∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
        ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have hindex : Finset.Ioc 0 (Nat.floor y) = Finset.Icc 1 (Nat.floor y) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  let F (d m : ℕ) : ℂ :=
    ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α
  rw [etaTwo_arithmetic_expSum_finite _ y hy α,hindex]
  have hinner (k : ℕ) :
      (((f*g) k*etaTwo ((k : ℝ)/y) : ℝ) : ℂ)*fourier (k : ℤ) α =
      ∑ d ∈ k.divisors, F d (k/d) := by
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)]
    rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have he : d*(k/d) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    simp only [F,he,Complex.ofReal_mul]
  simp_rw [hinner]
  rw [truncated_divisor_sum_complex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]

lemma arithmeticTail_zero_of_le (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    arithmeticTail U f n = 0 := by
  change f n-(if n ≤ U then f n else 0) = 0
  simp [hn]

lemma arithmeticTail_self_of_gt (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : U < n) :
    arithmeticTail U f n = f n := by
  change f n-(if n ≤ U then f n else 0) = f n
  simp [not_le_of_gt hn]

lemma vaughan_bilinear_coefficient_zero (U n : ℕ) (hn : n ≤ U) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  exact arithmeticTail_zero_of_le U d _ (hdn.trans hn)

lemma vaughan_bilinear_coefficient_short_moebius (U n : ℕ) (hn : n ≠ 1) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n =
      -(∑ d ∈ n.divisors.filter (fun d => d ≤ U), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have he : arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta =
      1-arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta := by
    unfold arithmeticTail
    rw [sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [he]
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply_ne hn,zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
  congr 1

lemma sum_Icc_of_low_zero (F : ℕ → ℂ) (U B : ℕ) (hF : ∀ n ≤ U, F n = 0) :
    (∑ n ∈ Finset.Icc 1 B, F n) = ∑ n ∈ Finset.Icc (U+1) B, F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨by omega,h2⟩
  · intro n hn hnot
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    have hnU : n ≤ U := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega,h2⟩)
    exact hF n hnU

theorem vaughan_typeTwo_bilinear_expSum (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc (V+1) (Nat.floor y), ∑ m ∈ Finset.Icc (U+1) (Nat.floor (y/(d : ℝ))),
        ((ArithmeticFunction.vonMangoldt d*
          (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
          etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have he : vaughanTypeTwo U V = arithmeticTail V ArithmeticFunction.vonMangoldt*
      (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) := by
    unfold vaughanTypeTwo
    ring
  rw [he,etaTwo_convolution_expSum_hyperbola _ _ y hy α]
  rw [sum_Icc_of_low_zero (U := V)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [sum_Icc_of_low_zero (U := U)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [arithmeticTail_self_of_gt V d _ (by have := (Finset.mem_Icc.mp hd).1;omega)]
    · intro m hm
      rw [vaughan_bilinear_coefficient_zero U m hm]
      simp
  · intro d hd
    rw [arithmeticTail_zero_of_le V d _ hd]
    simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Real ArithmeticFunction
open scoped BigOperators Classical ComplexConjugate

namespace Helfgott

lemma vaughan_typeTwo_full_rectangle (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc (V+1) (Nat.floor y),∑ m ∈ Finset.Icc (U+1) (Nat.floor y),
        (vonMangoldt d : ℂ)*
        ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ)*
        ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α) := by
  rw [vaughan_typeTwo_bilinear_expSum U V y hy α]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1;omega
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hfloor : Nat.floor (y/(d : ℝ)) ≤ Nat.floor y := Nat.floor_mono (div_le_self hy.le hdr)
  have he : (∑ m ∈ Finset.Icc (U+1) (Nat.floor (y/(d : ℝ))),
      ((vonMangoldt d*
        (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
        etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α) =
      ∑ m ∈ Finset.Icc (U+1) (Nat.floor y),
      ((vonMangoldt d*
        (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
        etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,(Finset.mem_Icc.mp hm).2.trans hfloor⟩
    · intro m hm hnot
      have hmf : Nat.floor (y/(d : ℝ))+1 ≤ m := by
        have hml := (Finset.mem_Icc.mp hm).1
        by_contra hh
        exact hnot (Finset.mem_Icc.mpr ⟨hml,by omega⟩)
      have hmr : y/(d : ℝ) < (m : ℝ) := (Nat.lt_floor_add_one (y/(d : ℝ))).trans_le (by exact_mod_cast hmf)
      have hprod : y < ((d*m : ℕ) : ℝ) := by
        have hh := (div_lt_iff₀ hd0).mp hmr
        push_cast
        nlinarith
      have hη : etaTwo (((d*m : ℕ) : ℝ)/y) = 0 := etaTwo_eq_zero_of_not_mem _ (by
        intro ht
        have hh := (div_le_iff₀ hy).mp ht.2
        linarith)
      simp only [hη,mul_zero,Complex.ofReal_zero,zero_mul]
  rw [he]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Complex.ofReal_mul]
  ring

theorem vaughan_typeTwo_correlation_cancellation_complete (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    ‖expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖^2 ≤
      (∑ d ∈ Finset.Icc (V+1) (Nat.floor y),(vonMangoldt d)^2)*
      (∑ m ∈ Finset.Icc (U+1) (Nat.floor y),∑ n ∈ Finset.Icc (U+1) (Nat.floor y),
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m| *
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n| *
        ((4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((Nat.floor y-V : ℕ) : ℝ)
         else min ((Nat.floor y-V : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)))) := by
  have hM : ∀ m ∈ Finset.Icc (U+1) (Nat.floor y),0 < m := by
    intro m hm
    have := (Finset.mem_Icc.mp hm).1
    omega
  have hh := compact_bilinear_fourier_cancellation y hy α (V+1) (Nat.floor y+1)
    (Finset.Icc (U+1) (Nat.floor y)) hM
    (fun d => (vonMangoldt d : ℂ))
    (fun m => ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ))
  rw [Finset.Ico_add_one_right_eq_Icc] at hh
  have hdif : Nat.floor y+1-(V+1) = Nat.floor y-V := by omega
  simp only [hdif,Complex.norm_real,Real.norm_eq_abs,sq_abs] at hh
  rw [vaughan_typeTwo_full_rectangle U V y hy α]
  exact hh

end Helfgott
end

open Helfgott Finset Real ArithmeticFunction

theorem solution (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    ‖expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖^2 ≤
      (∑ d ∈ Finset.Icc (V+1) (Nat.floor y),(vonMangoldt d)^2)*
      (∑ m ∈ Finset.Icc (U+1) (Nat.floor y),∑ n ∈ Finset.Icc (U+1) (Nat.floor y),
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m| *
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n| *
        ((4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((Nat.floor y-V : ℕ) : ℝ)
         else min ((Nat.floor y-V : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)))) := Helfgott.vaughan_typeTwo_correlation_cancellation_complete U V y hy α

#print axioms solution
