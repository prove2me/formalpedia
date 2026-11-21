-- Prove2me | solution 1 for MasulloRH.regularized_trace_error_le_finite_prime_zero_bound
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:56:56.902665+00:00
-- url     : https://prove2.me/submissions/bbd74a9b-56e2-41c5-94ba-13daded20aaa

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_regularized_trace_error_le_finite_resolvent_defect
import Mathlib

open MeasureTheory Filter Set Topology
open MasulloRH

private theorem mangoldt_tail_envelope (N : ℕ) (hN : 2 ≤ N) :
    Summable (fun n : ℕ => Real.log ↑(n+N+1) * (↑(n+N+1):ℝ)^(-(5/2):ℝ)) ∧
    ∑' n : ℕ, Real.log ↑(n+N+1) * (↑(n+N+1):ℝ)^(-(5/2):ℝ) ≤
      ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ) := by
  let g (x : ℝ) := Real.log x*x^(-(5/2):ℝ)
  let P (x : ℝ) := -((2/3)*Real.log x+4/9)*x^(-(3/2):ℝ)
  have hxN : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hg (x : ℝ) (hx : 0 < x) : HasDerivAt g
      ((1-(5/2)*Real.log x)*x^(-(7/2):ℝ)) x := by
    have d := (Real.hasDerivAt_log hx.ne').mul
      (Real.hasDerivAt_rpow_const (p:=-(5/2)) (.inl hx.ne'))
    apply d.congr_deriv
    rw [show (-(5/2):ℝ)-1 = -(7/2) by norm_num,
      show x^(-(5/2):ℝ) = x^(-(7/2):ℝ)*x by
        rw [←Real.rpow_add_one hx.ne']; norm_num]
    field_simp
    ring
  have hP (x : ℝ) (hx : x ∈ Ici (N:ℝ)) : HasDerivAt P (g x) x := by
    have hx0 : 0 < x := by change (N:ℝ) ≤ x at hx; linarith
    have d := ((((Real.hasDerivAt_log hx0.ne').const_mul (2/3)).add_const (4/9)).neg).mul
      (Real.hasDerivAt_rpow_const (p:=-(3/2)) (.inl hx0.ne'))
    apply d.congr_deriv
    dsimp [g]
    rw [show (-(3/2):ℝ)-1 = -(5/2) by norm_num,
      show x^(-(3/2):ℝ) = x^(-(5/2):ℝ)*x by
        rw [←Real.rpow_add_one hx0.ne']; norm_num]
    field_simp
    ring
  have anti : AntitoneOn g (Ici (N:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro x hx
      exact (hg x (lt_of_lt_of_le (by linarith) hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hg x (lt_of_lt_of_le (by linarith) (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxn : (N:ℝ) ≤ x := interior_subset hx
      have hx0 : 0 < x := by linarith
      have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) (hxN.trans hxn)
      rw [(hg x hx0).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_two_gt_d9])
        (Real.rpow_nonneg hx0.le _)
  have hpos (x : ℝ) (hx : x ∈ Ioi (N:ℝ)) : 0 ≤ g x := by
    change (N:ℝ) < x at hx
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.rpow_nonneg (by linarith) _)
  have hloglim := (isLittleO_log_rpow_atTop (r:=3/2) (by norm_num)).tendsto_div_nhds_zero
  have hpow := tendsto_rpow_neg_atTop (y:=3/2) (by norm_num)
  have hlim : Tendsto P atTop (𝓝 0) := by
    have h := ((hloglim.const_mul (2/3)).add (hpow.const_mul (4/9))).neg
    simp only [mul_zero,add_zero,neg_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    dsimp [P]
    rw [Real.rpow_neg hx.le]
    ring
  have hi := integrableOn_Ioi_deriv_of_nonneg' hP hpos hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hP hpos hlim
  constructor
  · have hS := AntitoneOn.summable_of_integrableOn_Ioi anti hi hpos
    simpa [g,Nat.add_assoc] using (summable_nat_add_iff (N+1)).mpr hS
  · calc _ ≤ ∫ x in Ioi (N:ℝ), g x := AntitoneOn.tsum_comp_add_le_integral N anti hi hpos
         _ = _ := by rw [he]; dsimp [P]; ring

theorem solution (N : ℕ) (hN : 2 ≤ N)
    (α R : ℝ) (s : ℂ) (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, |z.val.re-1/2| < α) :
    ‖zetaLogDeriv s-regularizedTraceRHS α s‖ ≤ 16*(2*(2*R+3)*(R+5/2)) *
      (Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range (N+1), (ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))) +
        ((2/3)*Real.log N+4/9)*(N:ℝ)^(-(3/2):ℝ) -
        ∑ z ∈ F,(zeroResolventTerm (1/2) 3 z).re) := by
  let f (n : ℕ) := ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ)
  have hsum := regularized_reference_mass_prime_series
  obtain ⟨hg,hupper⟩ := mangoldt_tail_envelope N hN
  have hterm (n : ℕ) : f (n+(N+1)) ≤
      Real.log ↑(n+N+1) * (↑(n+N+1):ℝ)^(-(5/2):ℝ) := by
    rw [← Nat.add_assoc]
    let k := n+N+1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
    have h0 : 0 ≤ (k:ℝ) := k.cast_nonneg
    change ArithmeticFunction.vonMangoldt k / (k:ℝ)^(5/2:ℝ) -
      ArithmeticFunction.vonMangoldt k / (k:ℝ)^(3:ℝ) ≤ Real.log (k:ℝ)*(k:ℝ)^(-(5/2):ℝ)
    rw [Real.rpow_neg h0, ← div_eq_mul_inv]
    exact (sub_le_self _ (div_nonneg hΛ (Real.rpow_nonneg h0 _))).trans
      (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.rpow_nonneg h0 _))
  have hfs : Summable f := hsum.summable
  have htail := ((summable_nat_add_iff (N+1)).mpr hfs).tsum_le_tsum hterm hg
  have he := hfs.sum_add_tsum_nat_add (N+1)
  rw [hsum.tsum_eq] at he
  have hbound := regularized_trace_error_le_finite_resolvent_defect α R s hR hs F hF
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by have := (norm_nonneg s).trans hR; positivity)
  apply sub_le_sub_right
  change _ ≤ _ + (∑ n ∈ Finset.range (N+1), f n) + _
  linarith only [he,htail.trans hupper]

