-- Prove2me | solution 1 for MasulloRH.critical_line_mass_prime_comparison_through_one_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:15:57.183445+00:00
-- url     : https://prove2.me/submissions/b660f3c2-41a3-42ae-913b-22f39ed737e2

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5
import Theorems.Thm_MasulloRH_critical_line_mass_of_verified_height_and_prime_tail
import Mathlib

open Set Filter Topology MeasureTheory ArithmeticFunction
open MasulloRH

private theorem mangoldt_series_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)^x)
      (-(zetaLogDeriv (x:ℂ)).re) := by
  have hs : 1 < (x:ℂ).re := hx
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  have hv := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries _ (x:ℂ) = _ at hv
  change HasSum _ (LSeries _ (x:ℂ)) at h
  rw [hv,neg_div] at h
  have hR := Complex.hasSum_re h
  convert hR using 1
  · ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · change _ = (LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k:ℂ)) (x:ℂ) n).re
      rw [LSeries.term_of_ne_zero hn]
      simp only [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow n.cast_nonneg,
        ← Complex.ofReal_div, Complex.ofReal_re]
  · simp [zetaLogDeriv]

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


private theorem reference_bound :
    8*((zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re ≤ 9/2 := by
  let l (j : ℕ) := vonMangoldt j/(j:ℝ)^(5/2:ℝ)
  have hal := mangoldt_series_hasSum (x:=5/2) (by norm_num)
  push_cast at hal
  have hL : -(zetaLogDeriv (5/2)).re ≤ 1/2 := by
    obtain ⟨hs,ht⟩ := mangoldt_tail_envelope 2 (by decide)
    have hp (k : ℕ) : l (k+3) ≤ Real.log ↑(k+2+1) * (↑(k+2+1):ℝ)^(-(5/2):ℝ) := by
      change vonMangoldt (k+3)/(↑(k+3):ℝ)^(5/2:ℝ) ≤ _
      rw [show k+2+1 = k+3 by omega,Real.rpow_neg (Nat.cast_nonneg _),←div_eq_mul_inv]
      exact div_le_div_of_nonneg_right vonMangoldt_le_log (by positivity)
    have hsum : Summable l := hal.summable
    have htail := ((summable_nat_add_iff 3).mpr hsum).tsum_le_tsum hp hs
    have hsplit := hsum.sum_add_tsum_nat_add 3
    rw [show (∑' j,l j) = _ from hal.tsum_eq] at hsplit
    have hp2 : (∑ j ∈ Finset.range 3,l j) = Real.log 2/(2:ℝ)^(5/2:ℝ) := by
      norm_num [Finset.sum_range_succ,l,vonMangoldt_apply_prime (by decide : Nat.Prime 2)]
    rw [hp2] at hsplit
    have hroot : (7/5:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have h2 : (2:ℝ)^(5/2:ℝ) = 4*Real.sqrt 2 := by
      rw [show (5/2:ℝ) = 2+1/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_two,←Real.sqrt_eq_rpow]
      ring
    have h3 : (2:ℝ)^(-(3/2):ℝ) = 1/(2*Real.sqrt 2) := by
      rw [Real.rpow_neg (by norm_num),show (3/2:ℝ) = 1+1/2 by norm_num,
        Real.rpow_add (by norm_num),Real.rpow_one,←Real.sqrt_eq_rpow,one_div]
    rw [h2] at hsplit
    norm_num only [Nat.cast_ofNat] at ht
    rw [h3] at ht
    have b2 : Real.log 2/(4*Real.sqrt 2) ≤ (7/10)/(4*(7/5):ℝ) :=
      div_le_div₀ (by norm_num) (by linarith [Real.log_two_lt_d9]) (by norm_num) (by linarith)
    have b3 : (2/3*Real.log 2+4/9)*(1/(2*Real.sqrt 2)) ≤
        (2/3*(7/10)+4/9)/(2*(7/5):ℝ) := by
      rw [←div_eq_mul_one_div]
      exact div_le_div₀ (by norm_num) (by linarith [Real.log_two_lt_d9]) (by norm_num) (by linarith)
    linarith only [b2,b3,hsplit,htail,ht]
  have hC : Real.log 2/2 + Real.pi/4 -37/30 ≤ 0 := by linarith [Real.log_two_lt_d9,Real.pi_lt_d4]
  have hprime := regularized_reference_mass_prime_series
  have hmono := hprime.summable.tsum_le_tsum (fun j => sub_le_self (l j)
    (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg j.cast_nonneg (3:ℝ)))) hal.summable
  rw [hprime.tsum_eq,hal.tsum_eq] at hmono
  linarith only [hC,hL,hmono]

private theorem critical_to_100000 (z : ZetaZerosInTraceStrip (1/2)) (hz : |z.val.im| ≤ 100000) :
    z.val.re = 1/2 := by
  have hpos (s : ℂ) (hs : riemannZeta s=0) (h0 : 0 < s.re) (h1 : s.re < 1)
      (him : 0 ≤ s.im) (hhigh : s.im ≤ 100000) : s.re=1/2 := by
    by_cases h2 : s.im ≤ 2
    · exact (ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six h0 h1
        (by rw [abs_of_nonneg him]; linarith) hs).elim
    by_cases h14 : s.im ≤ 14
    · exact (TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen s h0 h1 (by linarith) h14 hs).elim
    by_cases h100 : s.im ≤ 100
    · exact TaoFivePrimes.rh_verified_block_14_1e2 s hs h0 h1 (by linarith) (by norm_num; exact h100)
    by_cases h1k : s.im ≤ 1000
    · exact TaoFivePrimes.rh_verified_block_1e2_1e3 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h1k)
    by_cases h10k : s.im ≤ 10000
    · exact TaoFivePrimes.rh_verified_block_1e3_1e4 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact h10k)
    exact TaoFivePrimes.rh_verified_block_1e4_1e5 s hs h0 h1 (by norm_num; linarith) (by norm_num; exact hhigh)
  by_cases hr : 0 ≤ z.val.im
  · exact hpos z.val z.prop.1 z.prop.2.1 z.prop.2.2.1 hr ((le_abs_self _).trans hz)
  have hnot (j : ℕ) : z.val ≠ -j := by
    intro he; have h := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have hnot1 : z.val ≠ 1 := by
    intro he; have h := congrArg Complex.re he; rw [Complex.one_re] at h; linarith [z.prop.2.2.1]
  have hzero : riemannZeta (1-z.val)=0 := by rw [riemannZeta_one_sub hnot hnot1,z.prop.1,mul_zero]
  have h := hpos (1-z.val) hzero (by simp; linarith [z.prop.2.2.1])
    (by simp; linarith [z.prop.2.1]) (by simp; linarith) (by simp; linarith [neg_le_abs z.val.im])
  simp at h
  linarith

private theorem prime_lower (p : ℕ) (hp : p.Prime) (hp100 : 100 ≤ p) :
    4*((p.sqrt:ℝ)-1)/(p:ℝ)^3 ≤ vonMangoldt p/(p:ℝ)^(5/2:ℝ)-vonMangoldt p/(p:ℝ)^(3:ℝ) := by
  have hp100' : (100:ℝ) ≤ p := by exact_mod_cast hp100
  have hp0 : 0 < (p:ℝ) := by linarith
  have hp9 : (10:ℝ) ≤ Real.sqrt p := (Real.le_sqrt (by norm_num) hp0.le).mpr (by nlinarith)
  have hlog : (4:ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<3^4) (show (3:ℝ)^4 ≤ p by norm_num; linarith)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_three_gt_d9]
  have hsq : (p.sqrt:ℝ) ≤ Real.sqrt (p:ℝ) :=
    (Real.le_sqrt (by positivity) hp0.le).mpr (by exact_mod_cast Nat.sqrt_le' p)
  have he : (p:ℝ)^(5/2:ℝ) * Real.sqrt p = (p:ℝ)^3 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hp0,show (5/2:ℝ)+1/2=3 by norm_num,Real.rpow_ofNat]
  have hkey : vonMangoldt p/(p:ℝ)^(5/2:ℝ)-vonMangoldt p/(p:ℝ)^(3:ℝ) =
      Real.log p*(Real.sqrt p-1)/(p:ℝ)^3 := by
    rw [vonMangoldt_apply_prime hp,Real.rpow_ofNat,←he]
    field_simp [hp0.ne',(Real.rpow_pos_of_pos hp0 (5/2:ℝ)).ne',(Real.sqrt_pos.mpr hp0).ne']
  rw [hkey]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _ ≤ 4*(Real.sqrt p-1) := by linarith only [hsq]
       _ ≤ _ := mul_le_mul_of_nonneg_right hlog (by linarith)

private theorem exact_nat_sqrt {n m : ℕ} (h : m*m ≤ n) (h' : n < (m+1)*(m+1)) :
    Nat.sqrt n = m := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr h')) (Nat.le_sqrt.mpr h)

theorem solution (N : ℕ) (hN : N ≤ 100) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ j ∈ Finset.range N, (vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
          vonMangoldt j / (j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  let P : Finset ℕ := {101,103,107,109,113,127,131,137,139,149}
  have hPs (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 100 ≤ p := by
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  apply critical_line_mass_of_verified_height_and_prime_tail 49998 N P
    (fun p hp => hN.trans (hPs p hp).2)
  · intro z hz
    exact critical_to_100000 z (hz.trans (by norm_num))
  · have hlog : Real.log (49998:ℝ) ≤ 16*(7/10) := by
      have he := Real.log_le_log (by norm_num : (0:ℝ)<49998) (show (49998:ℝ) ≤ 2^16 by norm_num)
      rw [Real.log_pow] at he
      norm_num only [Nat.cast_ofNat] at he
      linarith [Real.log_two_lt_d9]
    calc _ ≤ (1/4500:ℝ) := by
              norm_num only [Nat.cast_ofNat]
              linarith only [reference_bound,hlog]
         _ ≤ ∑ p ∈ P, 4*((p.sqrt:ℝ)-1)/(p:ℝ)^3 := by
              norm_num [P,Finset.sum_insert,Finset.sum_singleton,
                show Nat.sqrt 101 = 10 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 103 = 10 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 107 = 10 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 109 = 10 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 113 = 10 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 127 = 11 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 131 = 11 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 137 = 11 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 139 = 11 from exact_nat_sqrt (by decide) (by decide),
                show Nat.sqrt 149 = 12 from exact_nat_sqrt (by decide) (by decide)]
         _ ≤ _ := Finset.sum_le_sum fun p hp => prime_lower p (hPs p hp).1 (hPs p hp).2

