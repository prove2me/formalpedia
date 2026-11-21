-- Prove2me | solution 1 for MasulloRH.finite_ordinate_prime_ramp_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:12:51.216171+00:00
-- url     : https://prove2.me/submissions/73886043-5bc1-462f-98fb-90771b2aab44

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_prime_ramp_absolute_explicit_formula
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5
import Mathlib
open Finset ArithmeticFunction Set Filter Topology MeasureTheory
noncomputable section
open MasulloRH
namespace RampFiniteProof
private abbrev Z := ZetaZerosInTraceStrip (1/2)
private abbrev B : ℝ := 0.8749570698
private def G (x : ℝ) : ℝ := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)
private def K (x : ℝ) (z : Z) : ℂ := (analyticOrderNatAt riemannZeta z.val : ℂ) * (x:ℂ)^(z.val-1)/(z.val*(z.val-1))
private def S (x : ℝ) : ℂ := ∑' z : Z,K x z
private def A (t : ℝ) : ℝ := (Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2
private def tail (x : ℝ) : ℝ := ∫ t in Ioi x,A t
private def C₀ : ℝ := |Real.log (2*Real.pi)|+|Real.log (1/2)|

private theorem zero_upper (z : Z) : z.val.re ≤ B := by
  by_contra! h
  have hne : z.val ≠ 1 := fun he => by have := z.prop.2.2.1; simpa [he] using this
  have hfree := TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (1 : DirichletCharacter ℂ 1) h (fun he => hne he.2)
  simpa [z.prop.1] using hfree

private theorem Knorm_sum {x : ℝ} (hx : 1≤x) : Summable (fun z => ‖K x z‖) :=
  prime_ramp_integrated_explicit_formula.1 x hx

private theorem K_bound {x : ℝ} (hx : 1≤x) {θ : ℝ} (z : Z) (hz : z.val.re≤θ) :
    ‖K x z‖ ≤ x^(θ-1)*‖K 1 z‖ := by
  have hx0 : 0<x := by linarith
  unfold K
  simp only [Complex.ofReal_one,Complex.one_cpow,mul_one,norm_mul,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have h : x^(z.val-1).re ≤ x^(θ-1) := Real.rpow_le_rpow_of_exponent_le hx (by simp; linarith [hz])
  calc _ ≤ (‖(analyticOrderNatAt riemannZeta z.val:ℂ)‖*x^(θ-1))/(‖z.val‖*‖z.val-1‖) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (by positivity)
       _ = _ := by ring

private theorem S_bound_for {x θ : ℝ} (hx : 1≤x) (hz : ∀ z : Z, z.val.re≤θ) :
    ‖S x‖ ≤ x^(θ-1)*(∑' z : Z,‖K 1 z‖) := by
  calc ‖S x‖ ≤ ∑' z : Z,‖K x z‖ := norm_tsum_le_tsum_norm (Knorm_sum hx)
       _ ≤ ∑' z : Z,x^(θ-1)*‖K 1 z‖ := (Knorm_sum hx).tsum_le_tsum (fun z => K_bound hx z (hz z)) ((Knorm_sum (x:=1) le_rfl).mul_left _)
       _ = _ := tsum_mul_left

private theorem S_bound {x : ℝ} (hx : 1≤x) :
    ‖S x‖ ≤ x^(B-1)*(∑' z : Z,‖K 1 z‖) := S_bound_for hx zero_upper

private theorem A_bound {t : ℝ} (ht : 2≤t) : ‖A t‖ ≤ C₀*t^(-2:ℝ) := by
  have ht0 : 0<t := by linarith
  have hi : 0 < (t^2)⁻¹ := by positivity
  have hi' : (t^2)⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hlow : Real.log (1/2) ≤ Real.log (1-(t^2)⁻¹) := Real.log_le_log (by norm_num) (by linarith)
  have hup : Real.log (1-(t^2)⁻¹) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl : |Real.log (1-(t^2)⁻¹)| ≤ |Real.log (1/2)| := by rw [abs_of_nonpos hup,abs_of_nonpos (hlow.trans hup)]; linarith
  unfold A C₀
  rw [Real.rpow_neg ht0.le,Real.rpow_two,Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg t),div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ hi.le
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  linarith [abs_nonneg (Real.log (1-(t^2)⁻¹))]

private theorem A_ible {x : ℝ} (hx : 2≤x) : IntegrableOn A (Ioi x) := by
  have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by linarith : 0<x)).const_mul C₀
  have hm : Measurable A := by unfold A; fun_prop
  apply h.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact A_bound (hx.trans (le_of_lt ht))

private theorem tail_bound {x : ℝ} (hx : 2≤x) : ‖tail x‖ ≤ C₀/x := by
  have hx0 : 0<x := by linarith
  unfold tail
  apply (norm_integral_le_integral_norm _).trans
  calc _ ≤ ∫ t in Ioi x,C₀*t^(-2:ℝ) := by
          apply integral_mono_ae (A_ible hx).norm ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hx0).const_mul C₀)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using A_bound (hx.trans (le_of_lt ht))
       _ = _ := by rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hx0]; norm_num [div_eq_mul_inv,Real.rpow_neg_one]

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


private theorem reference_bounds :
    (-(zetaLogDeriv (5/2)).re ≤ 1/2) ∧
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
  exact ⟨hL,by linarith only [hC,hL,hmono]⟩


private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))
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

private theorem mid_low (z : Z) : 6 < |z.val.im| :=
  lt_of_not_ge fun h => ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1

private theorem kernel_weight (z : Z) : ‖K 1 z‖ ≤ 2*zeroDecayWeight (1/2) z := by
  let m := analyticOrderNatAt riemannZeta z.val
  have hy := mid_low z
  have hy2 : 1 ≤ z.val.im^2 := by nlinarith [sq_abs z.val.im,sq_nonneg (|z.val.im|-6)]
  have hz := Complex.abs_im_le_norm z.val
  have hz' : |z.val.im| ≤ ‖z.val-1‖ := by simpa using Complex.abs_im_le_norm (z.val-1)
  have hd : 0 < ‖z.val‖*‖z.val-1‖ := mul_pos (by linarith) (by linarith)
  have hden : 1+z.val.im^2 ≤ 2*(‖z.val‖*‖z.val-1‖) := by
    nlinarith [mul_le_mul hz hz' (abs_nonneg _) (norm_nonneg _),sq_abs z.val.im]
  simp only [K,Complex.ofReal_one,Complex.one_cpow,mul_one,norm_div,norm_mul,Complex.norm_natCast,zeroDecayWeight]
  rw [←mul_div_assoc,div_le_div_iff₀ hd (by positivity)]
  exact (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)).trans_eq (by ring)

private theorem total_kernel : (∑' z : Z,‖K 1 z‖) ≤ 6 := by
  have hl := zero_decay_tail_at_real_lattice 1
  have ht (z : Z) : (5/2+2*(1:ℕ):ℝ) < |z.val.im| := by linarith [mid_low z]
  simp only [Nat.cast_one,Real.log_one,add_zero] at ht hl
  simp only [if_pos (ht _)] at hl
  have hr := reference_bounds.2
  have hw : (∑' z : Z,zeroDecayWeight (1/2) z) ≤ 3 := by norm_num at hl hr; linarith
  have hh := (Knorm_sum (x:=1) le_rfl).tsum_le_tsum kernel_weight ((weighted_zero_summability (1/2) (by norm_num)).mul_left 2)
  rw [tsum_mul_left] at hh; linarith

private theorem arch_three : C₀≤3 := by
  have hlow : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hu := Real.log_le_log (by positivity : 0<2*Real.pi) (by linarith [Real.pi_lt_four] : 2*Real.pi≤(2:ℝ)^3)
  rw [Real.log_pow] at hu; norm_num at hu
  unfold C₀
  rw [abs_of_nonneg (Real.log_nonneg hlow),Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub,abs_neg,abs_of_nonneg (Real.log_nonneg (by norm_num : 1≤(2:ℝ)))]
  linarith [Real.log_two_lt_d9]

private theorem weight_tail (n : ℕ) :
    (∑' z : Z,if 5/2+2*(n:ℝ) < |z.val.im| then zeroDecayWeight (1/2) z else 0) ≤
      (10+Real.log n)/(5/2+2*(n:ℝ)-1) := by
  have h := zero_decay_tail_at_real_lattice n
  have hd : 0 < 5/2+2*(n:ℝ)-1 := by linarith [n.cast_nonneg (α:=ℝ)]
  apply h.trans
  rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hd]
  linarith [reference_bounds.2]

private theorem error_factor (k : ℕ) (hk : 1≤k) :
    ((k:ℝ)^4)^B * (2*((10+Real.log (k^2:ℕ))/(5/2+2*((k^2:ℕ):ℝ)-1))) ≤ 10*(k:ℝ)^2 := by
  let r : ℝ := k
  have hr : 1≤r := by dsimp [r]; exact_mod_cast hk
  have hr0 : 0<r := by linarith
  change (r^4)^B*(2*((10+Real.log (k^2:ℕ))/(5/2+2*((k^2:ℕ):ℝ)-1))) ≤ 10*r^2
  push_cast
  change (r^4)^B*(2*((10+Real.log (r^2))/(5/2+2*r^2-1))) ≤ 10*r^2
  rw [Real.log_pow]
  have hroot := Real.sq_sqrt hr0.le
  have hs : 1≤Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr
  have hs0 : 0<Real.sqrt r := by linarith
  have hlog : Real.log r ≤ 2*(Real.sqrt r-1) := by
    have h := Real.log_le_sub_one_of_pos hs0
    have h' := Real.log_pow (Real.sqrt r) 2
    rw [hroot] at h'; norm_num at h'; linarith
  have hfactor : 2*((10+2*Real.log r)/(5/2+2*r^2-1)) ≤ (10*Real.sqrt r)/(r^2) := by
    rw [←mul_div_assoc,div_le_div_iff₀ (by nlinarith) (by positivity)]
    have hb : 2*(10+2*Real.log r)≤20*Real.sqrt r := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg r),mul_pos hs0 (by norm_num : 0<(3/2:ℝ))]
  have hpower : (r^4)^B ≤ r^3*Real.sqrt r := by
    rw [←Real.rpow_natCast_mul hr0.le,Real.sqrt_eq_rpow,←Real.rpow_natCast r 3,←Real.rpow_add hr0]
    apply Real.rpow_le_rpow_of_exponent_le hr
    norm_num [B]
  have hden : 0 < 5/2+2*r^2-1 := by nlinarith
  have hlr := Real.log_nonneg hr
  simp only [Nat.cast_ofNat]
  change (r^4)^B*(2*((10+2*Real.log r)/(5/2+2*r^2-1))) ≤ 10*r^2
  calc (r^4)^B*(2*((10+2*Real.log r)/(5/2+2*r^2-1))) ≤ (r^3*Real.sqrt r) * ((10*Real.sqrt r)/(r^2)) := mul_le_mul hpower hfactor (by positivity) (by positivity)
       _ = 10*r^3*(Real.sqrt r)^2/r^2 := by ring
       _ = 10*r^2 := by rw [hroot]; field_simp

private def P (x : ℝ) (z : Z) : ℂ := (x:ℂ)*K x z

private theorem P_summable {x : ℝ} (hx : 1≤x) : Summable (P x) :=
  (Knorm_sum hx).of_norm.mul_left _

private theorem P_point {x θ : ℝ} (hx : 1≤x) (z : Z) (hz : z.val.re≤θ) :
    ‖P x z‖ ≤ x^θ*‖K 1 z‖ := by
  have hx0 : 0<x := by linarith
  rw [P,norm_mul,Complex.norm_real,Real.norm_of_nonneg hx0.le]
  apply (mul_le_mul_of_nonneg_left (K_bound hx z hz) hx0.le).trans_eq
  rw [←mul_assoc]
  congr 1
  conv_lhs => arg 1; rw [←Real.rpow_one x]
  rw [←Real.rpow_add hx0]; congr 1; ring

private theorem G_series {x : ℝ} (hx : 2≤x) :
    (G x:ℂ) = -(∑' z : Z,P x z)+(x*tail x:ℝ) := by
  have h := prime_ramp_absolute_explicit_formula.1 x hx
  change ((G x/x:ℝ):ℂ) = -S x+(tail x:ℂ) at h
  rw [Complex.ofReal_div] at h
  unfold P
  rw [tsum_mul_left]
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he := (div_eq_iff hx0).mp h
  change _ = -((x:ℂ)*S x)+_ 
  push_cast
  linear_combination he

private theorem finite_approx {k : ℕ} (hk : 2≤k) {θ : ℝ} (hθ : 1/2≤θ) :
    let x := (k:ℝ)^4
    let H := 5/2+2*((k^2:ℕ):ℝ)
    ∃ F : Finset Z, (∀ z : Z,z ∈ F ↔ θ<z.val.re ∧ |z.val.im|≤H) ∧
      |G x+(∑ z ∈ F,P x z).re| ≤ 19*x^θ := by
  classical
  let x := (k:ℝ)^4
  let H : ℝ := 5/2+2*((k^2:ℕ):ℝ)
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1≤k by omega)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hx : 2≤x := by dsimp [x]; exact (le_trans (by norm_num : (2:ℝ)≤2^4) (pow_le_pow_left₀ (by norm_num) hk2 4))
  have hx1 : 1≤x := by linarith
  have hx0 : 0<x := by linarith
  have hX := Real.rpow_nonneg hx0.le θ
  have hB := Real.rpow_nonneg hx0.le B
  let V : Set Z := {z | H < |z.val.im|}
  let F := ((finite_zeros_to_height H (by dsimp [H]; positivity)).subset
    (show {z : Z | θ<z.val.re ∧ |z.val.im|≤H} ⊆ {z : Z | |z.val.im|≤H} from fun _ h => h.2)).toFinset
  have hF (z : Z) : z ∈ F ↔ θ<z.val.re ∧ |z.val.im|≤H := Set.Finite.mem_toFinset _
  refine ⟨F,hF,?_⟩
  let U : Set Z := (F : Set Z)ᶜ
  let w := zeroDecayWeight (1/2)
  let m (z : Z) := x^θ*‖K 1 z‖ + (2*x^B)*(V.indicator w z)
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hiw : Summable (V.indicator w) := hw.indicator V
  have hm : Summable m := ((Knorm_sum (x:=1) le_rfl).mul_left _).add (hiw.mul_left _)
  have hw0 (z : Z) : 0≤w z := by dsimp [w,zeroDecayWeight]; positivity
  have hv0 (z : Z) : 0≤V.indicator w z := Set.indicator_nonneg (fun z _ => hw0 z) _
  have hbnd (z : Z) : ‖U.indicator (P x) z‖ ≤ m z := by
    by_cases hu : z ∈ U
    · rw [Set.indicator_of_mem hu]
      by_cases hr : z.val.re≤θ
      · exact (P_point hx1 z hr).trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (hv0 z)))
      have hv : z ∈ V := by
        by_contra h
        have hH : |z.val.im|≤H := le_of_not_gt h
        exact hu ((hF z).2 ⟨lt_of_not_ge hr,hH⟩)
      dsimp only [m]; rw [Set.indicator_of_mem hv]
      apply (P_point hx1 z (zero_upper z)).trans
      apply (mul_le_mul_of_nonneg_left (kernel_weight z) hB).trans
      calc x^B*(2*w z) = (2*x^B)*w z := by ring
           _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hX (norm_nonneg _))
    · rw [Set.indicator_of_notMem hu,norm_zero]
      exact add_nonneg (mul_nonneg hX (norm_nonneg _)) (mul_nonneg (by positivity) (hv0 z))
  have hsum := (P_summable hx1).indicator U
  have hU : ‖∑' z : Z,U.indicator (P x) z‖ ≤ 6*x^θ+10*(k:ℝ)^2 := by
    calc _ ≤ ∑' z : Z,‖U.indicator (P x) z‖ := norm_tsum_le_tsum_norm hsum.norm
         _ ≤ ∑' z : Z,m z := hsum.norm.tsum_le_tsum hbnd hm
         _ = x^θ*(∑' z : Z,‖K 1 z‖)+(2*x^B)*(∑' z : Z,V.indicator w z) := by
           unfold m
           rw [Summable.tsum_add ((Knorm_sum (x:=1) le_rfl).mul_left _) (hiw.mul_left _),tsum_mul_left,tsum_mul_left]
         _ ≤ _ := by
           have ht : (∑' z : Z,V.indicator w z) ≤ (10+Real.log (k^2:ℕ))/(H-1) := weight_tail (k^2)
           have htr := mul_le_mul_of_nonneg_left ht (show 0≤2*x^B by positivity)
           have hfac : x^B*(2*((10+Real.log (k^2:ℕ))/(H-1))) ≤ 10*(k:ℝ)^2 := error_factor k (by omega)
           have hlow := mul_le_mul_of_nonneg_left total_kernel hX
           apply add_le_add (hlow.trans_eq (mul_comm ..))
           apply htr.trans
           rw [mul_comm 2 (x^B),mul_assoc]
           exact hfac
  have hs : (∑ z ∈ F,P x z)+(∑' z : Z,U.indicator (P x) z) = ∑' z : Z,P x z := by
    rw [←_root_.tsum_subtype]
    exact (P_summable hx1).sum_add_tsum_compl (s:=F)
  have he := G_series hx
  rw [←hs] at he
  have hreal := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.add_re,Complex.neg_re] at hreal
  have ht : |x*tail x|≤3 := by
    have h := tail_bound hx
    rw [Real.norm_eq_abs] at h
    rw [abs_mul,abs_of_pos hx0]
    apply (mul_le_mul_of_nonneg_left h hx0.le).trans
    simpa [div_eq_mul_inv,hx0.ne',mul_comm,mul_left_comm] using arch_three
  have hsq : (k:ℝ)^2 ≤ x^θ := by
    calc (k:ℝ)^2 = x^(1/2:ℝ) := by
           rw [←Real.sqrt_eq_rpow]; dsimp [x]; rw [show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 hθ
  have hone := Real.one_le_rpow hx1 (show 0≤θ by linarith)
  change |G x+(∑ z ∈ F,P x z).re|≤19*x^θ
  have hE : G x+(∑ z ∈ F,P x z).re = -(∑' z : Z,U.indicator (P x) z).re+x*tail x := by linarith
  rw [hE]
  apply (abs_add_le ..).trans
  rw [abs_neg]
  linarith [Complex.abs_re_le_norm (∑' z : Z,U.indicator (P x) z)]

private theorem explicit_nine {θ x : ℝ} (hθ : 0≤θ) (hz : ∀ z : Z,z.val.re≤θ) (hx : 2≤x) :
    |G x| ≤ 9*x^θ := by
  have h := prime_ramp_absolute_explicit_formula.2.1 θ hθ hz x hx
  change |G x| ≤ ((∑' z : Z,‖K 1 z‖)+C₀)*x^θ at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith [total_kernel,arch_three]) (Real.rpow_nonneg (by linarith) _))

private theorem verified_domain {k : ℕ} (hk : 2≤k) (hk' : k≤223) : |G ((k:ℝ)^4)| ≤ 19*(k:ℝ)^2 := by
  obtain ⟨F,hF,h⟩ := finite_approx hk (le_refl (1/2:ℝ))
  have hH : (5/2+2*((k^2:ℕ):ℝ))≤100000 := by
    have hle := pow_le_pow_left₀ (a:=(k:ℝ)) (by positivity) (by exact_mod_cast hk' : (k:ℝ)≤223) 2
    push_cast; nlinarith
  have hnil : F=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun z hz =>
    ((hF z).mp hz).1.ne (critical_to_100000 z (((hF z).mp hz).2.trans hH)).symm
  rw [hnil] at h
  simpa only [Finset.sum_empty,Complex.zero_re,add_zero,←Real.sqrt_eq_rpow,show (k:ℝ)^4=((k:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)] using h

end RampFiniteProof
open RampFiniteProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let P (x : ℝ) (z : ZetaZerosInTraceStrip (1/2)) := (x:ℂ)*
      ((analyticOrderNatAt riemannZeta z.val : ℂ)*(x:ℂ)^(z.val-1)/(z.val*(z.val-1)))
    (∀ k : ℕ, 2≤k → ∀ θ : ℝ, 1/2≤θ →
      ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
        (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ<z.val.re ∧
          100000 < |z.val.im| ∧ |z.val.im|≤5/2+2*((k^2:ℕ):ℝ)) ∧
        |G ((k:ℝ)^4)+(∑ z ∈ F,P ((k:ℝ)^4) z).re| ≤ 19*((k:ℝ)^4)^θ) ∧
    (∀ k : ℕ, 2≤k → k≤223 → |G ((k:ℝ)^4)| ≤ 19*(k:ℝ)^2) ∧
    (∀ θ : ℝ, 0≤θ → (∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤θ) →
      ∀ x : ℝ, 2≤x → |G x|≤9*x^θ) ∧
    (∀ x : ℝ, 2≤x → |G x|≤9*x^(0.8749570698:ℝ)) := by
  refine ⟨?_,fun k hk hk' => verified_domain hk hk',fun θ hθ hz x hx => explicit_nine hθ hz hx,
    fun x hx => explicit_nine (by norm_num [B] : 0≤B) zero_upper hx⟩
  intro k hk θ hθ
  obtain ⟨F,hF,h⟩ := finite_approx hk hθ
  refine ⟨F,fun z => ?_,h⟩
  rw [hF z]
  constructor
  · rintro ⟨hr,hi⟩; refine ⟨hr,?_,hi⟩
    by_contra! hlow; linarith [critical_to_100000 z hlow]
  · exact fun ⟨hr,_,hi⟩ => ⟨hr,hi⟩

end
