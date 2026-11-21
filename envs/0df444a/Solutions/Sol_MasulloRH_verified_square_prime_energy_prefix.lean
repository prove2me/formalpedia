-- Prove2me | solution 1 for MasulloRH.verified_square_prime_energy_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:41:53.561148+00:00
-- url     : https://prove2.me/submissions/099b46f3-a7a7-4b6c-a224-e1d673c6631b

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
namespace SquarePrefixProof
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

private theorem mid_fourteen (z : Z) : 14 < |z.val.im| := by
  by_contra! hz
  have h6 := mid_low z
  by_cases hr : 0 ≤ z.val.im
  · rw [abs_of_nonneg hr] at hz h6
    exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen z.val z.prop.2.1 z.prop.2.2.1 (by linarith) hz z.prop.1
  rw [abs_of_neg (lt_of_not_ge hr)] at hz h6
  have hn (j : ℕ) : z.val ≠ -j := by
    intro h; have a := congrArg Complex.re h; simp only [Complex.neg_re,Complex.natCast_re] at a
    linarith [z.prop.2.1,j.cast_nonneg (α:=ℝ)]
  have hn1 : z.val ≠ 1 := fun h => by have a := z.prop.2.2.1; simpa [h] using a
  have hf : riemannZeta (1-z.val)=0 := by rw [riemannZeta_one_sub hn hn1,z.prop.1,mul_zero]
  exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen (1-z.val)
    (by simp; linarith [z.prop.2.2.1]) (by simp; linarith [z.prop.2.1]) (by simp; linarith) (by simpa using hz) hf

private theorem small_kernel : (∑' z : Z,‖K 1 z‖) ≤ 9/4 := by
  have ht := weight_tail 5
  have ha (z : Z) : (5/2+2*(5:ℕ):ℝ) < |z.val.im| := by linarith [mid_fourteen z]
  simp only [if_pos (ha _)] at ht
  have hlog := Real.log_le_log (by norm_num : 0<(5:ℝ)) (by norm_num : (5:ℝ)≤2^3)
  rw [Real.log_pow] at hlog
  have hk := (Knorm_sum (x:=1) le_rfl).tsum_le_tsum kernel_weight ((weighted_zero_summability (1/2) (by norm_num)).mul_left 2)
  rw [tsum_mul_left] at hk
  norm_num at ht hlog
  rw [le_div_iff₀ (by norm_num)] at ht
  linarith [Real.log_two_lt_d9]

private theorem finite_height_estimate {x a : ℝ} (hx : 2≤x)
    (ha : ∀ z : Z, z.val.re≤a) (M : ℕ)
    (hcrit : ∀ z : Z, |z.val.im| ≤ 5/2+2*(M:ℝ) → z.val.re ≤ 1/2) :
    |G x| ≤ 9/4*Real.sqrt x + (2*x^a)*((10+Real.log M)/(5/2+2*(M:ℝ)-1))+3 := by
  classical
  let H := 5/2+2*(M:ℝ)
  let V : Set Z := {z | H < |z.val.im|}
  let w := zeroDecayWeight (1/2)
  let F (z : Z) := Real.sqrt x*‖K 1 z‖ + (2*x^a)*V.indicator w z
  have hx0 : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have hX := Real.sqrt_nonneg x
  have hA := Real.rpow_nonneg hx0.le a
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hiw : Summable (V.indicator w) := hw.indicator V
  have hm : Summable F := ((Knorm_sum (x:=1) le_rfl).mul_left _).add (hiw.mul_left _)
  have hpt (z : Z) : ‖P x z‖ ≤ F z := by
    dsimp only [F]
    by_cases hv : z ∈ V
    · rw [Set.indicator_of_mem hv]
      apply (P_point hx1 z (ha z)).trans
      apply (mul_le_mul_of_nonneg_left (kernel_weight z) hA).trans
      calc x^a*(2*w z) = (2*x^a)*w z := by ring
           _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hX (norm_nonneg _))
    · rw [Set.indicator_of_notMem hv,mul_zero,add_zero,Real.sqrt_eq_rpow]
      exact P_point hx1 z (hcrit z (le_of_not_gt hv))
  have hs : ‖∑' z : Z,P x z‖ ≤ 9/4*Real.sqrt x + (2*x^a)*((10+Real.log M)/(H-1)) := by
    calc _ ≤ ∑' z : Z,‖P x z‖ := norm_tsum_le_tsum_norm (P_summable hx1).norm
         _ ≤ ∑' z : Z,F z := (P_summable hx1).norm.tsum_le_tsum hpt hm
         _ = Real.sqrt x*(∑' z : Z,‖K 1 z‖)+(2*x^a)*(∑' z : Z,V.indicator w z) := by
           unfold F; rw [Summable.tsum_add ((Knorm_sum (x:=1) le_rfl).mul_left _) (hiw.mul_left _),tsum_mul_left,tsum_mul_left]
         _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_left small_kernel hX).trans_eq (mul_comm ..))
                    (mul_le_mul_of_nonneg_left (weight_tail M) (by positivity))
  have ht : |x*tail x|≤3 := by
    have h := tail_bound hx
    rw [Real.norm_eq_abs] at h
    rw [abs_mul,abs_of_pos hx0]
    apply (mul_le_mul_of_nonneg_left h hx0.le).trans
    calc x*(C₀/x) = C₀ := by field_simp
         _ ≤ 3 := arch_three
  have he := congrArg Complex.re (G_series hx)
  simp only [Complex.ofReal_re,Complex.add_re,Complex.neg_re] at he
  rw [he]
  apply (abs_add_le ..).trans
  rw [abs_neg]
  exact add_le_add ((Complex.abs_re_le_norm _).trans hs) ht

private theorem at_certified_height {x a : ℝ} (hx : 2≤x) (ha : ∀ z : Z,z.val.re≤a) :
    |G x| ≤ 9/4*Real.sqrt x + x^a/2300 +3 := by
  have h := finite_height_estimate hx ha 49998 (fun z hz => (critical_to_100000 z (by norm_num at hz; linarith)).le)
  have hlog := Real.log_le_log (by norm_num : 0<(49998:ℝ)) (by norm_num : (49998:ℝ)≤2^16)
  rw [Real.log_pow] at hlog
  have hv : (10+Real.log 49998)/(5/2+2*(49998:ℕ)-1:ℝ) ≤ 1/4600 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; norm_num at hlog ⊢; linarith [Real.log_two_lt_d9]
  have hu := mul_le_mul_of_nonneg_left hv (show 0≤2*x^a by positivity)
  norm_num only [Nat.cast_ofNat] at h hu
  exact h.trans (by linarith)

private def R (x : ℝ) := (1+Real.log x)⁻¹
private def w (x : ℝ) := 1/(x*(1+Real.log x)^2)
private def sample (x : ℝ) := (G (x^2))^2/(x^3*(1+Real.log x)^2)

private theorem weight_tel {x : ℝ} (hx : 1 ≤ x) : w (x+1) ≤ R x-R (x+1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hlog := Real.log_nonneg hx
  have hlog' := Real.log_le_log hx0 (show x ≤ x+1 by linarith)
  have ha : 0 < 1+Real.log x := by linarith
  have hb : 0 < 1+Real.log (x+1) := by linarith
  have hi := Real.log_le_sub_one_of_pos (div_pos hx0 hx1)
  rw [Real.log_div hx0.ne' hx1.ne'] at hi
  have hgap : 1/(x+1) ≤ Real.log (x+1)-Real.log x := by
    have he : x/(x+1)-1 = -(1/(x+1)) := by field_simp; ring
    rw [he] at hi; linarith
  have he : R x-R (x+1) = (Real.log (x+1)-Real.log x)/((1+Real.log x)*(1+Real.log (x+1))) := by
    unfold R; field_simp; ring
  rw [he]
  calc w (x+1) = (1/(x+1))/(1+Real.log (x+1))^2 := by unfold w; rw [div_div]
       _ ≤ (1/(x+1))/((1+Real.log x)*(1+Real.log (x+1))) := by
         apply div_le_div_of_nonneg_left (by positivity) (mul_pos ha hb)
         nlinarith [mul_le_mul_of_nonneg_right (by linarith : 1+Real.log x ≤ 1+Real.log (x+1)) hb.le]
       _ ≤ _ := div_le_div_of_nonneg_right hgap (mul_nonneg ha.le hb.le)

private theorem weight_part (N : ℕ) : (∑ n ∈ range N,w ((n:ℝ)+4)) ≤ 1/2 := by
  have h (M : ℕ) : (∑ n ∈ range M,w ((n:ℝ)+4)) ≤ R 3-R ((M:ℝ)+3) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ,Nat.cast_succ]
      have hd := weight_tel (x:=(M:ℝ)+3) (by linarith [M.cast_nonneg (α:=ℝ)])
      rw [show (M:ℝ)+3+1=M+4 by ring] at hd
      rw [show (M:ℝ)+1+3=M+4 by ring]
      linarith
  have h0 : 0 ≤ R ((N:ℝ)+3) := by
    unfold R; have := Real.log_nonneg (by linarith [N.cast_nonneg (α:=ℝ)] : 1≤(N:ℝ)+3); positivity
  have hx : 1≤Real.log 3 := (Real.le_log_iff_exp_le (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have h1 : R 3 ≤ 1/2 := by unfold R; rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith [h N]
private def e (r : ℝ) := Real.sqrt r/(1+Real.log r)^2
private def e₁ (r : ℝ) := r/(1+Real.log r)^2

private theorem sample_major {r : ℝ} (hr : 4≤r) (q : ℝ) (hq : 0≤q)
    (h : |G (r^2)| ≤ 3*r+q) :
    sample r ≤ 18*w r + 2*q^2/(r^3*(1+Real.log r)^2) := by
  have hr0 : 0<r := by linarith
  have hl := Real.log_nonneg (show 1≤r by linarith)
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  have hs' : (G (r^2))^2 ≤ 18*r^2+2*q^2 := by nlinarith [sq_abs (G (r^2)),sq_nonneg (3*r-q)]
  change (G (r^2))^2/(r^3*(1+Real.log r)^2) ≤ _
  apply (div_le_div_of_nonneg_right hs' (by positivity)).trans_eq
  unfold w
  field_simp
  <;> ring

private theorem general_square_bound {r a : ℝ} (hr : 4≤r) (ha : ∀ z : Z,z.val.re≤a) :
    |G (r^2)| ≤ 3*r+(r^2)^a/2300 := by
  have hr0 : 0≤r := by linarith
  have h := at_certified_height (x:=r^2) (by nlinarith) ha
  rw [Real.sqrt_sq hr0] at h
  linarith

private theorem major_seven_eighths {r : ℝ} (hr : 4≤r) :
    sample r ≤ 18*w r + (2/2300^2)*e r := by
  have hr0 : 0<r := by linarith
  have hl := Real.log_nonneg (show 1≤r by linarith)
  have hb : (r^2)^B ≤ r^(7/4:ℝ) := by
    calc _ ≤ (r^2)^(7/8:ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by norm_num [B])
         _ = _ := by rw [←Real.rpow_natCast_mul hr0.le]; norm_num
  have h := (general_square_bound hr zero_upper).trans (add_le_add_right (div_le_div_of_nonneg_right hb (by norm_num : (0:ℝ)≤2300)) _)
  apply (sample_major hr (r^(7/4:ℝ)/2300) (by positivity) h).trans_eq
  have he : (r^(7/4:ℝ))^2 = r^3*Real.sqrt r := by
    rw [←Real.rpow_mul_natCast hr0.le,Real.sqrt_eq_rpow,←Real.rpow_natCast r 3,←Real.rpow_add hr0]
    norm_num
  unfold e
  rw [div_pow,he]
  field_simp
  <;> ring

private theorem major_one {r : ℝ} (hr : 4≤r) :
    sample r ≤ 18*w r + (2/2300^2)*e₁ r := by
  have hr0 : 0<r := by linarith
  have hl := Real.log_nonneg (show 1≤r by linarith)
  have h := general_square_bound (a:=1) hr (fun z => z.prop.2.2.1.le)
  rw [Real.rpow_one] at h
  apply (sample_major hr (r^2/2300) (by positivity) h).trans_eq
  unfold e₁
  field_simp
  <;> ring

private theorem cut_sum (N L : ℕ) {c : ℝ} (hc : 0≤c) :
    (∑ n ∈ range N, if n<L then c else 0) ≤ L*c := by
  classical
  rw [←Finset.sum_filter]
  have hs : (range N).filter (fun n => n<L) ⊆ range L := by
    intro i hi; exact mem_range.mpr (mem_filter.mp hi).2
  calc _ ≤ ∑ _i ∈ range L,c := Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact hc)
       _ = _ := by simp

private theorem lower_log {r : ℝ} {m : ℕ} (h : (2:ℝ)^m≤r) :
    (m:ℝ)*Real.log 2 ≤ Real.log r := by
  simpa only [Real.log_pow] using Real.log_le_log (by positivity : 0<(2:ℝ)^m) h

private theorem error_point {n : ℕ} (hn : n<10000000) :
    e ((n:ℝ)+4) ≤ (if n<4096 then 64 else 0) +
      (if n<1048576 then 1024/81 else 0) + 3163/196 := by
  let r := (n:ℝ)+4
  have hr : 4≤r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
  have hl := Real.log_nonneg (show 1≤r by linarith)
  have he {q d : ℝ} (hd : 0<d) (hd' : d≤(1+Real.log r)^2) (hq : Real.sqrt r≤q) : e r ≤ q/d :=
    (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hd hd').trans (div_le_div_of_nonneg_right hq hd.le)
  change e r ≤ _
  by_cases h : r≤4096
  · have hn' : n<4096 := by dsimp [r] at h; exact_mod_cast (by linarith : (n:ℝ)<4096)
    rw [if_pos hn',if_pos (show n<1048576 by omega)]
    have H := he (d:=1) (by norm_num) (by nlinarith [sq_nonneg (Real.log r)]) (q:=64) ((Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩)
    linarith
  have hlog₁ := lower_log (m:=12) (r:=r) (by norm_num; linarith)
  norm_num at hlog₁
  by_cases h' : r≤1048576
  · have hn' : n<1048576 := by dsimp [r] at h'; exact_mod_cast (by linarith : (n:ℝ)<1048576)
    rw [if_pos hn']
    have h8 : 8≤Real.log r := by linarith [Real.log_two_gt_d9]
    have H := he (d:=81) (by norm_num) (by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤9) (show 9≤1+Real.log r by linarith)]) (q:=1024) ((Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩)
    split_ifs <;> linarith
  have hlog₂ := lower_log (m:=20) (r:=r) (by norm_num; linarith)
  norm_num at hlog₂
  have h13 : 13 ≤ Real.log r := by linarith [Real.log_two_gt_d9]
  have hr' : r≤10000004 := by
    dsimp [r]
    have hnR : (n:ℝ)<10000000 := by exact_mod_cast hn
    linarith
  have H := he (d:=196) (by norm_num) (by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤14) (show 14≤1+Real.log r by linarith)]) (q:=3163) ((Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩)
  split_ifs <;> linarith

private theorem err_one_point {n : ℕ} (hn : n<100000) :
    e₁ ((n:ℝ)+4) ≤ (if n<4096 then 4096 else 0) + 100004/81 := by
  let r := (n:ℝ)+4
  have hr : 4≤r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
  have hr0 : 0≤r := by linarith
  have hl := Real.log_nonneg (show 1≤r by linarith)
  change r/(1+Real.log r)^2 ≤ _
  have he {d : ℝ} (hd : 0<d) (hd' : d≤(1+Real.log r)^2) : r/(1+Real.log r)^2 ≤ r/d :=
    div_le_div_of_nonneg_left hr0 hd hd'
  by_cases h : r≤4096
  · have hn' : n<4096 := by dsimp [r] at h; exact_mod_cast (by linarith : (n:ℝ)<4096)
    rw [if_pos hn']
    have H := he (d:=1) (by norm_num) (by nlinarith [sq_nonneg (Real.log r)])
    linarith
  have hlog := lower_log (m:=12) (r:=r) (by norm_num; linarith)
  norm_num at hlog
  have h8 : 8≤Real.log r := by linarith [Real.log_two_gt_d9]
  have H := he (d:=81) (by norm_num) (by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤9) (show 9≤1+Real.log r by linarith)])
  have hnR : (n:ℝ)<100000 := by exact_mod_cast hn
  have hr' : r≤100004 := by dsimp [r]; linarith
  split_ifs <;> linarith

private theorem combine_sum (f : ℝ → ℝ) (N : ℕ) (C : ℝ)
    (h : ∀ {r : ℝ}, 4≤r → sample r ≤ 18*w r + (2/2300^2)*f r)
    (hC : (∑ n ∈ range N,f ((n:ℝ)+4)) ≤ C) :
    (∑ n ∈ range N,sample ((n:ℝ)+4)) ≤ 9+(2/2300^2)*C := by
  calc _ ≤ ∑ n ∈ range N,(18*w ((n:ℝ)+4) + (2/2300^2)*f ((n:ℝ)+4)) :=
           sum_le_sum fun n _ => h (by linarith [n.cast_nonneg (α:=ℝ)])
       _ = 18*(∑ n ∈ range N,w ((n:ℝ)+4))+(2/2300^2)*(∑ n ∈ range N,f ((n:ℝ)+4)) := by
         rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
       _ ≤ _ := by linarith [weight_part N]

private theorem prefix_ten_million {N : ℕ} (hN : N≤10000000) :
    (∑ n ∈ range N,sample ((n:ℝ)+4)) ≤ 76 := by
  have hE : (∑ n ∈ range N,e ((n:ℝ)+4)) ≤ 4096*64 + 1048576*(1024/81) + 10000000*(3163/196) := by
    calc _ ≤ ∑ n ∈ range N,((if n<4096 then (64:ℝ) else 0)+(if n<1048576 then 1024/81 else 0)+3163/196) :=
             sum_le_sum fun n hn => error_point ((mem_range.mp hn).trans_le hN)
         _ ≤ _ := by
           rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,card_range,nsmul_eq_mul]
           have hNR : (N:ℝ) ≤ 10000000 := by exact_mod_cast hN
           exact add_le_add (add_le_add (cut_sum N 4096 (c:=64) (by norm_num)) (cut_sum N 1048576 (c:=1024/81) (by norm_num))) (mul_le_mul_of_nonneg_right hNR (by norm_num))
  exact (combine_sum e N _ major_seven_eighths hE).trans (by norm_num)

private theorem prefix_hundred_thousand {N : ℕ} (hN : N≤100000) :
    (∑ n ∈ range N,sample ((n:ℝ)+4)) ≤ 63 := by
  have hE : (∑ n ∈ range N,e₁ ((n:ℝ)+4)) ≤ 4096*4096+100000*(100004/81) := by
    calc _ ≤ ∑ n ∈ range N,((if n<4096 then (4096:ℝ) else 0)+100004/81) :=
             sum_le_sum fun n hn => err_one_point ((mem_range.mp hn).trans_le hN)
         _ ≤ _ := by
           rw [Finset.sum_add_distrib,Finset.sum_const,card_range,nsmul_eq_mul]
           have hNR : (N:ℝ) ≤ 100000 := by exact_mod_cast hN
           exact add_le_add (cut_sum N 4096 (c:=4096) (by norm_num)) (mul_le_mul_of_nonneg_right hNR (by norm_num))
  exact (combine_sum e₁ N _ major_one hE).trans (by norm_num)

private theorem height_to_prefix (M N : ℕ)
    (hcrit : ∀ z : Z, |z.val.im| ≤ 5/2+2*(M:ℝ) → z.val.re ≤ 1/2)
    (hM : 2*(10+Real.log M)*((N:ℝ)+3) ≤ 5/2+2*(M:ℝ)-1) (hM0 : 1≤M) :
    (∑ n ∈ range N,sample ((n:ℝ)+4)) ≤ 8 := by
  have hmR : 1 ≤ (M:ℝ) := by exact_mod_cast hM0
  let H := 5/2+2*(M:ℝ)-1
  let L := 10+Real.log M
  have hH : 0<H := by dsimp [H]; linarith
  have hL : 0≤L := by dsimp [L]; linarith [Real.log_nonneg hmR]
  have hpt (n : ℕ) (hn : n∈range N) : sample ((n:ℝ)+4) ≤ 16*w ((n:ℝ)+4) := by
    let r := (n:ℝ)+4
    have hr : 4≤r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
    have hsmall : r≤(N:ℝ)+3 := by
      have ht : ((n+1:ℕ):ℝ)≤N := by exact_mod_cast mem_range.mp hn
      push_cast at ht; dsimp [r]; linarith
    have hr0 : 0<r := by linarith
    have hl := Real.log_nonneg (show 1≤r by linarith)
    have hb := finite_height_estimate (x:=r^2) (a:=1) (by nlinarith) (fun z => z.prop.2.2.1.le) M hcrit
    rw [Real.sqrt_sq hr0.le,Real.rpow_one] at hb
    have hq : (2*r^2)*(L/H) ≤ r := by
      rw [←mul_div_assoc,div_le_iff₀ hH]
      have he : 2*L*r ≤ H := (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans hM
      nlinarith [mul_le_mul_of_nonneg_right he hr0.le]
    have hgb : |G (r^2)|≤4*r := by change |G (r^2)| ≤ 9/4*r + (2*r^2)*(L/H)+3 at hb; linarith
    have hs := mul_self_le_mul_self (abs_nonneg _) hgb
    have h2 : (G (r^2))^2 ≤ 16*r^2 := by nlinarith [sq_abs (G (r^2))]
    change (G (r^2))^2/(r^3*(1+Real.log r)^2) ≤ 16*(1/(r*(1+Real.log r)^2))
    apply (div_le_div_of_nonneg_right h2 (by positivity)).trans_eq
    field_simp
  calc _ ≤ ∑ n ∈ range N,16*w ((n:ℝ)+4) := sum_le_sum hpt
       _ = 16*(∑ n ∈ range N,w ((n:ℝ)+4)) := (Finset.mul_sum ..).symm
       _ ≤ _ := by linarith [weight_part N]

end SquarePrefixProof
open SquarePrefixProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (∀ N ≤ 100000, E N ≤ 63) ∧ (∀ N ≤ 10000000, E N ≤ 76) ∧
      ∀ (M N : ℕ), 1≤M →
        (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ 5/2+2*(M:ℝ) → z.val.re ≤ 1/2) →
        2*(10+Real.log M)*((N:ℝ)+3) ≤ 5/2+2*(M:ℝ)-1 → E N ≤ 8 := by
  dsimp only
  exact ⟨fun _ h => prefix_hundred_thousand h,fun _ h => prefix_ten_million h,
    fun M N hM hc h => height_to_prefix M N hc h hM⟩
