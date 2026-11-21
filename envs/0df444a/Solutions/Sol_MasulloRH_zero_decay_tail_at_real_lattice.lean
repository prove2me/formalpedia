-- Prove2me | solution 1 for MasulloRH.zero_decay_tail_at_real_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:09:51.331398+00:00
-- url     : https://prove2.me/submissions/6c2cb16f-4b5c-43dc-a78d-57d4ee97a4d5

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Set Filter Topology MeasureTheory
open MasulloRH

private theorem arch_lattice (n : ℕ) :
    regularizedArch ((5/2+2*(n:ℝ):ℝ):ℂ) =
      ((-(∑ k ∈ Finset.range n, 1/(5/2+2*(k:ℝ))):ℝ):ℂ) := by
  let a (k : ℕ) := (5/2:ℝ)+2*k
  let g (k : ℕ) (t : ℝ) := t^(-(a k+1))
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hi (k : ℕ) : IntegrableOn (g k) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith [ha k]) zero_lt_one
  have he (k : ℕ) : ∫ t in Ioi (1:ℝ), g k t = 1/a k := by
    rw [show (∫ t in Ioi (1:ℝ),g k t) = _ from integral_Ioi_rpow_of_lt
      (show -(a k+1) < -1 by linarith [ha k]) zero_lt_one]
    rw [Real.one_rpow,show -(a k+1)+1 = -a k by ring]
    ring
  have hgeom (t : ℝ) (ht : 1 < t) (m : ℕ) :
      (t^(1/2-a m)-t^(-2:ℝ))*(Real.sqrt t/(t^2-1)) =
        -∑ k ∈ Finset.range m,g k t := by
    have ht0 : 0 < t := by linarith
    induction m with
    | zero =>
      rw [show 1/2-a 0 = (-2:ℝ) by norm_num [a]]
      simp
    | succ m ih =>
      rw [Finset.sum_range_succ,neg_add,←ih]
      have hshift : t^(1/2-a (m+1)) = t^(1/2-a m)/t^2 := by
        rw [show 1/2-a (m+1)= (1/2-a m)-2 by dsimp [a]; push_cast; ring,
            Real.rpow_sub ht0,Real.rpow_two]
      have hprod : t^(1/2-a m)*Real.sqrt t /t^2 = g m t := by
        rw [Real.sqrt_eq_rpow,←Real.rpow_add ht0,←Real.rpow_two,←Real.rpow_sub ht0]
        unfold g
        congr 1
        ring
      rw [hshift,←hprod]
      have hd : t^2-1 ≠ 0 := by nlinarith [mul_self_lt_mul_self zero_le_one ht]
      field_simp
      ring
  unfold regularizedArch
  calc _ = ∫ t in Ioi (1:ℝ), ((-∑ k ∈ Finset.range n,g k t:ℝ):ℂ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
          have ht0 : 0 ≤ t := le_of_lt (zero_lt_one.trans ht)
          change (((t:ℂ)^(1/2-(a n:ℂ))-(t:ℂ)^(-2:ℂ))*
            ((Real.sqrt t/(t^2-1):ℝ):ℂ)) = _
          rw [show (1/2-(a n:ℂ):ℂ) = ((1/2-a n:ℝ):ℂ) by push_cast; ring,
              show (-2:ℂ) = ((-2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow ht0,←Complex.ofReal_cpow ht0,
              ←Complex.ofReal_sub,←Complex.ofReal_mul,hgeom t ht n]
       _ = _ := by
          rw [integral_complex_ofReal, integral_neg,integral_finsetSum]
          · simp only [he,a]
          · exact fun i _ => hi i

private theorem height_majorant {R : ℝ} {s : ℂ} (hR : ‖s‖ ≤ R)
    (hs : (3/2:ℝ) ≤ s.re) (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) s ρ‖ ≤
      (2*(2*R+3)*(R+5/2)) * zeroDecayWeight (1/2) ρ := by
  let z : ℂ := ρ
  let b : ℂ := 5/2
  have hβ : z.re < 1 := ρ.property.2.2.1
  have hb : b.re = 5/2 := by norm_num [b,Complex.div_re]
  have hbim : b.im = 0 := by norm_num [b,Complex.div_im]
  have hbn : ‖b‖ = 5/2 := by norm_num [b,norm_div]
  have hA : 1/2 ≤ ‖s-z‖ := by
    have h := Complex.re_le_norm (s-z)
    rw [Complex.sub_re] at h
    linarith
  have hB : 1 ≤ ‖b-z‖ := by
    have h := Complex.re_le_norm (b-z)
    rw [Complex.sub_re,hb] at h
    linarith
  have ha0 : 0 < ‖s-z‖ := by linarith
  have hb0 : 0 < ‖b-z‖ := by linarith
  have hR0 := (norm_nonneg s).trans hR
  have himA : |z.im| ≤ R+‖s-z‖ := by
    calc |z.im| = |s.im - (s-z).im| := by rw [Complex.sub_im]; congr 1; ring
         _ ≤ |s.im|+|(s-z).im| := abs_sub _ _
         _ ≤ _ := add_le_add ((Complex.abs_im_le_norm s).trans hR) (Complex.abs_im_le_norm _)
  have himB : |z.im| ≤ ‖b-z‖ := by
    simpa [Complex.sub_im,hbim] using Complex.abs_im_le_norm (b-z)
  have h1 : 1+|z.im| ≤ (2*R+3)*‖s-z‖ := by
    nlinarith [mul_nonneg (show 0 ≤ R+1 by linarith) (show 0 ≤ ‖s-z‖ - 1/2 by linarith)]
  have h2 : 1+|z.im| ≤ 2*‖b-z‖ := by linarith
  have hw : 1+z.im^2 ≤ (2*(2*R+3))*(‖s-z‖*‖b-z‖) := by
    have h := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [sq_abs z.im, abs_nonneg z.im]
  have hdiff : 1/(s-z) - 1/(b-z) = (b-s)/((s-z)*(b-z)) := by
    field_simp [norm_pos_iff.mp ha0,norm_pos_iff.mp hb0]
    ring
  have hnum : ‖b-s‖ ≤ R+5/2 := by linarith [norm_sub_le b s]
  have hdiv : ‖1/(s-z) - 1/(b-z)‖ ≤ (2*(2*R+3)*(R+5/2))/(1+z.im^2) := by
    rw [hdiff,norm_div,norm_mul]
    apply (div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)).mpr
    calc ‖b-s‖ * (1+z.im^2) ≤ (R+5/2)*(1+z.im^2) := by gcongr
         _ ≤ (R+5/2)*((2*(2*R+3))*(‖s-z‖*‖b-z‖)) := by gcongr
         _ = _ := by ring
  unfold zeroResolventTerm zeroDecayWeight
  rw [norm_mul,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg (analyticOrderNatAt riemannZeta z))).trans_eq
  ring


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


private noncomputable def density (x : ℝ) (z : ZetaZerosInTraceStrip (1/2)) : ℝ :=
  (analyticOrderNatAt riemannZeta z.val:ℝ) *
    ((x-z.val.re)/((x-z.val.re)^2+z.val.im^2))

private theorem density_nonneg {x : ℝ} (hx : 5/2 ≤ x) (z : ZetaZerosInTraceStrip (1/2)) :
    0 ≤ density x z := by
  unfold density
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith [z.property.2.2.1]) (by positivity))

private theorem density_summable {x : ℝ} (hx : 5/2 ≤ x) : Summable (density x) := by
  have h := (weighted_zero_summability (1/2) (by norm_num)).mul_left x
  apply h.of_nonneg_of_le (density_nonneg hx)
  intro z
  let d := x-z.val.re
  have hd : 1 ≤ d := by dsimp [d]; linarith [z.property.2.2.1]
  have hdx : d ≤ x := by dsimp [d]; linarith [z.property.2.1]
  have hd' : 1+z.val.im^2 ≤ d^2+z.val.im^2 := by nlinarith [sq_nonneg (d-1)]
  have hfrac : d/(d^2+z.val.im^2) ≤ x/(1+z.val.im^2) := by
    exact div_le_div₀ (by linarith) hdx (by positivity) hd'
  unfold density zeroDecayWeight
  calc _ ≤ (analyticOrderNatAt riemannZeta z.val:ℝ)*(x/(1+z.val.im^2)) :=
         mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
       _ = _ := by ring

private theorem resolvent_re (x : ℝ) (z : ZetaZerosInTraceStrip (1/2)) :
    (zeroResolventTerm (1/2) (x:ℂ) z).re = density x z-density (5/2) z := by
  unfold zeroResolventTerm density
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  norm_num [Complex.div_ofNat_re,Complex.div_ofNat_im,pow_two]
  ring

private theorem density_difference {x : ℝ} (hx : 5/2 ≤ x) :
    (∑' z,density x z) - (∑' z,density (5/2) z) =
      (zetaLogDeriv (x:ℂ)).re -
        (zetaLogDeriv (5/2)+regularizedArch (x:ℂ)-regularizedPolar (x:ℂ)).re := by
  let f := zeroResolventTerm (1/2) (x:ℂ)
  let D := 2*(2*‖(x:ℂ)‖+3)*(‖(x:ℂ)‖+5/2)
  have hmajor (z) : ‖f z‖ ≤ D*zeroDecayWeight (1/2) z :=
    height_majorant le_rfl (by change (3/2:ℝ) ≤ x; linarith) z
  have hs : Summable f := ((weighted_zero_summability (1/2) (by norm_num)).mul_left D).of_norm_bounded hmajor
  rw [←(density_summable hx).tsum_sub (density_summable (x:=5/2) le_rfl),
    ←regularized_initial_identity_full_strip (x:ℂ) (by change (3/2:ℝ) < x; linarith)]
  change _ = ((_+(∑' z,f z)).re-_)
  rw [Complex.add_re,add_sub_cancel_left,Complex.re_tsum hs]
  exact tsum_congr fun z => (resolvent_re x z).symm

private theorem density_base_le (z : ZetaZerosInTraceStrip (1/2)) :
    density (5/2) z ≤ 8*(density 3 z-density (5/2) z) := by
  let a := 3-z.val.re
  let b := 5/2-z.val.re
  let Y := z.val.im^2
  have h6 : 6 < |z.val.im| := lt_of_not_ge fun h =>
    ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1
  have hY : 36 ≤ Y := by dsimp [Y]; nlinarith [sq_abs z.val.im,sq_nonneg (|z.val.im|-6)]
  have ha : 0 ≤ a := by dsimp [a]; linarith [z.prop.2.2.1]
  have hb : 0 ≤ b := by dsimp [b]; linarith [z.prop.2.2.1]
  have ha3 : a ≤ 3 := by dsimp [a]; linarith [z.prop.2.1]
  have hb' : b ≤ 5/2 := by dsimp [b]; linarith [z.prop.2.1]
  have hab : a*b ≤ 15/2 := by nlinarith [mul_le_mul ha3 hb' hb (by norm_num : (0:ℝ)≤3)]
  have ha2 : a^2 ≤ 9 := by nlinarith [mul_le_mul ha3 ha3 ha (by norm_num : (0:ℝ)≤3)]
  have hA : 0 < a^2+Y := by nlinarith [sq_nonneg a]
  have hB : 0 < b^2+Y := by nlinarith [sq_nonneg b]
  have hc : b*(a^2+Y) ≤ 4*(Y-a*b) := by
    have he := mul_le_mul hb' (add_le_add_left ha2 Y) hA.le (by norm_num : (0:ℝ)≤5/2)
    linarith
  have hk : b/(b^2+Y) ≤ 8*(a/(a^2+Y)-b/(b^2+Y)) := by
    calc _ = (b*(a^2+Y))/((a^2+Y)*(b^2+Y)) := by field_simp
         _ ≤ (4*(Y-a*b))/((a^2+Y)*(b^2+Y)) := div_le_div_of_nonneg_right hc (mul_pos hA hB).le
         _ = _ := by field_simp; dsimp [a,b]; ring
  let m := (analyticOrderNatAt riemannZeta z.val:ℝ)
  change m*(b/(b^2+Y)) ≤ 8*(m*(a/(a^2+Y))-m*(b/(b^2+Y)))
  calc _ ≤ m*(8*(a/(a^2+Y)-b/(b^2+Y))) := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
       _ = _ := by ring

private theorem high_ordinate_comparison {x : ℝ} (hx : 5/2 ≤ x)
    (z : ZetaZerosInTraceStrip (1/2)) (hz : x < |z.val.im|) :
    zeroDecayWeight (1/2) z ≤ (2/(x-1))*density x z := by
  let d := x-z.val.re
  let Y := z.val.im^2
  have hd : x-1 ≤ d := by dsimp [d]; linarith [z.prop.2.2.1]
  have hdx : d ≤ x := by dsimp [d]; linarith [z.prop.2.1]
  have hd0 : 0 ≤ d := by linarith
  have hxy : x^2 ≤ Y := by dsimp [Y]; nlinarith [sq_abs z.val.im,mul_self_le_mul_self (by linarith : 0≤x) hz.le]
  have hd2 : d^2 ≤ Y := (sq_le_sq' (by linarith) hdx).trans hxy
  have hY : 0 < Y := by dsimp [Y]; exact sq_pos_of_ne_zero (fun h => by simp [h] at hz; linarith)
  have ha : 0 < d^2+Y := by positivity
  have hb : 0 < x-1 := by linarith
  have hcmp : 1/(1+Y) ≤ (2/(x-1))*(d/(d^2+Y)) := by
    calc _ ≤ 2/(d^2+Y) := (div_le_div_iff₀ (by positivity) ha).mpr (by linarith)
         _ = (2/(x-1))*((x-1)/(d^2+Y)) := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hd ha.le) (by positivity)
  let m := (analyticOrderNatAt riemannZeta z.val:ℝ)
  change m/(1+Y) ≤ (2/(x-1))*(m*(d/(d^2+Y)))
  calc _ = m*(1/(1+Y)) := by ring
       _ ≤ m*((2/(x-1))*(d/(d^2+Y))) := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg _)
       _ = _ := by ring

private theorem polar_nonpos {x : ℝ} (hx : 5/2 ≤ x) : (regularizedPolar (x:ℂ)).re ≤ 0 := by
  have he : regularizedPolar (x:ℂ) =
      (((1/(x-1)-1/(5/2-1))+(1/x-1/(5/2)):ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.ofReal_re]
  apply add_nonpos <;> apply sub_nonpos.mpr
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · exact one_div_le_one_div_of_le (by norm_num) hx

private theorem raw_lattice_tail (n : ℕ) :
    let H : ℝ := 5/2+2*n
    (∑' z : ZetaZerosInTraceStrip (1/2),
      if H < |z.val.im| then zeroDecayWeight (1/2) z else 0) ≤
    2/(H-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + ∑ k ∈ Finset.range n,1/(5/2+2*(k:ℝ))) := by
  classical
  dsimp only
  let H : ℝ := 5/2+2*n
  have hH : 5/2 ≤ H := by dsimp [H]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  let E : Set (ZetaZerosInTraceStrip (1/2)) := {z | H < |z.val.im|}
  have hX : 0 ≤ 2/(H-1) := div_nonneg (by norm_num) (by linarith)
  have hd : (∑' z,E.indicator (zeroDecayWeight (1/2)) z) ≤
      (2/(H-1))*(∑' z,density H z) := by
    rw [←tsum_mul_left]
    apply ((weighted_zero_summability (1/2) (by norm_num)).indicator E).tsum_le_tsum _
      ((density_summable hH).mul_left (2/(H-1)))
    intro z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]; exact high_ordinate_comparison hH z hz
    · rw [Set.indicator_of_notMem hz]; exact mul_nonneg hX (density_nonneg hH z)
  have hb := (density_summable (x:=5/2) le_rfl).tsum_le_tsum density_base_le
    (((density_summable (x:=3) (by norm_num)).sub (density_summable (x:=5/2) le_rfl)).mul_left 8)
  rw [tsum_mul_left,(density_summable (x:=3) (by norm_num)).tsum_sub
    (density_summable (x:=5/2) le_rfl),density_difference (x:=3) (by norm_num)] at hb
  have hdif := density_difference hH
  have harch : (regularizedArch (H:ℂ)).re = -(∑ k ∈ Finset.range n,1/(5/2+2*(k:ℝ))) := by
    rw [arch_lattice]; rfl
  rw [Complex.sub_re,Complex.add_re,harch] at hdif
  have hz : (zetaLogDeriv (H:ℂ)).re ≤ 0 := by
    have hs := mangoldt_series_hasSum (x:=H) (by linarith)
    have hn : 0 ≤ -(zetaLogDeriv (H:ℂ)).re := by
      rw [←hs.tsum_eq]
      exact tsum_nonneg fun k => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg k.cast_nonneg _)
    linarith
  change (∑' z,E.indicator (zeroDecayWeight (1/2)) z) ≤ _
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ hX
  push_cast at hb
  linarith only [hb,hdif,hz,polar_nonpos hH]

theorem solution (n : ℕ) :
    let H : ℝ := 5/2+2*n
    (∑' z : ZetaZerosInTraceStrip (1/2),
      if H < |z.val.im| then zeroDecayWeight (1/2) z else 0) ≤
    2/(H-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2) := by
  dsimp only
  apply (raw_lattice_tail n).trans
  apply mul_le_mul_of_nonneg_left _ (by have hn := n.cast_nonneg (α:=ℝ); apply div_nonneg (by norm_num); linarith)
  apply add_le_add_right
  calc (∑ k ∈ Finset.range n,1/(5/2+2*(k:ℝ))) ≤ (harmonic n:ℝ)/2 := by
          rw [harmonic]
          push_cast
          rw [Finset.sum_div]
          apply Finset.sum_le_sum
          intro k _
          rw [inv_eq_one_div,div_div]
          apply one_div_le_one_div_of_le (by positivity)
          linarith
       _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log n) (by norm_num)

