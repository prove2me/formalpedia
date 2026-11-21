-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:30:24.819565+00:00
-- url     : https://prove2.me/submissions/cf909337-c3bd-48bc-b513-79289b52eacf

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_prime_ramp_log_energy
import Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation
import Theorems.Thm_MasulloRH_prime_ramp_chord_and_fourth_power_bound
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib
open Filter Finset Set Topology MeasureTheory ArithmeticFunction
noncomputable section
open MasulloRH
namespace RampSampleProof
private def G (x : ℝ) : ℝ := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)
private theorem small_G {x : ℝ} (hx : 1≤x) (h2 : x<2) : |G x|≤6 := by
  have hfl : ⌊x⌋₊=1 := Nat.floor_eq_iff (by linarith : 0≤x) |>.mpr ⟨by simpa,by norm_num; exact h2⟩
  have hG : G x = -x*(Real.log x-1-Real.eulerMascheroniConstant) := by simp [G,hfl,Finset.sum_range_succ]
  rw [hG,abs_mul,abs_neg,abs_of_nonneg (by linarith : 0≤x)]
  have hl := Real.log_nonneg hx
  have hl' := Real.log_le_log (by linarith : 0<x) h2.le
  have hcoef : |Real.log x-1-Real.eulerMascheroniConstant|≤3 := abs_le.mpr ⟨by linarith [Real.eulerMascheroniConstant_lt_two_thirds],by linarith [Real.log_two_lt_d9,Real.one_half_lt_eulerMascheroniConstant]⟩
  linarith [mul_le_mul_of_nonneg_left hcoef (by linarith : 0≤x)]

private theorem G_linear {x : ℝ} (hx : 2 ≤ x) : |G x| ≤ 9*x := by
  have h := finite_ordinate_prime_ramp_approximation.2.2.2 x hx
  change |G x| ≤ 9*x^(0.8749570698:ℝ) at h
  have he := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) (by norm_num : (0.8749570698:ℝ) ≤ 1)
  rw [Real.rpow_one] at he; linarith

private theorem chord {a b y : ℝ} (ha : 0 < a) (hab : a < b) (hay : a ≤ y) (hyb : y ≤ b) :
    (b-a)*G y ≤ (b-y)*G a+(y-a)*G b+(y-a)*(b-y)*(b-a)/y := by
  let t := (y-a)/(b-a)
  have hba : 0 < b-a := by linarith
  have h0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hay) hba.le
  have h1 : t ≤ 1 := (div_le_one hba).mpr (by linarith)
  have h := prime_ramp_chord_and_fourth_power_bound.1 a b t ha hab.le h0 h1
  have he : (1-t)*a+t*b=y := by dsimp [t]; field_simp; ring
  change G ((1-t)*a+t*b) ≤ (1-t)*G a+t*G b+t*(1-t)*(b-a)^2/((1-t)*a+t*b) at h
  rw [he] at h
  apply (mul_le_mul_of_nonneg_left h hba.le).trans_eq
  dsimp [t]; field_simp; ring

private theorem linear_modulus {a y : ℝ} (ha : 4 ≤ a) (hay : a ≤ y) (hy : y ≤ 2*a) :
    |G y-G a| ≤ 46*(y-a) := by
  have ha0 : 0 < a := by linarith
  have hy0 := ha0.trans_le hay
  have hh0 : 0 ≤ y-a := sub_nonneg.mpr hay
  have hA := abs_le.mp (G_linear (by linarith : 2 ≤ a))
  have hB := abs_le.mp (G_linear (by linarith : 2 ≤ 2*a))
  have hL := abs_le.mp (G_linear (by linarith : 2 ≤ a/2))
  have hY := abs_le.mp (G_linear (by linarith : 2 ≤ y))
  apply abs_le.mpr
  constructor
  · have h := chord (a:=a/2) (b:=y) (y:=a) (by linarith) (by linarith) (by linarith) hay
    have hid : (a-a/2)*(y-a)*(y-a/2)/a=(y-a)*(y-a/2)/2 := by field_simp; ring
    rw [hid] at h
    have hh : G (a/2)-G y ≤ 45*(y-a/2) := by linarith
    have hm := mul_le_mul_of_nonneg_left hh hh0
    have hscale : (y-a/2)*(G a-G y) ≤ (y-a/2)*(46*(y-a)) := by nlinarith [mul_nonneg hh0 (by linarith : 0 ≤ y-a/2)]
    linarith only [(le_of_mul_le_mul_left hscale (by linarith : 0 < y-a/2))]
  · have h := chord (a:=a) (b:=2*a) (y:=y) ha0 (by linarith) hay hy
    have hfrac : (y-a)*(2*a-y)*(2*a-a)/y ≤ (y-a)*a := by
      rw [div_le_iff₀ hy0]
      have hmul := mul_le_mul_of_nonneg_left (show 2*a-y ≤ y by linarith) (mul_nonneg hh0 ha0.le)
      linarith only [show (y-a)*(2*a-y)*(2*a-a) = (y-a)*a*(2*a-y) by ring,hmul]
    have hh : G (2*a)-G a ≤ 27*a := by linarith
    have hm := mul_le_mul_of_nonneg_left hh hh0
    have hscale : a*(G y-G a) ≤ a*(28*(y-a)) := by linarith only [h,hfrac,hm]
    linarith [le_of_mul_le_mul_left hscale ha0]

private noncomputable def raw (x : ℝ) (n : ℕ) := vonMangoldt n*max (x/(n:ℝ)-1) 0
private theorem raw_off {x : ℝ} {n : ℕ} (h : n ∉ range (⌊x⌋₊+1)) : raw x n=0 := by
  have hn : ⌊x⌋₊+1 ≤ n := by simpa using h
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hxn : x ≤ (n:ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  simp [raw,max_eq_right (sub_nonpos.mpr ((div_le_one hn0).mpr hxn))]

private theorem G_meas : Measurable G := by
  have he (x : ℝ) : (∑ n ∈ range (⌊x⌋₊+1),raw x n) = ∑' n,raw x n := (tsum_eq_sum (fun n hn => raw_off hn)).symm
  change Measurable (fun x : ℝ => (∑ n ∈ range (⌊x⌋₊+1),raw x n) - x*(Real.log x-1-Real.eulerMascheroniConstant))
  simp_rw [he]
  have hm : Measurable (fun x : ℝ => ∑' n,raw x n) := Measurable.tsum (fun n => by unfold raw; fun_prop)
  fun_prop

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

private theorem weight_part (N : ℕ) : (∑ n ∈ range N,w ((n:ℝ)+4)) ≤ 1 := by
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
  have h1 : R 3 ≤ 1 := by
    unfold R; apply inv_le_one_of_one_le₀; linarith [Real.log_nonneg (by norm_num : 1 ≤ (3:ℝ))]
  linarith [h N]

private theorem weight_sum : Summable (fun n : ℕ => w ((n:ℝ)+4)) :=
  summable_of_sum_range_le (fun n => by unfold w; positivity) weight_part

private theorem sample_nonneg (n : ℕ) : 0 ≤ sample ((n:ℝ)+4) := by unfold sample; positivity

private theorem sample_partial_RH (hRH : RiemannHypothesis) (N : ℕ) :
    (∑ n ∈ range N,sample ((n:ℝ)+4)) ≤ 81 := by
  have hz (z : ZetaZerosInTraceStrip (1/2)) : z.val.re ≤ 1/2 :=
    ((riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH) z.val z.prop.1 z.prop.2.1 z.prop.2.2.1).le
  have hp (n : ℕ) : sample ((n:ℝ)+4) ≤ 81*w ((n:ℝ)+4) := by
    let x := (n:ℝ)+4
    have hx : 4 ≤ x := by dsimp [x]; linarith [n.cast_nonneg (α:=ℝ)]
    have hx0 : 0 < x := by linarith
    have h := finite_ordinate_prime_ramp_approximation.2.2.1 (1/2) (by norm_num) hz (x^2) (by nlinarith)
    change |G (x^2)| ≤ 9*(x^2)^(1/2:ℝ) at h
    rw [←Real.sqrt_eq_rpow,Real.sqrt_sq hx0.le] at h
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    have h2 : (G (x^2))^2 ≤ 81*x^2 := by nlinarith [sq_abs (G (x^2))]
    change (G (x^2))^2/(x^3*(1+Real.log x)^2) ≤ 81*(1/(x*(1+Real.log x)^2))
    apply (div_le_div_of_nonneg_right h2 (by positivity)).trans_eq
    have hl := Real.log_nonneg (by linarith : 1 ≤ x)
    field_simp
  calc _ ≤ ∑ n ∈ range N,81*w ((n:ℝ)+4) := Finset.sum_le_sum fun n _ => hp n
       _ = 81*(∑ n ∈ range N,w ((n:ℝ)+4)) := (Finset.mul_sum ..).symm
       _ ≤ _ := by linarith [weight_part N]

private def e (u : ℝ) := (G (Real.exp u))^2/(Real.exp u*(1+u)^2)
private theorem e_meas : Measurable e := by unfold e; have h:=G_meas; fun_prop
private theorem e_pos (u : ℝ) : 0 ≤ e u := by unfold e; positivity
private theorem e_eq (u : ℝ) : (G (Real.exp u)*Real.exp (-((1/2:ℝ)*u))/(1+u))^2=e u := by
  unfold e; rw [div_pow,mul_pow,←Real.exp_nat_mul]
  push_cast
  rw [show (2:ℝ)*(-(1/2*u))= -u by ring,Real.exp_neg]
  simp only [div_eq_mul_inv,mul_inv_rev]; ring

private def hgt (n : ℕ) := 2*Real.log ((n:ℝ)+4)
private def cell (n : ℕ) := Ioc (hgt n) (hgt (n+1))
private def cb (r : ℝ) := (2*(G (r^2))^2+2*138^2*r^2)/(r^2*(1+Real.log r)^2)
private theorem cb_pos {r : ℝ} (hr : 0 ≤ r) : 0 ≤ cb r := by unfold cb; positivity

private theorem exp_hgt {r : ℝ} (hr : 0 < r) : Real.exp (2*Real.log r)=r^2 := by
  simpa [Real.exp_log hr] using Real.exp_nat_mul (Real.log r) 2

private theorem cell_bound {n : ℕ} {u : ℝ} (hu : u ∈ cell n) : e u ≤ cb ((n:ℝ)+4) := by
  let r : ℝ := (n:ℝ)+4
  have hr : 4 ≤ r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
  have hr0 : 0 < r := by linarith
  have hl := Real.log_nonneg (by linarith : 1 ≤ r)
  have hu0 : 2*Real.log r ≤ u := hu.1.le
  have hu1 : u ≤ 2*Real.log (r+1) := by
    have h := hu.2
    have he : hgt (n+1) = 2*Real.log (r+1) := by unfold hgt r; push_cast; ring_nf
    exact h.trans_eq he
  have hry : r^2 ≤ Real.exp u := (exp_hgt hr0).symm.le.trans (Real.exp_le_exp.mpr hu0)
  have hyr : Real.exp u ≤ (r+1)^2 := (Real.exp_le_exp.mpr hu1).trans_eq (exp_hgt (by linarith))
  have hdiff := linear_modulus (a:=r^2) (y:=Real.exp u) (by nlinarith) hry (by nlinarith)
  have hb : |G (Real.exp u)| ≤ |G (r^2)|+138*r := by
    have h := abs_add_le (G (Real.exp u)-G (r^2)) (G (r^2))
    rw [sub_add_cancel] at h
    nlinarith
  have hsq : (G (Real.exp u))^2 ≤ 2*(G (r^2))^2+2*138^2*r^2 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hb,sq_abs (G (Real.exp u)),sq_abs (G (r^2)),sq_nonneg (|G (r^2)|-138*r)]
  have hweight : r^2*(1+Real.log r)^2 ≤ Real.exp u*(1+u)^2 :=
    mul_le_mul hry (by nlinarith [mul_self_le_mul_self (by linarith : 0≤1+Real.log r) (by linarith : 1+Real.log r≤1+u)]) (sq_nonneg _) (Real.exp_nonneg _)
  exact div_le_div₀ (by positivity) hsq (by positivity : 0 < r^2*(1+Real.log r)^2) hweight

private theorem cell_integrable (n : ℕ) : IntegrableOn e (cell n) := by
  apply (integrableOn_const (C:=cb ((n:ℝ)+4)) (s:=cell n) (μ:=volume) measure_Ioc_lt_top.ne).mono' e_meas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioc (a:=hgt n) (b:=hgt (n+1)))] with u hu
  simpa only [Real.norm_of_nonneg (e_pos _)] using cell_bound (n:=n) hu

private theorem cell_mass (n : ℕ) : (∫ u in cell n, ‖e u‖) ≤
    4*sample ((n:ℝ)+4)+(4*138^2)*w ((n:ℝ)+4) := by
  let r : ℝ := (n:ℝ)+4
  have hr : 4 ≤ r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
  have hr0 : 0<r := by linarith
  have hmono : hgt n ≤ hgt (n+1) := by
    unfold hgt; apply mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by push_cast; linarith)) (by norm_num)
  have hlen : hgt (n+1)-hgt n ≤ 2/r := by
    have he := Real.log_le_sub_one_of_pos (div_pos (show 0<r+1 by linarith) hr0)
    rw [Real.log_div (by linarith) hr0.ne',show (r+1)/r-1=1/r by field_simp; ring] at he
    have hnext : hgt (n+1) = 2*Real.log (r+1) := by unfold hgt r; push_cast; ring_nf
    rw [hnext]; change 2*Real.log (r+1)-2*Real.log r ≤ 2/r; linarith [show 2/r = 2*(1/r) by ring]
  have hset : MeasurableSet (cell n) := measurableSet_Ioc
  have hc : IntegrableOn (fun _ : ℝ => cb r) (cell n) := integrableOn_const measure_Ioc_lt_top.ne
  calc _ ≤ ∫ _ in cell n,cb r := setIntegral_mono_on (cell_integrable n).norm hc hset fun u hu => by
             rw [Real.norm_of_nonneg (e_pos _)]; exact cell_bound hu
       _ = (hgt (n+1)-hgt n)*cb r := by rw [setIntegral_const,cell,Real.volume_real_Ioc_of_le hmono,smul_eq_mul]
       _ ≤ (2/r)*cb r := mul_le_mul_of_nonneg_right hlen (cb_pos hr0.le)
       _ = _ := by
          change (2/r)*cb r = 4*sample r+(4*138^2)*w r
          have hl := Real.log_nonneg (by linarith : 1≤r)
          unfold cb sample w; field_simp; ring

private theorem full_integral (hs : Summable (fun n : ℕ => sample ((n:ℝ)+4))) : IntegrableOn e (Ioi 0) := by
  have hm : Summable (fun n : ℕ => ∫ u in cell n,‖e u‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) cell_mass ((hs.mul_left 4).add (weight_sum.mul_left (4*138^2)))
  have hint := integrableOn_iUnion_of_summable_integral_norm cell_integrable hm
  have hlim : Tendsto hgt atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : 0<(2:ℝ))
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hunion : (⋃ n : ℕ,cell n)=Ioi (hgt 0) := by
    apply iUnion_Ioc_map_succ_eq_Ioi
    · intro n; change 2*Real.log ((0:ℕ)+4:ℝ) ≤ 2*Real.log ((n:ℝ)+4)
      apply mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by simp)) (by norm_num)
    · exact not_bddAbove_of_tendsto_atTop hlim
  rw [hunion] at hint
  have hstart : IntegrableOn e (Ioc 0 (hgt 0)) := by
    apply (integrableOn_const (C:=(144:ℝ)^2) (s:=Ioc 0 (hgt 0)) (μ:=volume) measure_Ioc_lt_top.ne).mono' e_meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 := le_of_lt (show 0 < u from hu.1)
    have hu1 : u ≤ 2*Real.log 4 := by simpa [hgt] using hu.2
    have h1 := Real.one_le_exp hu0
    have h2 : Real.exp u ≤ 16 := (Real.exp_le_exp.mpr hu1).trans (by rw [exp_hgt (by norm_num)]; norm_num)
    have hg : |G (Real.exp u)| ≤ 144 := by
      by_cases h : 2 ≤ Real.exp u
      · linarith [G_linear h]
      · linarith [small_G h1 (lt_of_not_ge h)]
    rw [Real.norm_of_nonneg (e_pos _)]
    apply (div_le_self (sq_nonneg _) (by nlinarith [mul_le_mul h1 (show 1 ≤ (1+u)^2 by nlinarith) (by norm_num : 0≤(1:ℝ)) (Real.exp_nonneg _)] : 1≤Real.exp u*(1+u)^2)).trans
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hg,sq_abs (G (Real.exp u))]
  have hpos : 0 ≤ hgt 0 := by simp [hgt,Real.log_nonneg (by norm_num : 1≤(4:ℝ))]
  simpa only [Ioc_union_Ioi_eq_Ioi hpos] using hstart.union hint

end RampSampleProof
open RampSampleProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let a (n : ℕ) := let k := (n:ℝ)+4
      (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (RiemannHypothesis ↔ Summable a) ∧
    (RiemannHypothesis ↔ ∀ N : ℕ,(∑ n ∈ range N,a n) ≤ 81) ∧
    (∀ x y : ℝ,4 ≤ x → x ≤ y → y ≤ 2*x → |G y-G x| ≤ 46*(y-x)) := by
  have hforward (h : RiemannHypothesis) : Summable (fun n : ℕ => sample ((n:ℝ)+4)) :=
    summable_of_sum_range_le sample_nonneg (sample_partial_RH h)
  have hreverse (h : Summable (fun n : ℕ => sample ((n:ℝ)+4))) : RiemannHypothesis := by
    apply riemannHypothesis_iff_prime_ramp_log_energy.2.1.mpr
    change IntegrableOn (fun u : ℝ => (G (Real.exp u)*Real.exp (-((1/2:ℝ)*u))/(1+u))^2) (Ioi 0)
    simp only [e_eq]
    exact full_integral h
  refine ⟨⟨hforward,hreverse⟩,⟨sample_partial_RH,fun h => hreverse (summable_of_sum_range_le sample_nonneg h)⟩,
    fun x y hx hxy hy => linear_modulus hx hxy hy⟩

end
