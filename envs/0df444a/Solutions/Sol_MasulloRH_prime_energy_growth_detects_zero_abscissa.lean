-- Prove2me | solution 1 for MasulloRH.prime_energy_growth_detects_zero_abscissa
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:47:51.802482+00:00
-- url     : https://prove2.me/submissions/49bb4a31-e2ab-4408-b07d-fd4b76ef95a2

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_prime_ramp_log_energy
import Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation
import Theorems.Thm_MasulloRH_prime_ramp_chord_and_fourth_power_bound
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib
open Filter Finset Set Topology MeasureTheory ArithmeticFunction
noncomputable section
open MasulloRH
namespace SquareGrowthProof
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

private theorem prefix_integrable : IntegrableOn e (Ioc 0 (hgt 0)) := by
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
private def E (N : ℕ) := ∑ n ∈ range N,sample ((n:ℝ)+4)
private abbrev Z := ZetaZerosInTraceStrip (1/2)

private theorem E_nonneg (N : ℕ) : 0≤E N := sum_nonneg fun n _ => sample_nonneg n
private theorem E_mono : Monotone E := by
  intro n m h
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) (fun i _ _ => sample_nonneg i)

private theorem weighted_samples {p q C : ℝ} (hp : 0≤p) (hq : p<q) (hC : 0≤C)
    (h : ∀ N : ℕ,E N≤C*((N:ℝ)+3)^p) :
    Summable (fun n : ℕ => sample ((n:ℝ)+4)*((n:ℝ)+4)^(-q)) := by
  let a (n : ℕ) := sample ((n:ℝ)+4)
  have hO : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n,a i) =O[atTop] (fun n : ℕ => (n:ℝ)^p) := by
    apply Asymptotics.IsBigO.of_bound (C*5^p)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
    have hs : (∑ i ∈ Finset.Icc 1 n,a i) ≤ E (n+1) :=
      sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)) (fun i _ _ => sample_nonneg i)
    have hpos : 0≤∑ i ∈ Finset.Icc 1 n,a i := sum_nonneg (fun i _ => sample_nonneg i)
    rw [Real.norm_of_nonneg hpos,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) p)]
    apply hs.trans ((h (n+1)).trans ?_)
    push_cast
    calc C*((n:ℝ)+1+3)^p ≤ C*(5*n)^p := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hp) hC
         _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  have hS : LSeriesSummable (fun n => (a n:ℂ)) (q:ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO sample_nonneg hp (by simpa)
  apply Summable.of_norm_bounded_eventually_nat (g:=fun n => ‖LSeries.term (fun n => (a n:ℂ)) (q:ℂ) n‖) hS.norm
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0<(n:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [LSeries.term_of_ne_zero (by omega),norm_div,Complex.norm_real,Real.norm_of_nonneg (sample_nonneg n)]
  change ‖a n*((n:ℝ)+4)^(-q)‖ ≤ a n/‖((n:ℕ):ℂ)^(q:ℂ)‖
  rw [show (n:ℂ)=((n:ℝ):ℂ) by simp,Complex.norm_cpow_eq_rpow_re_of_pos hnR,Complex.ofReal_re,
    Real.norm_of_nonneg (mul_nonneg (sample_nonneg n) (Real.rpow_nonneg (by positivity) _)),
    Real.rpow_neg (by positivity),←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (sample_nonneg n) (Real.rpow_pos_of_pos hnR q)
    (Real.rpow_le_rpow hnR.le (by linarith) (hp.trans hq.le))

private def tilt (q u : ℝ) := Real.exp (-(q/2)*u)
private def eqt (q u : ℝ) := e u*tilt q u
private theorem eqt_meas (q : ℝ) : Measurable (eqt q) := by
  unfold eqt tilt; have := e_meas; fun_prop
private theorem eqt_pos (q u : ℝ) : 0≤eqt q u := mul_nonneg (e_pos _) (Real.exp_nonneg _)

private theorem tilt_le {q u : ℝ} (hq : 0≤q) (hu : 0≤u) : tilt q u≤1 := by
  unfold tilt; rw [Real.exp_le_one_iff]; nlinarith

private theorem tilted_mono_on {q : ℝ} (hq : 0≤q) {U : Set ℝ} (hU : MeasurableSet U) (hpos : ∀ u∈U,0≤u)
    (h : IntegrableOn e U) : IntegrableOn (eqt q) U := by
  apply h.mono' (eqt_meas q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hU] with u hu
  rw [Real.norm_of_nonneg (eqt_pos _ _)]
  exact mul_le_of_le_one_right (e_pos _) (tilt_le hq (hpos u hu))

private theorem tilted_state {q : ℝ} (hq : 0≤q)
    (hs : Summable (fun n : ℕ => sample ((n:ℝ)+4)*((n:ℝ)+4)^(-q))) :
    IntegrableOn (eqt q) (Ioi 0) := by
  have hlow (n : ℕ) : 0≤hgt n := by
    unfold hgt; apply mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [n.cast_nonneg (α:=ℝ)]))
  have hint (n : ℕ) : IntegrableOn (eqt q) (cell n) :=
    tilted_mono_on hq measurableSet_Ioc (fun _ hu => (hlow n).trans hu.1.le) (cell_integrable n)
  have hmass (n : ℕ) : (∫ u in cell n, ‖eqt q u‖) ≤
      4*(sample ((n:ℝ)+4)*((n:ℝ)+4)^(-q)) + (4*138^2)*w ((n:ℝ)+4) := by
    let r := (n:ℝ)+4
    have hr : 1≤r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
    have hr0 : 0<r := by linarith
    have hrq := Real.rpow_nonneg hr0.le (-q)
    have ht (u : ℝ) (hu : u∈cell n) : tilt q u≤r^(-q) := by
      rw [tilt,Real.rpow_def_of_pos hr0,Real.exp_le_exp]
      have hle : 2*Real.log r≤u := hu.1.le
      nlinarith [mul_le_mul_of_nonneg_left hle hq]
    calc _ ≤ ∫ u in cell n, ‖e u‖*r^(-q) := by
             apply setIntegral_mono_on (hint n).norm ((cell_integrable n).norm.mul_const _) measurableSet_Ioc
             intro u hu
             rw [Real.norm_of_nonneg (eqt_pos _ _),Real.norm_of_nonneg (e_pos _)]
             exact mul_le_mul_of_nonneg_left (ht u hu) (e_pos u)
         _ = (∫ u in cell n,‖e u‖)*r^(-q) := integral_mul_const _ _
         _ ≤ (4*sample r+(4*138^2)*w r)*r^(-q) := mul_le_mul_of_nonneg_right (cell_mass n) hrq
         _ ≤ _ := by
           have hle := Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.mpr hq)
           have hw : 0≤w r := by unfold w; positivity
           change _ ≤ 4*(sample r*r^(-q))+(4*138^2)*w r
           nlinarith [mul_le_of_le_one_right hw hle]
  have hm : Summable (fun n : ℕ => ∫ u in cell n, ‖eqt q u‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hmass ((hs.mul_left 4).add (weight_sum.mul_left _))
  have hi := integrableOn_iUnion_of_summable_integral_norm hint hm
  have hlim : Tendsto hgt atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : 0<(2:ℝ))
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hunion : (⋃ n : ℕ,cell n)=Ioi (hgt 0) := by
    apply iUnion_Ioc_map_succ_eq_Ioi
    · intro n; unfold hgt; apply mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by simp)) (by norm_num)
    · exact not_bddAbove_of_tendsto_atTop hlim
  rw [hunion] at hi
  have hstart := tilted_mono_on hq measurableSet_Ioc (U:=Ioc 0 (hgt 0)) (fun _ hu => hu.1.le) prefix_integrable
  simpa only [Ioc_union_Ioi_eq_Ioi (hlow 0)] using hstart.union hi

private theorem zeros_of_weight {q : ℝ} (hq : 0≤q) (hq2 : q<2)
    (hs : Summable (fun n : ℕ => sample ((n:ℝ)+4)*((n:ℝ)+4)^(-q))) :
    ∀ z : Z, z.val.re≤1/2+q/4 := by
  apply (riemannHypothesis_iff_prime_ramp_log_energy.1 (1/2+q/4) (by linarith) (by linarith)).2
  have he (u : ℝ) : (G (Real.exp u)*Real.exp (-((1/2+q/4)*u))/(1+u))^2 = eqt q u := by
    unfold eqt e tilt
    rw [div_pow,mul_pow,←Real.exp_nat_mul]
    push_cast
    rw [show 2*(-((1/2+q/4)*u)) = -u + (-(q/2)*u) by ring,Real.exp_add,Real.exp_neg]
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  change IntegrableOn (fun u => (G (Real.exp u)*Real.exp (-((1/2+q/4)*u))/(1+u))^2) (Ioi 0)
  simp only [he]
  exact tilted_state hq hs

private def Subpower (p : ℝ) : Prop :=
  ∀ d : ℝ, 0<d → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,E N≤C*((N:ℝ)+3)^(p+d)

private theorem upper_of_subpower {p : ℝ} (hp : 0≤p) (h : Subpower p) :
    ∀ z : Z,z.val.re≤1/2+p/4 := by
  intro z
  by_contra! hbad
  let q := (p+4*(z.val.re-1/2))/2
  let d := (q-p)/2
  have hq : p<q := by dsimp [q]; linarith
  have hq2 : q<2 := by dsimp [q]; linarith [z.prop.2.2.1]
  have hd : 0<d := by dsimp [d]; linarith
  obtain ⟨C,hC,hb⟩ := h d hd
  have hw := weighted_samples (p:=p+d) (q:=q) (by linarith) (by dsimp [d]; linarith) hC hb
  have hz := zeros_of_weight (hp.trans hq.le) hq2 hw z
  dsimp [q] at hz
  linarith

private theorem exact_power_cap {p : ℝ} (hp : 0≤p) (hz : ∀ z : Z,z.val.re≤1/2+p/4) (N : ℕ) :
    E N ≤ 81*((N:ℝ)+3)^p := by
  have hpt (n : ℕ) (hn : n ∈ range N) : sample ((n:ℝ)+4) ≤ (81*((N:ℝ)+3)^p)*w ((n:ℝ)+4) := by
    let r := (n:ℝ)+4
    have hr : 4≤r := by dsimp [r]; linarith [n.cast_nonneg (α:=ℝ)]
    have hr0 : 0<r := by linarith
    have hl := Real.log_nonneg (show 1≤r by linarith)
    have hsmall : r≤(N:ℝ)+3 := by
      have ht : ((n+1:ℕ):ℝ)≤N := by exact_mod_cast mem_range.mp hn
      push_cast at ht; dsimp [r]; linarith
    have h := finite_ordinate_prime_ramp_approximation.2.2.1 (1/2+p/4) (by linarith) hz (r^2) (by nlinarith)
    change |G (r^2)| ≤ 9*(r^2)^(1/2+p/4) at h
    have he : ((r^2)^(1/2+p/4))^2 = r^p*r^2 := by
      rw [←Real.rpow_natCast_mul hr0.le,←Real.rpow_mul_natCast hr0.le,
        ←Real.rpow_natCast r 2,←Real.rpow_add hr0]
      congr 1; ring
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    have hh : (G (r^2))^2 ≤ 81*(r^p*r^2) := by
      rw [←he]; nlinarith [sq_abs (G (r^2))]
    have h1 : sample r ≤ 81*r^p*w r := by
      apply (div_le_div_of_nonneg_right hh (show 0≤r^3*(1+Real.log r)^2 by positivity)).trans_eq
      unfold w; field_simp <;> ring
    apply h1.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr0.le hsmall hp) (by norm_num))
      (by unfold w; positivity)
  calc E N ≤ ∑ n ∈ range N,(81*((N:ℝ)+3)^p)*w ((n:ℝ)+4) := sum_le_sum hpt
       _ = (81*((N:ℝ)+3)^p)*(∑ n ∈ range N,w ((n:ℝ)+4)) := (Finset.mul_sum ..).symm
       _ ≤ _ := mul_le_of_le_one_right (by positivity) (weight_part N)

private theorem subpower_of_exact {p : ℝ} (h : ∀ N : ℕ,E N≤81*((N:ℝ)+3)^p) : Subpower p := by
  intro d hd
  refine ⟨81,by norm_num,fun N => (h N).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α:=ℝ)])
    (show p≤p+d by linarith)) (by norm_num)

private def D (j : ℕ) : ℕ := 2^(2^j)
private theorem D_pos (j : ℕ) : 0<D j := by unfold D; positivity
private theorem D_sq (j : ℕ) : D (j+1) = (D j)^2 := by simp [D,pow_succ,pow_mul]
private theorem D_large (j : ℕ) : j+1≤D j := by
  induction j with
  | zero => norm_num [D]
  | succ j ih =>
    rw [D_sq]; have h2 : 2≤D j := by
      cases j with
      | zero => norm_num [D]
      | succ j => omega
    nlinarith
private theorem D_mono : Monotone D := monotone_nat_of_le_succ fun j => by
  rw [D_sq]; have := D_pos j; nlinarith

private theorem sparse_subpower (hs : ∃ J : ℕ,∀ j ≥ J,
    E (D j) ≤ (D j:ℝ)^(1/((j:ℝ)+1))) : Subpower 0 := by
  obtain ⟨J,hJ⟩ := hs
  intro d hd
  obtain ⟨K,hK⟩ := exists_nat_gt (2/d)
  let L := max J K
  refine ⟨max 1 (E (D L)),le_trans zero_le_one (le_max_left ..),?_⟩
  intro N
  rw [zero_add]
  have hN1 : 1≤(N:ℝ)+3 := by linarith [N.cast_nonneg (α:=ℝ)]
  have hpow := Real.one_le_rpow hN1 hd.le
  by_cases hsmall : N≤D L
  · exact (E_mono hsmall).trans ((le_max_right ..).trans
      (le_mul_of_one_le_right (le_trans zero_le_one (le_max_left ..)) hpow))
  have hreach : ∃ j : ℕ,N≤D j := ⟨N,by have := D_large N; omega⟩
  let j := Nat.find hreach
  have hj : N≤D j := Nat.find_spec hreach
  have hLj : L<j := by
    by_contra! hj'
    exact hsmall (hj.trans (D_mono hj'))
  have hj0 : 0<j := by omega
  have hprev : D (j-1)<N := lt_of_not_ge (Nat.find_min hreach (show j-1<j by omega))
  have hsq : D j≤N^2 := by
    have he : j-1+1=j := by omega
    rw [←he,D_sq]; exact Nat.pow_le_pow_left hprev.le _
  have hsqR : (D j:ℝ)≤((N:ℝ)+3)^2 := by
    have hcast : (D j:ℝ)≤(N:ℝ)^2 := by exact_mod_cast hsq
    nlinarith [N.cast_nonneg (α:=ℝ)]
  have hjJ : J≤j := (le_max_left J K).trans hLj.le
  have hKj : (K:ℝ)≤(j:ℝ) := by exact_mod_cast (le_max_right J K).trans hLj.le
  have hdj : 1/((j:ℝ)+1)≤d/2 := by
    have he := (div_lt_iff₀ hd).mp hK
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hKj hd.le]
  have hpos : 1≤(D j:ℝ) := by exact_mod_cast D_pos j
  calc E N ≤ E (D j) := E_mono hj
       _ ≤ (D j:ℝ)^(1/((j:ℝ)+1)) := hJ j hjJ
       _ ≤ (D j:ℝ)^(d/2) := Real.rpow_le_rpow_of_exponent_le hpos hdj
       _ ≤ (((N:ℝ)+3)^2)^(d/2) := Real.rpow_le_rpow (by positivity) hsqR (by linarith)
       _ = ((N:ℝ)+3)^d := by rw [←Real.rpow_natCast_mul (by positivity)]; congr 1; push_cast; ring
       _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_max_left ..)

private theorem sparse_of_RH (h : RiemannHypothesis) :
    ∃ J : ℕ,∀ j ≥ J,E (D j) ≤ (D j:ℝ)^(1/((j:ℝ)+1)) := by
  refine ⟨8,fun j hj => (sample_partial_RH h _).trans ?_⟩
  have hpow (m : ℕ) (hm : 8 ≤ m) : 7*(m+1)≤2^m := by
    induction m,hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have he : (7:ℝ)*((j:ℝ)+1)≤(2^j:ℕ) := by exact_mod_cast hpow j hj
  have hl : (7:ℝ)≤(2^j:ℕ)/((j:ℝ)+1) := (le_div_iff₀ (by positivity)).2 he
  have hid : (D j:ℝ)^(1/((j:ℝ)+1)) = (2:ℝ)^(((2^j:ℕ):ℝ)/((j:ℝ)+1)) := by
    unfold D; push_cast; rw [←Real.rpow_natCast_mul (by norm_num : 0≤(2:ℝ))]
    congr 1; push_cast; ring
  rw [hid]
  calc (81:ℝ) ≤ (2:ℝ)^(7:ℝ) := by norm_num
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hl

private theorem counter_witness {p : ℝ} (hp : 0≤p) (z : Z) (hz : 1/2+p/4<z.val.re)
    (C : ℝ) (L : ℕ) : ∃ N ≥ L, C*((N:ℝ)+3)^p < E N := by
  by_contra! hno
  let C' := max (max 0 C) (E L)
  have hc : 0≤C' := (le_max_left 0 C).trans (le_max_left ..)
  have hpwr (N : ℕ) : 1≤((N:ℝ)+3)^p := Real.one_le_rpow (by linarith [N.cast_nonneg (α:=ℝ)]) hp
  have hb (N : ℕ) : E N≤C'*((N:ℝ)+3)^p := by
    by_cases h : L≤N
    · exact (hno N h).trans (mul_le_mul_of_nonneg_right ((le_max_right 0 C).trans (le_max_left ..)) (by positivity))
    · exact (E_mono (le_of_not_ge h)).trans ((le_max_right ..).trans (le_mul_of_one_le_right hc (hpwr _)))
  have hsub : Subpower p := by
    intro d hd; refine ⟨C',hc,fun N => (hb N).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α:=ℝ)]) (by linarith)) hc
  exact (not_lt_of_ge (upper_of_subpower hp hsub z)) hz

private theorem usual_RH : RiemannHypothesis ↔ ∀ z : Z,z.val.re ≤ 1/2 := by
  rw [riemannHypothesis_iff_zeros_in_strip_on_line]
  constructor
  · exact fun h z => (h z.val z.prop.1 z.prop.2.1 z.prop.2.2.1).le
  · intro h s hzero h0 h1
    let z : Z := ⟨s,hzero,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hu : s.re ≤ 1/2 := h z
    have hnot (n : ℕ) : s ≠ -n := by
      intro he; have hr := congrArg Complex.re he; simp only [Complex.neg_re,Complex.natCast_re] at hr
      linarith [n.cast_nonneg (α:=ℝ)]
    have hne : s ≠ 1 := fun he => by simp [he] at h1
    have hz' : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnot hne,hzero,mul_zero]
    have h0' : 0 < (1-s).re := by simp; linarith
    have h1' : (1-s).re < 1 := by simp; linarith
    let z' : Z := ⟨1-s,hz',h0',h1',abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have hl : (1-s).re ≤ 1/2 := h z'
    rw [Complex.sub_re,Complex.one_re] at hl
    linarith

end SquareGrowthProof
open SquareGrowthProof

theorem solution :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (∀ p : ℝ, 0≤p →
      ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤1/2+p/4) ↔
        ∀ d : ℝ, 0<d → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,E N ≤ C*((N:ℝ)+3)^(p+d)) ∧
      ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤1/2+p/4) ↔
        ∀ N : ℕ,E N ≤ 81*((N:ℝ)+3)^p)) ∧
    (∀ p : ℝ,0≤p → ∀ z : ZetaZerosInTraceStrip (1/2), 1/2+p/4<z.val.re →
      ∀ (C : ℝ) (L : ℕ), ∃ N ≥ L, C*((N:ℝ)+3)^p < E N) ∧
    (RiemannHypothesis ↔ ∃ J : ℕ,∀ j ≥ J, let D := (2:ℕ)^(2^j)
      E D ≤ (D:ℝ)^(1/((j:ℝ)+1))) := by
  dsimp only
  refine ⟨fun p hp => ⟨⟨fun h => subpower_of_exact (exact_power_cap hp h),upper_of_subpower hp⟩,
    ⟨exact_power_cap hp,fun h => upper_of_subpower hp (subpower_of_exact h)⟩⟩,
    fun _ hp z hz C L => counter_witness hp z hz C L,sparse_of_RH,?_⟩
  intro h
  apply usual_RH.2
  simpa using upper_of_subpower (p:=0) (by norm_num) (sparse_subpower h)
