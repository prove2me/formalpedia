-- Prove2me | solution 1 for LogLogJam.Supplement.phase_location_from_samples
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:32:29.019635+00:00
-- url     : https://prove2.me/submissions/938df6cf-f91d-4848-8ad1-143e421cdd2a

import Theorems.Thm_LogLogJam_Supplement_squeezed_phase_density_bounds
import Theorems.Thm_LogLogJam_Supplement_squeezed_phase_first_moment

open MeasureTheory Set
open scoped ENNReal
namespace AngleStats
private noncomputable def P : ℝ := 2*Real.pi
private theorem pp : 0 < P := mul_pos (by norm_num) Real.pi_pos
def arc (a b : ℝ) : Set ℝ := {x | toIcoMod (by positivity : 0 < 2*Real.pi) a x < b}
theorem meas_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  unfold arc toIcoMod
  simp only [toIcoDiv_eq_floor,zsmul_eq_mul]
  exact measurableSet_lt (by fun_prop) measurable_const
private theorem periodIntegral (f : ℝ → ℝ) (hf : Function.Periodic f P) (a : ℝ) :
    ∫ x in Ico 0 P, f x = ∫ x in Ico a (a+P), f x := by
  simpa only [zero_add, intervalIntegral.integral_of_le pp.le,
    intervalIntegral.integral_of_le (le_add_of_nonneg_right pp.le),
    integral_Ico_eq_integral_Ioc] using hf.intervalIntegral_add_eq 0 a
private theorem arc_integral (f : ℝ → ℝ) (hf : Function.Periodic f P) (a b : ℝ)
    (hab : a ≤ b) (hb : b ≤ a+P) :
    (∫ x in arc a b ∩ Ico 0 P, f x) = ∫ x in a..b, f x := by
  let B := arc a b
  have hp : Function.Periodic (B.indicator f) P := by
    intro x
    change (if toIcoMod pp a (x+P)<b then f (x+P) else 0) = (if toIcoMod pp a x<b then f x else 0)
    rw [toIcoMod_add_right pp a x,hf]
  have he : B ∩ Ico a (a+P) = Ico a b := by
    ext x; constructor
    · rintro ⟨hx,h⟩
      change toIcoMod pp a x < b at hx
      rw [(toIcoMod_eq_self pp).mpr h] at hx; exact ⟨h.1,hx⟩
    · rintro ⟨h0,h1⟩
      have hx : x ∈ Ico a (a+P) := ⟨h0,h1.trans_le hb⟩
      refine ⟨?_,hx⟩; change toIcoMod pp a x < b; rwa [(toIcoMod_eq_self pp).mpr hx]
  have hs := meas_arc a b
  calc
    _ = ∫ x in Ico 0 P, B.indicator f x := by rw [setIntegral_indicator hs,inter_comm]
    _ = ∫ x in Ico a (a+P), B.indicator f x := periodIntegral _ hp _
    _ = ∫ x in Ico a b, f x := by rw [setIntegral_indicator hs,inter_comm,he]
    _ = _ := by rw [integral_Ico_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
private theorem arc_real (p : ℝ → ℝ) (hp : Function.Periodic p P) (hn : ∀ t, 0 ≤ p t)
    (μ : Measure ℝ) (α a b : ℝ)
    (hm : ∀ B : Set ℝ, MeasurableSet B → μ B = ENNReal.ofReal (∫ x in B ∩ Ico 0 P, p (x-α)))
    (h0 : a ≤ b) (h1 : b ≤ a+P) :
    μ.real (arc a b) = ∫ x in a-α..b-α, p x := by
  have hf : Function.Periodic (fun x => p (x-α)) P := by
    intro x; change p (x+P-α)=_; rw [show x+P-α = x-α+P by ring,hp]
  rw [measureReal_def,hm _ (meas_arc _ _),ENNReal.toReal_ofReal (integral_nonneg (fun _ => hn _))]
  rw [arc_integral _ hf a b h0 h1,intervalIntegral.integral_comp_sub_right]
private theorem half (p : ℝ → ℝ) (hc : Continuous p) (hp : Function.Periodic p P)
    (he : ∀ x, p (-x)=p x) (α : ℝ) (hm : (∫ x in Ico 0 P, p (x-α))=1) :
    (∫ x in (-Real.pi)..0, p x)=1/2 := by
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le pp.le,
    intervalIntegral.integral_comp_sub_right] at hm
  have h := hp.intervalIntegral_add_eq (0-α) (-Real.pi)
  have e : (0:ℝ)-α+P = P-α := by ring
  have e' : -Real.pi+P = Real.pi := by dsimp [P]; ring
  rw [e,e',hm] at h
  have t := intervalIntegral.integral_comp_neg (f:=p) (a:=(0:ℝ)) (b:=Real.pi)
  simp_rw [he] at t; rw [neg_zero] at t
  have z := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (-Real.pi) 0) (hc.intervalIntegrable (μ:=volume) 0 Real.pi)
  linarith
theorem arc_masses (p : ℝ → ℝ) (hc : Continuous p) (hp : Function.Periodic p (2*Real.pi))
    (hn : ∀ x, 0 ≤ p x) (he : ∀ x, p (-x)=p x)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (α h u d e : ℝ)
    (hm : ∀ B : Set ℝ, MeasurableSet B → μ B = ENNReal.ofReal (∫ x in B ∩ Ico 0 (2*Real.pi), p (x-α)))
    (hh : 0 ≤ h) (hh' : h ≤ 1/2) (hu : 0 ≤ u) (hu' : u ≤ 1/2)
    (hp0 : ∀ x, |x| ≤ u → d ≤ p x)
    (hpπ : ∀ x, |x+Real.pi| ≤ h → p x ≤ 1)
    (hgap : e ≤ u*d-h) :
    μ.real (arc (α-Real.pi-h) (α-u)) ≤ 1/2-e ∧
      1/2+e ≤ μ.real (arc (α-Real.pi+h) (α+u)) := by
  have hπ := Real.pi_gt_three
  have hm1 : (∫ x in Ico 0 P, p (x-α))=1 := by
    have H := congrArg ENNReal.toReal (hm univ MeasurableSet.univ)
    simpa [P,ENNReal.toReal_ofReal (integral_nonneg fun x => hn (x-α))] using H.symm
  have hhalf := half p hc hp he α hm1
  have int (a b : ℝ) := hc.intervalIntegrable (μ:=volume) a b
  have add (a b c : ℝ) := intervalIntegral.integral_add_adjacent_intervals (int a b) (int b c)
  have low (a b : ℝ) (hab : a ≤ b) (hal : -u ≤ a) (hb : b ≤ u) :
      (b-a)*d ≤ ∫ x in a..b, p x := by
    have H := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) (int a b)
      (f:=fun _ => d) (fun x hx => hp0 x (abs_le.mpr ⟨hal.trans hx.1,hx.2.trans hb⟩))
    simpa [smul_eq_mul] using H
  have high (a b : ℝ) (hab : a ≤ b) (hal : -Real.pi-h ≤ a) (hb : b ≤ -Real.pi+h) :
      (∫ x in a..b, p x) ≤ b-a := by
    have H := intervalIntegral.integral_mono_on hab (int a b) (intervalIntegrable_const)
      (g:=fun _ => (1:ℝ)) (fun x hx => hpπ x (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩))
    simpa using H
  constructor
  · rw [arc_real p hp hn μ α _ _ hm (by linarith) (by dsimp [P]; linarith)]
    rw [show α-Real.pi-h-α = -Real.pi-h by ring,show α-u-α = -u by ring]
    have l := low (-u) 0 (by linarith) le_rfl hu
    have t := high (-Real.pi-h) (-Real.pi) (by linarith) le_rfl (by linarith)
    linarith [add (-Real.pi-h) (-Real.pi) (-u), add (-Real.pi) (-u) 0]
  · rw [arc_real p hp hn μ α _ _ hm (by linarith) (by dsimp [P]; linarith)]
    rw [show α-Real.pi+h-α = -Real.pi+h by ring, show α+u-α = u by ring]
    have l := low 0 u hu (by linarith) le_rfl
    have t := high (-Real.pi) (-Real.pi+h) (by linarith) (by linarith) le_rfl
    linarith [add (-Real.pi) (-Real.pi+h) 0,add (-Real.pi+h) 0 u]
end AngleStats
open MeasureTheory Set Complex LogLogJam.Supplement
open scoped ENNReal ComplexConjugate
namespace AngleStats
noncomputable def ampq (q t : ℝ) : ℂ := ∑' n : ℕ,
  (((Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n)*q^n:ℝ):ℂ) *
      Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
noncomputable def density (q t : ℝ) : ℝ := Real.sqrt (1-q^2)/(2*Real.pi) * ‖ampq q t‖^2
theorem density_nn (q t : ℝ) : 0 ≤ density q t := by unfold density; positivity
private noncomputable def bn (n : ℕ) : ℝ := Real.sqrt (Nat.centralBinom n)/(2:ℝ)^n
private theorem b0 n : 0 ≤ bn n := by unfold bn; positivity
private theorem b1 n : bn n ≤ 1 := by
  have h : (Nat.centralBinom n:ℝ) ≤ (4:ℝ)^n := by exact_mod_cast Nat.centralBinom_le_four_pow n
  have e : (4:ℝ)^n = ((2:ℝ)^n)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  dsimp [bn]; rw [div_le_one (by positivity)]
  exact (Real.sqrt_le_iff.mpr ⟨by positivity,h.trans_eq e⟩)
theorem density_cont (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) : Continuous (density q) := by
  suffices h : Continuous (ampq q) from continuous_const.mul (h.norm.pow _)
  unfold ampq
  apply continuous_tsum (u:=fun n : ℕ => q^n) (fun _ => by fun_prop) (summable_geometric_of_lt_one hq hq')
  intro n t
  change ‖(↑(bn n*q^n):ℂ)*Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (b0 n) (pow_nonneg hq n)),
    Complex.norm_exp_I_mul_ofReal,mul_one]
  exact mul_le_of_le_one_left (pow_nonneg hq _) (b1 n)
theorem density_even (q t : ℝ) : density q (-t)=density q t := by
  have h : ampq q (-t) = conj (ampq q t) := by
    unfold ampq; rw [Complex.conj_tsum]; apply tsum_congr; intro n
    rw [map_mul,Complex.conj_ofReal,← Complex.exp_conj]
    congr 1; push_cast; simp
  rw [density,density,h,Complex.norm_conj]
theorem density_periodic (q : ℝ) : Function.Periodic (density q) (2*Real.pi) := by
  intro t
  have h : ampq q (t+2*Real.pi) = ampq q t := by
    apply tsum_congr; intro n; congr 1
    have e : Complex.I*((-((n:ℝ)*(t+2*Real.pi))):ℝ) =
        Complex.I*((-((n:ℝ)*t)):ℝ) + (-((n:ℤ):ℤ):ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [e,Complex.exp_add]
    have h' := Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ))
    push_cast at h' ⊢;rw [h',mul_one]
  unfold density; rw [h]
theorem hr_q (r : ℝ) (hr : 0 ≤ r) : 0 ≤ Real.tanh r := by
  rw [Real.tanh_eq_sinh_div_cosh]; exact div_nonneg (Real.sinh_nonneg_iff.mpr hr) (Real.cosh_pos _).le
private theorem gap (r : ℝ) : 1-(Real.tanh r)^2 = (Real.cosh r ^ 2)⁻¹ := by
  rw [Real.tanh_eq_sinh_div_cosh]; field_simp [(Real.cosh_pos r).ne']; nlinarith [Real.cosh_sq_sub_sinh_sq r]
theorem sinh_from_q (r : ℝ) : Real.sinh (2*r) = 2*Real.tanh r/(1-(Real.tanh r)^2) := by
  rw [gap,Real.sinh_two_mul,Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos r).ne']
private theorem sqrt_from_q (r : ℝ) : Real.sqrt (1-(Real.tanh r)^2) = 1/Real.cosh r := by
  rw [gap,Real.sqrt_inv,Real.sqrt_sq (Real.cosh_pos r).le,one_div]
theorem density_set (r θ : ℝ) (B : Set ℝ) :
    let b := fun n : ℕ => Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
    let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
    (∫ x in B ∩ Ico 0 (2*Real.pi),
      ‖∑' n, (((b n / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * z^n) *
        Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2) / (2 * Real.pi) =
      ∫ x in B ∩ Ico 0 (2*Real.pi), density (Real.tanh r) (x-2*θ) := by
  dsimp only
  let q := Real.tanh r
  let sc := Real.sqrt (Real.cosh r)
  have scpos : 0 < sc := Real.sqrt_pos.mpr (Real.cosh_pos _)
  have scal : ‖((sc:ℂ)⁻¹)‖^2 = 1/Real.cosh r := by
    simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg scpos.le,inv_pow,one_div]
    congr 1; exact Real.sq_sqrt (Real.cosh_pos _).le
  have hA (x : ℝ) : (∑' n : ℕ, ((bn n / sc:ℝ):ℂ) * ((q:ℂ)*Complex.exp ((2*θ:ℝ)*Complex.I))^n *
      Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)) = (sc:ℂ)⁻¹ * ampq q (x-2*θ) := by
    unfold ampq; rw [← tsum_mul_left]
    apply tsum_congr; intro n
    rw [mul_pow,← Complex.exp_nat_mul]
    dsimp [bn]
    push_cast
    rw [show Complex.I * -((n:ℂ)*((x:ℂ)-2*(θ:ℂ))) =
        ((n:ℂ)*((2*(θ:ℂ))*Complex.I))+(-(n:ℂ)*(x:ℂ)*Complex.I) by ring,Complex.exp_add]
    ring
  change (∫ x in B ∩ Ico 0 (2*Real.pi), ‖∑' n : ℕ, ((bn n / sc:ℝ):ℂ) * ((q:ℂ)*Complex.exp ((2*θ:ℝ)*Complex.I))^n *
      Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2)/(2*Real.pi) = _
  simp_rw [hA,norm_mul,mul_pow,scal]
  unfold density; rw [sqrt_from_q,integral_const_mul,integral_const_mul]; ring
theorem density_peak {q u : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hu : u ≤ (1-q)/2) (x : ℝ) (hx : |x|≤u) :
    1/(128*(1-q)) ≤ density q x := by
  have h := (squeezed_phase_density_bounds q hq hq').1 x (hx.trans hu)
  change 1/(32*Real.pi) ≤ (1-q)*density q x at h
  have hd : 0 < 1-q := by linarith
  have hpi := Real.pi_pos
  have h' : 1/(128:ℝ) ≤ 1/(32*Real.pi) := by apply one_div_le_one_div_of_le (by positivity); linarith [Real.pi_lt_four]
  apply (div_le_iff₀ (by positivity)).mpr; linarith [h'.trans h]
theorem density_far {q h : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (hh : h≤1/2) (x : ℝ) (hx : |x+Real.pi|≤h) :
    density q x ≤ 1 := by
  have hπ := Real.pi_gt_three
  have hi : Real.cos x ≤ 0 := by
    have z := Real.cos_nonneg_of_mem_Icc (x:=x+Real.pi) (by obtain ⟨ha,hb⟩ := abs_le.mp hx; constructor <;> linarith)
    rw [Real.cos_add_pi] at z; linarith
  have z := (squeezed_phase_density_bounds q hq hq').2 x hi
  apply le_trans z
  apply (div_le_iff₀ Real.pi_pos).mpr
  have hh' : Real.sqrt (1-q^2) ≤ 1 := (Real.sqrt_le_iff.mpr ⟨zero_le_one,by nlinarith [sq_nonneg q]⟩)
  linarith
end AngleStats
open MeasureTheory
open scoped ComplexConjugate
namespace PhaseChart

noncomputable def chart (c x : ℝ) := toIcoMod Real.two_pi_pos (c-Real.pi) x

theorem cut_mono {c d : ℝ} (h : c ≤ d) (x : ℝ) : chart c x ≤ chart d x := by
  simp only [chart,toIcoMod,toIcoDiv_eq_floor,zsmul_eq_mul]
  apply sub_le_sub_left; apply mul_le_mul_of_nonneg_right _ Real.two_pi_pos.le
  apply Int.cast_le.mpr; apply Int.floor_mono
  apply div_le_div_of_nonneg_right _ Real.two_pi_pos.le; linarith

theorem left_subset {a c h u : ℝ} (hac : |a-c| ≤ h) :
    {x | chart c x < a-u} ⊆ {x | chart (a-h) x < a-u} := by
  intro x hx; exact lt_of_le_of_lt (cut_mono (by linarith [(abs_le.mp hac).2]) x) hx

theorem right_subset {a c h u : ℝ} (hac : |a-c| ≤ h) :
    {x | chart (a+h) x < a+u} ⊆ {x | chart c x < a+u} := by
  intro x hx; exact lt_of_le_of_lt (cut_mono (by linarith [(abs_le.mp hac).1]) x) hx

theorem left_subset_le {a c h u : ℝ} (hac : |a-c| ≤ h) :
    {x | chart c x ≤ a-u} ⊆ {x | chart (a-h) x ≤ a-u} := by
  intro x hx; exact le_trans (cut_mono (by linarith [(abs_le.mp hac).2]) x) hx

theorem right_subset_le {a c h u : ℝ} (hac : |a-c| ≤ h) :
    {x | chart (a+h) x ≤ a+u} ⊆ {x | chart c x ≤ a+u} := by
  intro x hx; exact le_trans (cut_mono (by linarith [(abs_le.mp hac).1]) x) hx

theorem shifted_eq {a α : ℝ} (ha : (a:Real.Angle) = (α:Real.Angle)) (h u : ℝ) :
    {x | chart (a+h) x < a+u} = {x | chart (α+h) x < α+u} ∧
    {x | chart (a+h) x ≤ a+u} = {x | chart (α+h) x ≤ α+u} := by
  obtain ⟨k,hk⟩ := Real.Angle.coe_eq_zero_iff.mp (show ((a-α:ℝ):Real.Angle) = 0 by rw [Real.Angle.coe_sub,ha,sub_self])
  have eq : a = α+k • (2*Real.pi) := by linarith
  have hc (x) : chart (a+h) x = chart (α+h) x + k • (2*Real.pi) := by
    unfold chart;rw [eq,show α+k • (2*Real.pi)+h-Real.pi = (α+h-Real.pi)+k • (2*Real.pi) by abel,toIcoMod_add_zsmul']
  constructor <;> ext x <;> simp only [Set.mem_setOf_eq] <;> rw [hc] <;> constructor <;> intro hx <;> linarith

noncomputable def unitphase (a : ℝ) : ℂ := Complex.exp ((a:ℂ)*Complex.I)
private theorem unit_norm (a : ℝ) : ‖unitphase a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem same_phase {a b : ℝ} (h : (a:Real.Angle) = (b:Real.Angle)) :
    unitphase a = unitphase b := by
  have hc : Real.cos a = Real.cos b := congrArg Real.Angle.cos h
  have hs : Real.sin a = Real.sin b := congrArg Real.Angle.sin h
  apply Complex.ext <;> simp [unitphase,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,hc,hs]

private theorem chord (a c : ℝ) :
    ‖unitphase a-unitphase c‖ = 2*|Real.sin ((a-c)/2)| := by
  have h : unitphase a-unitphase c = (Complex.exp (Complex.I*((a-c:ℝ):ℂ))-1)*unitphase c := by
    unfold unitphase; rw [sub_mul,one_mul,← Complex.exp_add]
    congr 2; push_cast; ring
  rw [h,norm_mul,unit_norm,mul_one,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]

theorem coarse_arg (v : ℂ) (R q e α : ℝ) (he : 0 < e) (hq : 100000*e ≤ q)
    (hR : q/2 ≤ R) (hdev : ‖v-(R:ℂ)*unitphase α‖ ≤ 2*e) :
    ∃ a : ℝ, (a:Real.Angle) = (α:Real.Angle) ∧ |a-v.arg| ≤ 32*e/q := by
  let c := v.arg
  let a := chart c α
  have ha : (a:Real.Angle) = (α:Real.Angle) := Real.Angle.coe_toIcoMod _ _
  have hq0 : 0 < q := by linarith
  have hR0 : 0 < R := by linarith
  have hwin := toIcoMod_mem_Ico Real.two_pi_pos (c-Real.pi) α
  have hwin' : |a-c| ≤ Real.pi := by
    change c-Real.pi ≤ a ∧ a < c-Real.pi+2*Real.pi at hwin
    exact abs_le.mpr ⟨by linarith [hwin.1],by linarith [hwin.2]⟩
  have hRnorm : ‖(R:ℂ)*unitphase α‖ = R := by rw [norm_mul,unit_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0]
  have hrad : |‖v‖-R| ≤ 2*e := by
    rw [← hRnorm];exact (abs_norm_sub_norm_le _ _).trans hdev
  have hvarg : (‖v‖:ℂ)*unitphase c = v := Complex.norm_mul_exp_arg_mul_I _
  have hcr : ‖v-(R:ℂ)*unitphase c‖ ≤ 2*e := by
    rw [← hvarg,← sub_mul,norm_mul,unit_norm,mul_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; exact hrad
  have hsep : R*(2*|Real.sin ((a-c)/2)|) ≤ 4*e := by
    rw [← chord,same_phase ha]
    calc R*‖unitphase α-unitphase c‖ = ‖(R:ℂ)*unitphase α-(R:ℂ)*unitphase c‖ := by
           rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0]
         _ ≤ ‖(R:ℂ)*unitphase α-v‖ + ‖v-(R:ℂ)*unitphase c‖ := by simpa [dist_eq_norm] using dist_triangle ((R:ℂ)*unitphase α) v ((R:ℂ)*unitphase c)
         _ ≤ _ := by rw [norm_sub_rev ((R:ℂ)*unitphase α) v];linarith
  have hs := Real.mul_abs_le_abs_sin (x:=(a-c)/2) (by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)];linarith : |(a-c)/2| ≤ Real.pi/2)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hs
  have hp := Real.pi_pos
  have hθ : |a-c| ≤ Real.pi * |Real.sin ((a-c)/2)| := by
    field_simp at hs; linarith
  refine ⟨a,ha,(le_div_iff₀ hq0).mpr ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hθ hq0.le
  have h2 := mul_le_mul_of_nonneg_right hR (abs_nonneg (Real.sin ((a-c)/2)))
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_lt_four.le (mul_nonneg hq0.le (abs_nonneg (Real.sin ((a-c)/2))))]
end PhaseChart

namespace PhaseChart
open Finset

private def groups (n : ℕ) := (Finset.univ : Finset (Fin n)).powersetCard (n/2+1)
private theorem groups_ne {n : ℕ} (hn : 0<n) : (groups n).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr;simp;omega

private noncomputable def vmax {n : ℕ} (s : Finset (Fin n)) (v : Fin n → ℝ) :=
  if hs : s.Nonempty then s.sup' hs v else 0

noncomputable def median (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  if hn : 0<n then -(groups n).sup' (groups_ne hn) (fun s => -vmax s v) else 0

private theorem sup_meas {Ω ι : Type*} [MeasurableSpace Ω] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Ω → ℝ) (hm : ∀ i ∈ s, Measurable (f i)) : Measurable (fun t => s.sup' hs (fun i => f i t)) := by
  have h := Finset.measurable_sup' hs hm
  convert h using 1
  funext x; simp [Finset.sup'_apply]

theorem measurable_median (n : ℕ) : Measurable (median n) := by
  by_cases hn : 0<n
  · have single (s : Finset (Fin n)) : Measurable (vmax s) := by
      unfold vmax
      by_cases hs : s.Nonempty
      · simp only [dif_pos hs]
        exact sup_meas s hs (fun i (v : Fin n → ℝ) => v i) (fun i _ => measurable_pi_apply i)
      · simp only [dif_neg hs];exact measurable_const
    unfold median;simp only [dif_pos hn]
    exact (sup_meas _ (groups_ne hn) (fun s v => -vmax s v) (fun s _ => (single s).neg)).neg
  · unfold median; simp only [dif_neg hn];exact measurable_const

theorem median_lower {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (b : ℝ)
    (hh : (Finset.univ.filter fun i => x i < b).card ≤ n/2) : b ≤ median n x := by
  classical
  rw [median,dif_pos hn,le_neg];apply Finset.sup'_le
  intro s hs
  have hsize := (Finset.mem_powersetCard.mp hs).2
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hnsub : ¬s ⊆ (Finset.univ.filter fun i => x i < b) := by
    intro sub;have := Finset.card_le_card sub;omega
  obtain ⟨i,hi,hnot⟩ := Finset.not_subset.mp hnsub
  have hv : b ≤ x i := by simpa using hnot
  rw [vmax,dif_pos hne];exact neg_le_neg (hv.trans (Finset.le_sup' _ hi))

theorem median_upper {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (b : ℝ)
    (hh : n/2 < (Finset.univ.filter fun i => x i < b).card) : median n x < b := by
  classical
  obtain ⟨s,hsub,hsize⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hh)
  have hs : s ∈ groups n := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hsize⟩
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hv : vmax s x < b := by
    rw [vmax,dif_pos hne,Finset.sup'_lt_iff]
    intro i hi;exact (Finset.mem_filter.mp (hsub hi)).2
  have ht := Finset.le_sup' (fun t => -vmax t x) hs
  rw [median,dif_pos hn];linarith

theorem measurable_chart {Ω : Type*} [MeasurableSpace Ω] {c x : Ω → ℝ}
    (hc : Measurable c) (hx : Measurable x) : Measurable (fun t => chart (c t) (x t)) := by
  simp only [chart,toIcoMod,toIcoDiv_eq_floor,zsmul_eq_mul]
  fun_prop

noncomputable def trained_angle {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :=
  median n (fun i => chart c (x i)) / 2

theorem measurable_trained {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {C : Ω → ℝ} {f : Ω → Fin n → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun t => trained_angle (C t) (f t)) := by
  apply Measurable.div_const
  exact (measurable_median n).comp (measurable_pi_iff.mpr fun i => measurable_chart hC ((measurable_pi_apply i).comp hf))

theorem trained_error {n : ℕ} (hn : 0<n) (x : Fin n → ℝ) (a α c h u : ℝ) (hu : 0≤u)
    (ha : (a:Real.Angle)=(α:Real.Angle)) (hac : |a-c|≤h)
    (hleft : (Finset.univ.filter fun i => chart (α-h) (x i) < α-u).card ≤ n/2)
    (hright : n/2 < (Finset.univ.filter fun i => chart (α+h) (x i) < α+u).card) :
    |Real.sin (α/2 - trained_angle c x)| ≤ u/2 := by
  classical
  let y (i : Fin n) := chart c (x i)
  have hL : {t | chart c t < a-u} ⊆ {t | chart (α-h) t < α-u} := by
    have sh := (shifted_eq ha (-h) (-u)).1
    rw [← sub_eq_add_neg,← sub_eq_add_neg,← sub_eq_add_neg,← sub_eq_add_neg] at sh
    exact (left_subset hac).trans sh.subset
  have hU : {t | chart (α+h) t < α+u} ⊆ {t | chart c t < a+u} :=
    (shifted_eq ha h u).1.symm.subset.trans (right_subset hac)
  have hlsub : (Finset.univ.filter fun i => y i < a-u) ⊆ (Finset.univ.filter fun i => chart (α-h) (x i) < α-u) := by
    intro i hi;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL (Finset.mem_filter.mp hi).2⟩
  have hrsub : (Finset.univ.filter fun i => chart (α+h) (x i) < α+u) ⊆ (Finset.univ.filter fun i => y i < a+u) := by
    intro i hi;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU (Finset.mem_filter.mp hi).2⟩
  have ll := median_lower hn y (a-u) ((Finset.card_le_card hlsub).trans hleft)
  have uu := median_upper hn y (a+u) (hright.trans_le (Finset.card_le_card hrsub))
  have hsin : |Real.sin (α/2-trained_angle c x)| = |Real.sin (a/2-trained_angle c x)| := by
    have hco : ((2*(α/2-trained_angle c x):ℝ):Real.Angle) = ((2*(a/2-trained_angle c x):ℝ):Real.Angle) := by
      rw [show 2*(α/2-trained_angle c x)=α-2*trained_angle c x by ring,show 2*(a/2-trained_angle c x)=a-2*trained_angle c x by ring,Real.Angle.coe_sub,Real.Angle.coe_sub,ha]
    have hd : 2 • ((α/2-trained_angle c x:ℝ):Real.Angle) = 2 • ((a/2-trained_angle c x:ℝ):Real.Angle) := by simpa only [two_nsmul,two_mul,Real.Angle.coe_add] using hco
    exact Real.Angle.abs_sin_eq_of_two_nsmul_eq hd
  rw [hsin];apply Real.abs_sin_le_abs.trans
  change |a/2 - median n y/2| ≤ u/2
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end PhaseChart


open MeasureTheory
open scoped ENNReal
namespace PhaseChart

theorem phase_moments_of_density (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ) (α : ℝ)
    (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (hμ : ∀ B : Set ℝ, MeasurableSet B → μ B = ENNReal.ofReal
      (∫ x in B ∩ Set.Ico 0 (2*Real.pi), p (x-α))) :
    let w := fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)
    let M := ∫ x in Set.Ico 0 (2*Real.pi), w x * (p (x-α):ℂ)
    (∫ x, w x ∂μ) = M ∧ (∫ x, Real.cos x ∂μ) = M.re ∧ (∫ x, Real.sin x ∂μ) = M.im := by
  let J := Set.Ico 0 (2*Real.pi)
  let f (x : ℝ) := p (x-α)
  let w (x : ℝ) := Complex.exp ((x:ℂ)*Complex.I)
  have hf : Continuous f := hp.comp (continuous_id.sub continuous_const)
  have hf0 x : 0 ≤ f x := hp0 _
  have hj : MeasurableSet J := measurableSet_Ico
  have hi : IntegrableOn f J := hf.continuousOn.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hw : Continuous w := by unfold w;fun_prop
  have hwi : Integrable w μ := by
    apply (integrable_const (1:ℝ)).mono' hw.aestronglyMeasurable;filter_upwards with x
    rw [show ‖w x‖=1 from Complex.norm_exp_ofReal_mul_I _]
  have hEq : μ = (volume.restrict J).withDensity (fun x => ENNReal.ofReal (f x)) := by
    ext B hB;rw [hμ B hB,withDensity_apply _ hB,Measure.restrict_restrict hB]
    apply ofReal_integral_eq_lintegral_ofReal
    · exact hi.mono_set Set.inter_subset_right
    · exact Filter.Eventually.of_forall fun x => hf0 x
  have he : (∫ x, w x ∂μ) = ∫ x in J, w x * (f x:ℂ) := by
    rw [hEq]
    have hd : Measurable (fun x => ENNReal.ofReal (f x)) := ENNReal.measurable_ofReal.comp hf.measurable
    rw [integral_withDensity_eq_integral_toReal_smul hd (by simp) w]
    apply integral_congr_ae;filter_upwards with x
    rw [ENNReal.toReal_ofReal (hf0 x),Complex.real_smul,mul_comm]
  refine ⟨he,?_,?_⟩
  · have h := integral_re hwi
    change (∫ x, (w x).re ∂μ) = (∫ x, w x ∂μ).re at h
    exact ((by simpa only [w,Complex.exp_ofReal_mul_I_re] using h) : (∫ x, Real.cos x ∂μ) = (∫ x,w x ∂μ).re).trans (congrArg Complex.re he)
  · have h := integral_im hwi
    change (∫ x, (w x).im ∂μ) = (∫ x, w x ∂μ).im at h
    exact ((by simpa only [w,Complex.exp_ofReal_mul_I_im] using h) : (∫ x, Real.sin x ∂μ) = (∫ x,w x ∂μ).im).trans (congrArg Complex.im he)
end PhaseChart
open MeasureTheory ProbabilityTheory
open scoped ENNReal
private theorem bounded_product_tail {m : ℕ} (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset (Fin m)) (hs : s.Nonempty) (f : Fin m → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hb : ∀ i x, |f i x| ≤ 1) (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ) {x | (s.card:ℝ)*t ≤ ∑ i ∈ s, (f i (x i) - ∫ y, f i y ∂μ i)} ≤
      ENNReal.ofReal (Real.exp (-(s.card:ℝ)*t^2/2)) := by
  let X (i : Fin m) (x : Fin m → ℝ) := f i (x i) - ∫ y, f i y ∂μ i
  have hind : iIndepFun X (Measure.pi μ) := iIndepFun_pi (X:=fun i y => f i y - ∫ u, f i u ∂μ i) (fun i => ((hf i).sub_const _).aemeasurable)
  have hsub (i : Fin m) : HasSubgaussianMGF (X i) 1 (Measure.pi μ) := by
    have heta : HasSubgaussianMGF (fun x => f i x - ∫ y, f i y ∂μ i) 1 (μ i) := by
      have h := hasSubgaussianMGF_of_mem_Icc (μ:=μ i) (X:=f i) (hf i).aemeasurable (a := (-1:ℝ)) (b := 1) (ae_of_all _ fun x => (abs_le.mp (hb i x)))
      convert h using 1 <;> norm_num [Real.nnnorm_of_nonneg]
    have hp := measurePreserving_eval μ i
    rw [← hp.map_eq] at heta
    have q := HasSubgaussianMGF.of_map hp.measurable.aemeasurable (X:=fun x => f i x - ∫ y, f i y ∂(Measure.pi μ).map (Function.eval i)) heta
    simpa only [hp.map_eq, Function.comp_def, Function.eval] using q
  have hi : 0 < (s.card:ℝ) := by exact_mod_cast s.card_pos.mpr hs
  have he := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (c:=fun _ => 1) (s:=s) (fun i _ => hsub i) (mul_nonneg hi.le ht.le)
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hn : -((s.card:ℝ)*t)^2 / (2*(s.card:ℝ)) = -(s.card:ℝ)*t^2/2 := by field_simp <;> ring
  simpa [X, Measure.real,hn] using he

open scoped Classical

theorem phase_empirical_tail {m : ℕ} (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset (Fin m)) (hs : s.Nonempty) (L U : Set ℝ) (hL : MeasurableSet L) (hU : MeasurableSet U)
    (C S e : ℝ) (he : 0 < e)
    (hC : ∀ i ∈ s, ∫ x, Real.cos x ∂μ i = C)
    (hS : ∀ i ∈ s, ∫ x, Real.sin x ∂μ i = S)
    (hlo : ∀ i ∈ s, (μ i).real L ≤ 1/2-2*e) (hhi : ∀ i ∈ s, 1/2+2*e ≤ (μ i).real U) :
    (Measure.pi μ) {x : Fin m → ℝ | ¬ (
      ‖(s.card:ℂ)⁻¹ * ∑ i ∈ s, Complex.exp ((x i:ℂ)*Complex.I) - ((C:ℂ)+(S:ℂ)*Complex.I)‖ ≤ 2*e ∧
      (((s.filter (fun i => x i ∈ L)).card:ℝ) < (s.card:ℝ)/2) ∧
      ((s.card:ℝ)/2 < ((s.filter (fun i => x i ∈ U)).card:ℝ)))} ≤
        ENNReal.ofReal (6 * Real.exp (-(s.card:ℝ)*e^2/2)) := by
  classical
  let n : ℝ := s.card
  have hn : 0 < n := by dsimp [n]; exact_mod_cast s.card_pos.mpr hs
  let T (f : ℝ → ℝ) : Set (Fin m → ℝ) := {x | n*e ≤ ∑ i ∈ s, (f (x i)- ∫ y, f y ∂μ i)}
  let b := Real.exp (-n*e^2/2)
  have tail (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
      (Measure.pi μ) (T f) ≤ ENNReal.ofReal b :=
    bounded_product_tail μ s hs (fun _ => f) (fun _ => hf) (fun _ => hb) e he
  let ind (A : Set ℝ) (x : ℝ) : ℝ := A.indicator (fun _ => 1) x
  have hind (A : Set ℝ) (hA : MeasurableSet A) : Measurable (ind A) := measurable_const.indicator hA
  have hib (A : Set ℝ) (x : ℝ) : |ind A x| ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [ind, Set.indicator, hx]
  have hint (A : Set ℝ) (hA : MeasurableSet A) (i : Fin m) :
      ∫ y, ind A y ∂μ i = (μ i).real A := by simp [ind, integral_indicator hA, Measure.real]
  have hcnt (x : Fin m → ℝ) (A : Set ℝ) :
      ∑ i ∈ s, ind A (x i) = ((s.filter (fun i => x i ∈ A)).card:ℝ) := by
    simp [ind, Set.indicator, Finset.sum_boole]
  let fs : Fin 6 → ℝ → ℝ := ![Real.cos, fun x => -Real.cos x, Real.sin, fun x => -Real.sin x,
    ind L, fun x => -ind U x]
  have ht (j : Fin 6) : (Measure.pi μ) (T (fs j)) ≤ ENNReal.ofReal b := by
    apply tail
    · fin_cases j <;> simp [fs, Real.measurable_cos, Real.measurable_sin, hind L hL, hind U hU,
        Real.measurable_cos.neg,Real.measurable_sin.neg,(hind U hU).neg]
    · intro x
      fin_cases j <;> simp [fs, Real.abs_cos_le_one, Real.abs_sin_le_one, hib]
  calc
    _ ≤ (Measure.pi μ) (⋃ j, T (fs j)) := by
      apply measure_mono
      intro x hx
      by_contra h
      have hnot (j : Fin 6) : x ∉ T (fs j) := fun hj => h (Set.mem_iUnion.mpr ⟨j,hj⟩)
      have qa (f : ℝ → ℝ) (a : ℝ) (ha : ∀ i ∈ s, ∫ y, f y ∂μ i = a)
          (h₁ : x ∉ T f) (h₂ : x ∉ T (fun v => -f v)) :
          |n⁻¹ * (∑ i ∈ s, f (x i)) - a| ≤ e := by
        have hp : (∑ i ∈ s, f (x i)) - n*a < n*e := by
          change ¬ n*e ≤ _ at h₁
          have := lt_of_not_ge h₁
          simpa [Finset.sum_sub_distrib,Finset.sum_congr rfl ha,n] using this
        have hm : -(∑ i ∈ s, f (x i)) + n*a < n*e := by
          change ¬ n*e ≤ _ at h₂
          have := lt_of_not_ge h₂
          simp only [integral_neg,sub_neg_eq_add,Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.sum_congr rfl ha,Finset.sum_const,nsmul_eq_mul] at this
          exact this
        rw [← div_eq_inv_mul, abs_le]
        constructor <;> [apply le_of_lt; apply le_of_lt]
        · rw [lt_sub_iff_add_lt, lt_div_iff₀ hn]; linarith
        · rw [sub_lt_iff_lt_add, div_lt_iff₀ hn]; linarith
      apply hx
      refine ⟨?_,?_,?_⟩
      · have hc := qa Real.cos C hC (hnot 0) (hnot 1)
        have hs' := qa Real.sin S hS (hnot 2) (hnot 3)
        apply (Complex.norm_le_abs_re_add_abs_im _).trans
        change _ ≤ 2*e
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
        simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
          Complex.mul_re,Complex.mul_im, Complex.ofReal_re,Complex.ofReal_im,
          Complex.I_re,Complex.I_im, mul_zero,mul_one,add_zero,zero_add,zero_mul,sub_zero, Complex.re_sum,Complex.im_sum,
          Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
        exact (add_le_add hc hs').trans (by ring_nf; rfl)
      · have hh := hnot 4
        change ¬ n*e ≤ _ at hh
        have htop := lt_of_not_ge hh
        change (∑ i ∈ s, (ind L (x i) - ∫ y, ind L y ∂μ i)) < n*e at htop
        rw [Finset.sum_sub_distrib,hcnt] at htop
        have ha := Finset.sum_le_sum (s:=s) (fun i hi => (hint L hL i).le.trans (hlo i hi))
        simp only [Finset.sum_const,nsmul_eq_mul] at ha
        change _ < n/2
        change _ ≤ n*_ at ha
        nlinarith [mul_pos hn he]
      · have hh := hnot 5
        change ¬ n*e ≤ _ at hh
        have hbot := lt_of_not_ge hh
        change (∑ i ∈ s, (-ind U (x i) - ∫ y, -ind U y ∂μ i)) < n*e at hbot
        simp only [integral_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib,hcnt] at hbot
        have ha := Finset.sum_le_sum (s:=s) (fun i hi => (hhi i hi).trans (hint U hU i).ge)
        simp only [Finset.sum_const,nsmul_eq_mul] at ha
        change n/2 < _
        change n*_ ≤ _ at ha
        nlinarith [mul_pos hn he]
    _ ≤ ∑ j : Fin 6, (Measure.pi μ) (T (fs j)) := by simpa using (measure_iUnion_le (μ:=Measure.pi μ) (fun j => T (fs j)))
    _ ≤ ∑ _j : Fin 6, ENNReal.ofReal b := Finset.sum_le_sum fun j _ => ht j
    _ = _ := by simp [ENNReal.ofReal_mul, b, n]
open MeasureTheory
open scoped ENNReal
theorem phase_sample_arithmetic :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1/4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2/δ) / η^2 ≤ m → 0 < m/2 ∧
      ENNReal.ofReal (6 * Real.exp (-(↑(m/2) : ℝ) * (η/100000000)^2 / 2)) ≤ ENNReal.ofReal δ := by
  refine ⟨24 * 100000000^2, by positivity, ?_⟩
  intro η δ hη hη' hδ hδ' m hm
  have hratio : 2 ≤ (2:ℝ)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2) hratio
  have hms := (div_le_iff₀ (sq_pos_of_pos hη)).mp hm
  have hm₂ : 2 ≤ m := by
    by_contra! h
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hms <;>
      nlinarith [Real.log_two_gt_d9, mul_nonneg hη.le (sub_nonneg.mpr hη')]
  have hn : (m:ℝ) ≤ 4*(↑(m/2):ℝ) := by exact_mod_cast (show m ≤ 4*(m/2) by omega)
  have hl₃ : Real.log (6/δ) ≤ 3*Real.log (2/δ) := by
    have hpow : (3:ℝ) ≤ (2/δ)^2 := by nlinarith [sq_nonneg (2/δ-2)]
    have ht := Real.log_le_log (by norm_num : (0:ℝ)<3) hpow
    rw [Real.log_pow] at ht
    rw [show (6:ℝ)/δ=3*(2/δ) by ring,Real.log_mul (by norm_num) (by positivity)]
    norm_num at ht;linarith
  have hbudget : 3*Real.log (2/δ) ≤ (↑(m/2):ℝ)*(η/100000000)^2/2 := by
    nlinarith only [hms,mul_le_mul_of_nonneg_right hn (sq_nonneg η)]
  refine ⟨by omega, ENNReal.ofReal_le_ofReal ?_⟩
  have hneg := Real.exp_le_exp.mpr (neg_le_neg (hl₃.trans hbudget))
  rw [Real.exp_neg (Real.log _), Real.exp_log (by positivity)] at hneg
  rw [show -(↑(m/2):ℝ)*(η/100000000)^2/2 = -((↑(m/2):ℝ)*(η/100000000)^2/2) by ring]
  calc
    _ ≤ 6*(6/δ)⁻¹ := mul_le_mul_of_nonneg_left hneg (by norm_num)
    _ = δ := by field_simp

theorem phase_weak_scale (η q x : ℝ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hq : 0 ≤ q) (hq' : q < 1) (hw : q < 100000*(η/100000000)) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (2*q/(1-q^2))*x ≤ η := by
  have hsmall : q ≤ 1/2 := by linarith
  have hh : 0 < 1-q^2 := by nlinarith [mul_pos (sub_pos.mpr hq') (by linarith : 0 < 1+q)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hh]
  have hsq : q^2 ≤ 1/4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2-q) (by linarith : 0 ≤ 1/2+q)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1/4-q^2) hη.le, mul_nonneg hq (sub_nonneg.mpr hx')]
theorem phase_strong_scale (η q : ℝ) (hη : 0 < η) (hη' : η ≤ 1/4)
    (hq : 0 ≤ q) (hq' : q < 1) (hw : 100000*(η/100000000) ≤ q) :
    let e := η/100000000
    let h := 32*e/q
    let u := 8192*e*(1-q)/q
    let d := 1/(128*(1-q))
    0 ≤ h ∧ h ≤ 1/2 ∧ 0 ≤ u ∧ u ≤ 1/2 ∧ u ≤ (1-q)/2 ∧ 2*e ≤ u*d-h ∧
      (2*q/(1-q^2))*(u/2) ≤ η := by
  dsimp only
  have hq₀ : 0 < q := by linarith
  have hd : 0 < 1-q := by linarith
  have hh : 0 < 1-q^2 := by nlinarith [mul_pos hd (by linarith : 0 < 1+q)]
  have hu : 8192*(η/100000000)*(1-q)/q ≤ (1-q)/2 := by
    rw [div_le_iff₀ hq₀]
    nlinarith [mul_nonneg (by linarith : 0 ≤ q/2-8192*(η/100000000)) hd.le]
  refine ⟨by positivity, (div_le_iff₀ hq₀).mpr (by linarith), by positivity, by linarith, hu, ?_, ?_⟩
  · have h : 8192*(η/100000000)*(1-q)/q*(1/(128*(1-q))) - 32*(η/100000000)/q = 32*(η/100000000)/q := by
      field_simp; ring
    rw [h, le_div_iff₀ hq₀]
    nlinarith [mul_nonneg hη.le hd.le]
  · have h : (2*q/(1-q^2))*(8192*(η/100000000)*(1-q)/q/2) = (8192*(η/100000000))/(1+q) := by
      field_simp; ring
    rw [h, div_le_iff₀ (by linarith : 0 < 1+q)]
    nlinarith [mul_nonneg hη.le hq]
open MeasureTheory AngleStats PhaseChart LogLogJam.Supplement
open scoped ENNReal Classical
set_option maxHeartbeats 850000

theorem solution :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∃ angle : (Fin m → ℝ) → ℝ, Measurable angle ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      ∀ (r θ : ℝ), 0 ≤ r → ∀ μ : Fin m → Measure ℝ,
        (∀ i, IsProbabilityMeasure (μ i)) →
        (∀ (i : Fin m), i.val < m / 2 → ∀ B : Set ℝ, MeasurableSet B →
          let b := fun n : ℕ => Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n
          let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ:ℝ)*Complex.I)
          μ i B = ENNReal.ofReal ((∫ x in B ∩ Set.Ico 0 (2*Real.pi),
            ‖∑' n, (((b n / Real.sqrt (Real.cosh r) : ℝ) : ℂ) * z^n) *
              Complex.exp (-(n:ℂ)*(x:ℂ)*Complex.I)‖^2) / (2 * Real.pi))) →
        Measure.pi μ {x | η < Real.sinh (2*r) * |Real.sin (θ - angle x)|} ≤ ENNReal.ofReal δ
 := by
  classical
  obtain ⟨K,hK,hN⟩ := phase_sample_arithmetic
  refine ⟨K,hK,?_⟩
  intro η δ hη hη4 hδ hδ1 m hm
  obtain ⟨hn0,hprob⟩ := hN η δ hη hη4 hδ hδ1 m hm
  let n := m/2
  have hn : 0 < n := hn0
  let emb : Fin n ↪ Fin m := ⟨fun i => ⟨i.val,i.isLt.trans_le (Nat.div_le_self _ _)⟩,
    fun i j h => Fin.ext (congrArg (fun z : Fin m => z.val) h)⟩
  let s := Finset.univ.map emb
  have hs : s.Nonempty := ⟨emb ⟨0,hn⟩,Finset.mem_map_of_mem _ (Finset.mem_univ _)⟩
  have hsc : s.card = n := by simp [s]
  have hfirst (i : Fin m) (hi : i ∈ s) : i.val < m/2 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact j.isLt
  let Y := fun (x : Fin m → ℝ) (j : Fin n) => x (emb j)
  let Z := fun x : Fin m → ℝ => (s.card:ℂ)⁻¹ * ∑ i ∈ s, Complex.exp ((x i:ℂ)*Complex.I)
  let angle := fun x : Fin m → ℝ => trained_angle (Z x).arg (Y x)
  have hmZ : Measurable Z := by dsimp [Z]; fun_prop
  refine ⟨angle,measurable_trained (Complex.measurable_arg.comp hmZ) (measurable_pi_lambda _ (fun i => measurable_pi_apply (emb i))),?_,?_⟩
  · intro x y hxy
    have hY : Y x=Y y := by funext i; exact hxy _ i.isLt
    have hZ : Z x=Z y := by
      unfold Z; congr 1; apply Finset.sum_congr rfl; intro i hi; rw [hxy _ (hfirst i hi)]
    dsimp only [angle]; rw [hY,hZ]
  intro r θ hr μ hμ hread
  letI (i : Fin m) : IsProbabilityMeasure (μ i) := hμ i
  let q := Real.tanh r
  let e := η/100000000
  let α := 2*θ
  let p := density q
  have hq : 0 ≤ q := hr_q r hr
  have hq' : q < 1 := Real.tanh_lt_one r
  have he : 0 < e := by dsimp [e]; positivity
  by_cases hstrong : 100000*e ≤ q
  · let h := 32*e/q
    let u := 8192*e*(1-q)/q
    let d := 1/(128*(1-q))
    obtain ⟨hh,hh',hu,hu',huq,hgap,hrisk⟩ := phase_strong_scale η q hη hη4 hq hq' hstrong
    let L := arc (α-Real.pi-h) (α-u)
    let U := arc (α-Real.pi+h) (α+u)
    have laws (i : Fin m) (hi : i∈s) (B : Set ℝ) (hB : MeasurableSet B) :
        μ i B = ENNReal.ofReal (∫ x in B ∩ Set.Ico 0 (2*Real.pi), p (x-α)) := by
      rw [hread i (hfirst i hi) B hB,← density_set r θ B]
    have hnorm : (∫ x in Set.Ico 0 (2*Real.pi), p (x-α)) = 1 := by
      obtain ⟨i,hi⟩ := hs
      have h := congrArg ENNReal.toReal (laws i hi Set.univ MeasurableSet.univ)
      have hpos : 0 ≤ ∫ x in Set.Ico 0 (2*Real.pi), p (x-α) := integral_nonneg fun x => density_nn q (x-α)
      simpa only [Set.univ_inter, measure_univ, ENNReal.toReal_one, ENNReal.toReal_ofReal hpos] using h.symm
    obtain ⟨R,hR,hFour⟩ := squeezed_phase_first_moment q α hq hq'
    change q/2*(∫ x in Set.Ico 0 (2*Real.pi), p (x-α)) ≤ R at hR
    rw [hnorm,mul_one] at hR
    let M := unitphase α * (R:ℂ)
    have hM : (∫ x in Set.Ico 0 (2*Real.pi), unitphase x * (p (x-α):ℂ)) = M := hFour
    have hmeans (i : Fin m) (hi : i∈s) : (∫ x, Real.cos x ∂μ i)=M.re ∧ (∫ x, Real.sin x ∂μ i)=M.im := by
      have H := (phase_moments_of_density (μ i) p α (density_cont q hq hq') (density_nn q) (laws i hi)).2
      change (∫ x, Real.cos x ∂μ i) = (∫ x in Set.Ico 0 (2*Real.pi), unitphase x * (p (x-α):ℂ)).re ∧
        (∫ x, Real.sin x ∂μ i) = (∫ x in Set.Ico 0 (2*Real.pi), unitphase x * (p (x-α):ℂ)).im at H
      rwa [hM] at H
    have harcs (i : Fin m) (hi : i∈s) : (μ i).real L ≤ 1/2-2*e ∧ 1/2+2*e ≤ (μ i).real U :=
      arc_masses p (density_cont q hq hq') (density_periodic q) (density_nn q) (density_even q)
        (μ i) α h u d (2*e) (laws i hi) hh hh' hu hu' (density_peak hq hq' huq) (density_far hq hq' hh') hgap
    have htail := phase_empirical_tail μ s hs L U (meas_arc _ _) (meas_arc _ _) M.re M.im e he
      (fun i hi => (hmeans i hi).1) (fun i hi => (hmeans i hi).2) (fun i hi => (harcs i hi).1) (fun i hi => (harcs i hi).2)
    apply le_trans (le_trans (measure_mono ?_) htail)
    · simpa only [hsc] using hprob
    intro x hx hgood
    obtain ⟨hinit,hlo,hhi⟩ := hgood
    have hv : ‖Z x - (R:ℂ)*unitphase α‖ ≤ 2*e := by
      rw [Complex.re_add_im M] at hinit
      simpa only [Z,M,mul_comm (unitphase α) (R:ℂ)] using hinit
    obtain ⟨a,ha,hac⟩ := coarse_arg (Z x) R q e α he hstrong hR hv
    have hcard (B : Set ℝ) : (s.filter (fun i => x i∈B)).card = (Finset.univ.filter (fun j => Y x j ∈B)).card := by
      simp only [s,Finset.filter_map,Finset.card_map]; rfl
    rw [hsc,hcard] at hlo hhi
    have hLo : (Finset.univ.filter fun j => chart (α-h) (Y x j) < α-u).card ≤ n/2 := by
      have hs' : (Finset.univ.filter (fun j => Y x j∈L)).card ≤ n/2 := by
        have : 2*(Finset.univ.filter (fun j => Y x j∈L)).card < n := by exact_mod_cast (show 2*((Finset.univ.filter (fun j => Y x j∈L)).card:ℝ)<n by linarith)
        omega
      simpa only [L,arc,chart, Set.mem_setOf_eq,sub_right_comm α h Real.pi] using hs'
    have hHi : n/2 < (Finset.univ.filter fun j => chart (α+h) (Y x j) < α+u).card := by
      have hs' : n/2 < (Finset.univ.filter (fun j => Y x j∈U)).card := by
        have : n < 2*(Finset.univ.filter (fun j => Y x j∈U)).card := by exact_mod_cast (show (n:ℝ)<2*((Finset.univ.filter (fun j => Y x j∈U)).card:ℝ) by linarith)
        omega
      simpa only [U,arc,chart,Set.mem_setOf_eq,show α+h-Real.pi = α-Real.pi+h by ring] using hs'
    have hz := trained_error hn (Y x) a α (Z x).arg h u hu ha hac hLo hHi
    have htheta : α/2 = θ := by dsimp [α]; ring
    rw [htheta] at hz
    change η < Real.sinh (2*r)*|Real.sin (θ-trained_angle (Z x).arg (Y x))| at hx
    rw [sinh_from_q] at hx
    have hnon : 0 ≤ 2*q/(1-q^2) := div_nonneg (by positivity) (by nlinarith [mul_self_le_mul_self hq hq'.le])
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hz hnon).trans hrisk)) hx
  · have hemp : {x | η < Real.sinh (2*r)*|Real.sin (θ-angle x)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      change η < Real.sinh (2*r)*|Real.sin (θ-angle x)| at hx
      rw [sinh_from_q] at hx
      exact (not_lt_of_ge (phase_weak_scale η q _ hη hη4 hq hq' (lt_of_not_ge hstrong) (abs_nonneg _) (Real.abs_sin_le_one _))) hx
    rw [hemp,measure_empty]; exact zero_le
