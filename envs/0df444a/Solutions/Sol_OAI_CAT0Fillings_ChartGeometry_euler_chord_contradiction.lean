-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:05:54.806535+00:00
-- url     : https://prove2.me/submissions/8739045c-f6e5-4dcc-a695-c1e83e3733fa

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_chord_scalar_average
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_opposite_all_center

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma beta_integrand_coe (a b x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    ((x^(a-1)*(1-x)^(b-1):ℝ):ℂ) =
      (x:ℂ)^((a:ℂ)-1)*(1-(x:ℂ))^((b:ℂ)-1) := by
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hx.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  push_cast
  rfl

lemma beta_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0:ℝ)..1,x^(a-1)*(1-x)^(b-1)) = Real.Gamma a*Real.Gamma b/Real.Gamma (a+b) := by
  have he : Complex.betaIntegral (a:ℂ) (b:ℂ) =
      ((∫ x in (0:ℝ)..1,x^(a-1)*(1-x)^(b-1):ℝ):ℂ) := by
    rw [Complex.betaIntegral,←intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro x hx
    exact (beta_integrand_coe a b x hx).symm
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a:ℂ)) (t := (b:ℂ)) ha hb
  rw [he,←Complex.ofReal_add,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal,
    ←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.ofReal_inj] at hc
  apply (eq_div_iff (ne_of_gt (Real.Gamma_pos_of_pos (add_pos ha hb)))).mpr
  linarith [hc]

end CAT0Fillings.RadialSobolev
end

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma betaRadius_deriv (r : ℝ) :
    HasDerivAt betaRadius (2*r/(1+r^2)^2) r := by
  have h : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  have hd := ((hasDerivAt_id r).pow 2).div
    ((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)) h
  dsimp only [id_eq, Pi.pow_apply, Pi.add_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, zero_add, mul_one] at hd
  convert hd using 1 <;> first | rfl | ring

lemma betaRadius_mono : MonotoneOn betaRadius (Ioi 0) := by
  intro x hx y hy hxy
  dsimp [betaRadius]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+x^2) (by positivity : 0 < 1+y^2)).mpr
  have hsq : x^2 ≤ y^2 := sq_le_sq₀ (le_of_lt hx) (le_of_lt hy) |>.mpr hxy
  nlinarith

lemma betaRadius_image : betaRadius '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hd : 0 < 1+r^2 := by positivity
    exact ⟨div_pos (sq_pos_of_pos hr) hd, (div_lt_one hd).mpr (by linarith)⟩
  · intro ht
    have hd : 0 < 1-t := sub_pos.mpr ht.2
    refine ⟨Real.sqrt (t/(1-t)), Real.sqrt_pos.2 (div_pos ht.1 hd), ?_⟩
    dsimp [betaRadius]
    rw [Real.sq_sqrt (div_nonneg ht.1.le hd.le)]
    field_simp
    ring

lemma bubble_substitution_algebra {a b r : ℝ} (hr : 0 < r) :
    (2*r/(1+r^2)^2)*((betaRadius r)^(a-1)*(1-betaRadius r)^(b-1)) =
      2*(r^(2*a-1)*(1+r^2)^(-(a+b))) := by
  have H : 0 < 1+r^2 := by positivity
  have he : 1-betaRadius r = 1/(1+r^2) := by dsimp [betaRadius]; field_simp; ring
  rw [he, betaRadius, Real.div_rpow (sq_nonneg _) H.le,
    Real.div_rpow zero_le_one H.le, Real.one_rpow]
  have he2 : (r^2)^(a-1) = r^(2*(a-1)) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hr.le]
    norm_num
  rw [he2]
  rw [div_mul_div_comm]
  have hnum : r*r^(2*(a-1)) = r^(2*a-1) := by
    conv_lhs => lhs; rw [←Real.rpow_one r]
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hden : (1+r^2)^2*((1+r^2)^(a-1)*(1+r^2)^(b-1)) = (1+r^2)^(a+b) := by
    rw [←Real.rpow_natCast, ←Real.rpow_add H, ←Real.rpow_add H]
    congr 1
    ring
  calc
    _ = 2*(r*r^(2*(a-1)))/((1+r^2)^2*((1+r^2)^(a-1)*(1+r^2)^(b-1))) := by
      field_simp
    _ = 2*r^(2*a-1)/(1+r^2)^(a+b) := by rw [hnum,hden]
    _ = _ := by rw [Real.rpow_neg H.le]; ring

lemma bubble_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ r in Ioi (0:ℝ), r^(2*a-1)*(1+r^2)^(-(a+b))) =
       Real.Gamma a*Real.Gamma b/(2*Real.Gamma (a+b)) := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn
    measurableSet_Ioi (fun r _ => (betaRadius_deriv r).hasDerivWithinAt)
    betaRadius_mono (fun t : ℝ => t^(a-1)*(1-t)^(b-1))
  rw [betaRadius_image] at h
  have he : (∫ r in Ioi (0:ℝ), (2*r/(1+r^2)^2) •
      ((betaRadius r)^(a-1)*(1-betaRadius r)^(b-1))) =
      2*∫ r in Ioi (0:ℝ), r^(2*a-1)*(1+r^2)^(-(a+b)) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact bubble_substitution_algebra hr
  rw [he] at h
  have hb' := beta_integral ha hb
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hb'
  rw [hb'] at h
  calc
    _ = (Real.Gamma a*Real.Gamma b/Real.Gamma (a+b))/2 := by linarith
    _ = _ := by ring

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma bubble_power_p {n : ℕ} (hn : 2 < n) (r : ℝ) :
    (bubble n r)^(sobolevP n) = (1+r^2)^(-(n:ℝ)) := by
  have h : (n:ℝ)-2 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [bubble, ←Real.rpow_mul (by positivity)]
  congr 1
  dsimp [sobolevP]
  field_simp

lemma bubble_power_q {n : ℕ} (hn : 2 < n) (r : ℝ) :
    (bubble n r)^(sobolevQ n) = (1+r^2)^(1-(n:ℝ)) := by
  have h : (n:ℝ)-2 ≠ 0 := by exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [bubble, ←Real.rpow_mul (by positivity)]
  congr 1
  dsimp [sobolevQ]
  field_simp
  ring

lemma bubbleMoment_algebra {n : ℕ} (hn : 2 < n) {r : ℝ} (hr : 0 < r) :
    r^(n-1)*(bubble n r)^(sobolevP n) = r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+(n:ℝ)/2)) ∧
    r^(n-1)*(bubble n r)^(sobolevQ n) = r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+((n:ℝ)/2-1))) ∧
    r^(n-1)*(bubble n r)^(sobolevP n)*r^2 =
      r^(2*((n:ℝ)/2+1)-1)*(1+r^2)^(-(((n:ℝ)/2+1)+((n:ℝ)/2-1))) := by
  have h1 : 1 ≤ n := by omega
  rw [bubble_power_p hn, bubble_power_q hn, ←Real.rpow_natCast,
    Nat.cast_sub h1, Nat.cast_one]
  refine ⟨?_, ?_, ?_⟩
  · congr 2 <;> ring
  · congr 2 <;> ring
  · calc
      _ = (r^((n:ℝ)-1)*r^(2:ℝ))*(1+r^2)^(-(n:ℝ)) := by rw [Real.rpow_two]; ring
      _ = _ := by rw [←Real.rpow_add hr]; congr 2 <;> ring

lemma bubble_moments {n : ℕ} (hn : 2 < n) :
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevP n)) = bubbleMass n ∧
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevQ n)) = sobolevQ n*bubbleMass n ∧
    (∫ r in Ioi (0:ℝ),r^(n-1)*(bubble n r)^(sobolevP n)*r^2) =
      (n:ℝ)/(n-2)*bubbleMass n := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  have h0 : (0:ℝ) < n/2 := by linarith
  have h1 : (0:ℝ) < n/2-1 := by linarith
  have he0 : (n:ℝ)/2+(n:ℝ)/2 = n := by ring
  have he1 : (n:ℝ)/2+((n:ℝ)/2-1) = (n:ℝ)-1 := by ring
  have he2 : ((n:ℝ)/2+1)+((n:ℝ)/2-1) = n := by ring
  have G1 : Real.Gamma ((n:ℝ)/2) = ((n:ℝ)/2-1)*Real.Gamma ((n:ℝ)/2-1) := by
    convert Real.Gamma_add_one h1.ne' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have G2 : Real.Gamma (n:ℝ) = ((n:ℝ)-1)*Real.Gamma ((n:ℝ)-1) := by
    convert Real.Gamma_add_one (by linarith : (n:ℝ)-1 ≠ 0) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have G3 := Real.Gamma_add_one h0.ne'
  have d1 : Real.Gamma ((n:ℝ)-1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have d2 : (n:ℝ)-2 ≠ 0 := by linarith
  have d3 : (n:ℝ)-1 ≠ 0 := by linarith
  refine ⟨?_,?_,?_⟩
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+(n:ℝ)/2)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).1)
      _ = bubbleMass n := by rw [bubble_integral h0 h0,he0]; simp only [bubbleMass,pow_two]
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2)-1)*(1+r^2)^(-((n:ℝ)/2+((n:ℝ)/2-1))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).2.1)
      _ = sobolevQ n*bubbleMass n := by
        rw [bubble_integral h0 h1,he1]
        dsimp [sobolevQ,bubbleMass]
        rw [G1,G2]
        field_simp [d1,d2,d3]
  · calc
      _ = ∫ r in Ioi (0:ℝ),r^(2*((n:ℝ)/2+1)-1)*(1+r^2)^(-(((n:ℝ)/2+1)+((n:ℝ)/2-1))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun r hr => (bubbleMoment_algebra hn hr).2.2)
      _ = (n:ℝ)/(n-2)*bubbleMass n := by
        rw [bubble_integral (by linarith : (0:ℝ) < n/2+1) h1,he2,G3]
        dsimp [bubbleMass]
        rw [G1]
        field_simp [d1,d2,d3]

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Euclidean
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma omega_gamma {k : ℕ} (hk : 0 < k) :
    omega k = Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2+1) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [omega, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

lemma polar_constant_gamma {n : ℕ} (hn : 0 < n) :
    (n:ℝ)*omega n = 2*Real.sqrt Real.pi^n/Real.Gamma ((n:ℝ)/2) := by
  have h : (0:ℝ) < n := by exact_mod_cast hn
  rw [omega_gamma hn,Real.Gamma_add_one (by positivity : (n:ℝ)/2 ≠ 0)]
  field_simp

lemma sphereArea_gamma (n : ℕ) :
    sphereArea n = 2*Real.sqrt Real.pi^(n+1)/Real.Gamma (((n:ℝ)+1)/2) := by
  have hh := polar_constant_gamma (Nat.succ_pos n)
  simpa [sphereArea,Nat.cast_add,Nat.cast_one] using hh

lemma bubble_mass_sphere {n : ℕ} (hn : 2 < n) :
    (2:ℝ)^n*((n:ℝ)*omega n*bubbleMass n) = sphereArea n := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  have G : Real.Gamma ((n:ℝ)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have H : Real.Gamma ((n:ℝ)) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have J : Real.Gamma (((n:ℝ)+1)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hd := Real.Gamma_mul_Gamma_add_half ((n:ℝ)/2)
  have e1 : (n:ℝ)/2+1/2 = ((n:ℝ)+1)/2 := by ring
  have e2 : 2*((n:ℝ)/2) = n := by ring
  rw [e1,e2, Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one,Real.rpow_natCast] at hd
  rw [polar_constant_gamma (by omega),sphereArea_gamma,bubbleMass,pow_succ]
  apply (eq_div_iff J).mpr
  field_simp [G,H] at *
  have he := congrArg (fun x : ℝ => x*Real.sqrt Real.pi^n) hd
  rw [pow_succ]
  nlinarith [he]

end CAT0Fillings.RadialSobolev
end

section
open Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma integral_euclidean_bubble {n : ℕ} (hn : 2 < n) :
    (∫ x : Euc n, (1+‖x‖^2)^(-(n:ℝ))) = sphereArea n/(2:ℝ)^n := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  rw [integral_fun_norm_addHaar (volume : Measure (Euc n)) (fun r : ℝ => (1+r^2)^(-(n:ℝ)))]
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,nsmul_eq_mul,←bubble_power_p hn]
  rw [(bubble_moments hn).1]
  have hc := bubble_mass_sphere hn
  change (n:ℝ)*(omega n*bubbleMass n) = _
  apply (eq_div_iff (by positivity)).mpr
  nlinarith [hc]
end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Fubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings

theorem secant_lower_bound
    {h : ℝ → ℝ} {d : ℝ}
    (hdiff : ∀ x > 0, DifferentiableAt ℝ h x)
    (hineq : ∀ x > 0, h x - 1 ≤ x * deriv h x)
    (hlim : Tendsto (fun x => (h x - 1) / x) (𝓝[>] (0 : ℝ)) (𝓝 d))
    {a : ℝ} (ha : 0 < a) : 1 + d * a ≤ h a := by
  let f : ℝ → ℝ := fun x => (h x - 1) / x
  have hfderiv : ∀ x > 0,
      HasDerivAt f ((deriv h x * x - (h x - 1)) / x ^ 2) x := by
    intro x hx
    convert
      (((hdiff x hx).hasDerivAt.sub_const 1).div (hasDerivAt_id x) (ne_of_gt hx)) using 1 <;>
        first | rfl | simp
  have hfmono : MonotoneOn f (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx
      exact (hfderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfderiv x (by simpa using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa using hx
      rw [(hfderiv x hx').deriv]
      apply div_nonneg _ (sq_nonneg x)
      have := hineq x hx'
      nlinarith
  have hb : d ≤ f a := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with x hx hxa
    exact hfmono hx ha (le_of_lt hxa)
  dsimp [f] at hb
  have := (le_div_iff₀ ha).mp hb
  linarith

theorem chord_scalar_bound
    {J G : ℝ → ℝ} {q D : ℝ} (hq : 0 < q) (hD : 0 ≤ D)
    (hG0 : G 0 = 1)
    (hGderiv0 : HasDerivWithinAt G (-q * D) (Ici 0) 0)
    (hGpos : ∀ a > 0, 0 < G a)
    (hJnonneg : ∀ a > 0, 0 ≤ J a)
    (hGdiff : ∀ a > 0, DifferentiableAt ℝ G a)
    (hJle : ∀ a > 0, J a ^ (q / (q + 1)) ≤ G a)
    (hODE : ∀ a > 0, a * deriv G a = q * (J a - G a))
    {a : ℝ} (ha : 0 < a) : J a ≤ (1 + D * a) ^ (-(q + 1)) := by
  let h : ℝ → ℝ := fun x => G x ^ (-1 / q)
  have hqp : 0 < q + 1 := by linarith
  have hGI {x : ℝ} (hx : 0 < x) :
      J x * G x ^ (-((q + 1) / q)) ≤ 1 := by
    have hj : J x ≤ G x ^ ((q + 1) / q) := by
      have ht := Real.rpow_le_rpow (Real.rpow_nonneg (hJnonneg x hx) _)
        (hJle x hx) (le_of_lt (div_pos hqp hq))
      rw [← Real.rpow_mul (hJnonneg x hx)] at ht
      have he : q / (q + 1) * ((q + 1) / q) = 1 := by
        field_simp
      simpa [he] using ht
    rw [Real.rpow_neg (le_of_lt (hGpos x hx))]
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (hGpos x hx) _)).mpr (by simpa using hj)
  have hderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt h (deriv G x * (-1 / q) * G x ^ (-1 / q - 1)) x := by
    exact (hGdiff x hx).hasDerivAt.rpow_const (Or.inl (ne_of_gt (hGpos x hx)))
  have hexp : -1 / q - 1 = -((q + 1) / q) := by field_simp; ring
  have hineq : ∀ x > 0, h x - 1 ≤ x * deriv h x := by
    intro x hx
    rw [(hderiv hx).deriv, hexp]
    have hp : G x * G x ^ (-((q + 1) / q)) = h x := by
      change G x * G x ^ (-((q + 1) / q)) = G x ^ (-1 / q)
      conv_lhs => lhs; rw [← Real.rpow_one (G x)]
      rw [← Real.rpow_add (hGpos x hx)]
      congr 1
      field_simp
      ring
    have heq : x * (deriv G x * (-1 / q) * G x ^ (-((q + 1) / q))) =
        h x - J x * G x ^ (-((q + 1) / q)) := by
      calc
        _ = (x * deriv G x) * (-1 / q) * G x ^ (-((q + 1) / q)) := by ring
        _ = q * (J x - G x) * (-1 / q) * G x ^ (-((q + 1) / q)) := by rw [hODE x hx]
        _ = G x * G x ^ (-((q + 1) / q)) -
            J x * G x ^ (-((q + 1) / q)) := by field_simp; ring
        _ = _ := by rw [hp]
    rw [heq]
    linarith [hGI hx]
  have hd0 : HasDerivWithinAt h D (Ici 0) 0 := by
    have ht := hGderiv0.rpow_const (p := -1 / q) (Or.inl (by rw [hG0]; norm_num))
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    simp [hG0]
    field_simp
  have hh0 : h 0 = 1 := by simp [h, hG0]
  have hlim : Tendsto (fun x => (h x - 1) / x) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd0
    have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
    change Tendsto (fun x => slope h 0 x) _ _ at ht
    simpa only [hs, slope_def_field, hh0, sub_zero] using ht
  have hbound : 1 + D * a ≤ h a :=
    secant_lower_bound (fun x hx => (hderiv hx).differentiableAt) hineq hlim ha
  have hj : J a ≤ G a ^ ((q + 1) / q) := by
    have ht := Real.rpow_le_rpow (Real.rpow_nonneg (hJnonneg a ha) _)
      (hJle a ha) (le_of_lt (div_pos hqp hq))
    rw [← Real.rpow_mul (hJnonneg a ha)] at ht
    have he : q / (q + 1) * ((q + 1) / q) = 1 := by field_simp
    simpa [he] using ht
  have hepower : G a ^ ((q + 1) / q) = h a ^ (-(q + 1)) := by
    dsimp [h]
    rw [← Real.rpow_mul (le_of_lt (hGpos a ha))]
    congr 1
    ring
  rw [hepower] at hj
  exact hj.trans (Real.rpow_le_rpow_of_nonpos (by positivity) hbound (by linarith))

namespace ChordTransform

open MeasureTheory

lemma kernel_pos {n b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) : 0 < kernel n b a :=
  Real.rpow_pos_of_pos (by positivity) _

lemma kernel_le_one {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    kernel n b a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)

lemma kernel_hasDerivAt {n b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) :
    HasDerivAt (kernel n b) (-n*b*(1+a*b)^(-n-1)) a := by
  have h := (((hasDerivAt_id a).mul_const b).const_add 1).rpow_const
    (p := -n) (Or.inl (by positivity : 1+a*b ≠ 0))
  refine h.congr_deriv (Eq.symm ?_)
  · dsimp
    ring

lemma kernel_deriv_bound {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    ‖-n*b*(1+a*b)^(-n-1)‖ ≤ n*b := by
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith : 1 ≤ 1+a*b)
    (show -n-1 ≤ 0 by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg hn,
    abs_of_nonneg hb, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (mul_nonneg hn hb)

lemma kernel_lipschitzOn {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) :
    LipschitzOnWith ⟨n*b, mul_nonneg hn hb⟩ (kernel n b) (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun a ha => (kernel_hasDerivAt hb ha).hasDerivWithinAt)
  intro a ha
  exact kernel_deriv_bound hn hb ha

lemma kernel_slope_bound {n b a : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (ha : 0 < a) :
    ‖(kernel n b a - 1) / a‖ ≤ n*b := by
  have h := (kernel_lipschitzOn hn hb).dist_le_mul a ha.le 0 (by simp)
  simp only [kernel, zero_mul, add_zero, Real.one_rpow, Real.dist_eq,
    sub_zero, abs_of_pos ha] at h
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr h

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma kernel_aestronglyMeasurable {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (n a : ℝ) : AEStronglyMeasurable (fun x => kernel n (b x) a) μ :=
  ((hb.aemeasurable.const_mul a).const_add 1 |>.pow_const (-n)).aestronglyMeasurable

lemma kernel_integrable {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) :
    Integrable (fun x => kernel n (b x) a) μ := by
  apply (integrable_const (1 : ℝ)).mono' (kernel_aestronglyMeasurable μ hb n a)
  filter_upwards [hb0] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hx ha)]
  exact kernel_le_one hn hx ha

lemma transform_zero (n : ℝ) (b : α → ℝ) : transform μ n b 0 = 1 := by
  simp only [transform, kernel, zero_mul, add_zero, Real.one_rpow, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]

omit [IsProbabilityMeasure μ] in
lemma transform_nonneg {b : α → ℝ} (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ}
    (ha : 0 ≤ a) : 0 ≤ transform μ n b a := by
  exact integral_nonneg_of_ae (hb0.mono fun _ hx => (kernel_pos hx ha).le)

lemma transform_pos {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n a : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) :
    0 < transform μ n b a := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (hb0.mono fun _ hx => (kernel_pos hx ha).le) (kernel_integrable μ hb hb0 hn ha)).mpr
  have heq : Function.support (fun x => kernel n (b x) a) =ᵐ[μ] univ := by
    filter_upwards [hb0] with x hx
    apply propext
    change (kernel n (b x) a ≠ 0) ↔ True
    exact iff_true_intro (kernel_pos hx ha).ne'
  rw [measure_congr heq, measure_univ]
  norm_num

lemma transform_lipschitzOn {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 0 ≤ n) :
    LipschitzOnWith ⟨n * ∫ x, b x ∂μ, mul_nonneg hn (integral_nonneg_of_ae hb0)⟩
      (transform μ n b) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha c hc
  have hia := kernel_integrable μ hb.aestronglyMeasurable hb0 hn ha
  have hic := kernel_integrable μ hb.aestronglyMeasurable hb0 hn hc
  change |(∫ x, kernel n (b x) a ∂μ) - ∫ x, kernel n (b x) c ∂μ| ≤ _
  rw [← integral_sub hia hic, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, ‖kernel n (b x) a - kernel n (b x) c‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, n * b x * dist a c ∂μ := by
      apply integral_mono_ae (hia.sub hic).norm ((hb.const_mul n).mul_const _)
      filter_upwards [hb0] with x hx
      exact (kernel_lipschitzOn hn hx).dist_le_mul a ha c hc
    _ = (n * ∫ x, b x ∂μ) * dist a c := by
      rw [integral_mul_const, integral_const_mul]

lemma transform_hasDerivWithinAt_zero {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 0 ≤ n) :
    HasDerivWithinAt (transform μ n b) (-n * ∫ x, b x ∂μ) (Ici 0) 0 := by
  have hlim : Tendsto (fun t => ∫ x, (kernel n (b x) t - 1) / t ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, -n*b x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => n*b x)
    · exact Eventually.of_forall fun t =>
        (((kernel_aestronglyMeasurable μ hb.aestronglyMeasurable n t).aemeasurable.sub_const 1).div_const t).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hb0.mono fun x hx => kernel_slope_bound hn hx ht
    · exact hb.const_mul n
    · filter_upwards [hb0] with x hx
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp
        ((kernel_hasDerivAt (n := n) hx (le_refl (0 : ℝ))).hasDerivWithinAt (s := Ici 0))
      have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (kernel n (b x)) 0 t) _ _ at ht
      simpa only [hs, slope_def_field, kernel, zero_mul, add_zero, Real.one_rpow,
        mul_one, sub_zero] using ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  have hfg : (fun t => ∫ x, (kernel n (b x) t - 1) / t ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      slope (transform μ n b) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [integral_div, integral_sub (kernel_integrable μ hb.aestronglyMeasurable hb0 hn ht.le)
      (integrable_const 1), integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    rw [slope_def_field, transform_zero, sub_zero]
    rfl
  simpa only [integral_const_mul] using (hlim.congr' hfg)

end ChordTransform

end CAT0Fillings

namespace CAT0Fillings.ChordAverage

lemma integrable_weight {q : ℝ} (hq : 0 < q) (a : ℝ) :
    IntervalIntegrable (fun u : ℝ => u^(q-1)) volume 0 a :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

lemma weight_integral {q : ℝ} (hq : 0 < q) :
    ∫ u in (0 : ℝ)..1, u^(q-1) = 1/q := by
  rw [integral_rpow (Or.inl (by linarith))]
  simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hq.ne', sub_zero]

lemma integrable_weighted {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun t => J t * t^(q-1)) volume 0 a := by
  apply (integrable_weight hq a).continuousOn_mul
  rw [uIcc_of_le ha]
  exact hJ.mono fun _ hx => hx.1

lemma integrable_average {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (fun u => J (a*u) * u^(q-1)) volume 0 1 := by
  apply (integrable_weight hq 1).continuousOn_mul
  apply hJ.comp (continuous_const.mul continuous_id).continuousOn
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  exact mul_nonneg ha hu.1

lemma average_zero {q : ℝ} (hq : 0 < q) (J : ℝ → ℝ) :
    average q J 0 = J 0 := by
  simp only [average, zero_mul, intervalIntegral.integral_const_mul, weight_integral hq]
  field_simp

lemma average_rescale {q a : ℝ} (ha : 0 < a) (J : ℝ → ℝ) :
    average q J a = q * a^(-q) * ∫ t in (0 : ℝ)..a, J t * t^(q-1) := by
  have hc := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun t => J t * t^(q-1)) ha.ne'
  have he : (∫ u in (0 : ℝ)..1, J (a*u) * (a*u)^(q-1)) =
      a^(q-1) * ∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    dsimp only
    rw [Real.mul_rpow ha.le hu.1]
    ring
  rw [he, mul_zero, mul_one, smul_eq_mul] at hc
  have ha0 : a^(q-1) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  have hp : a^(-q) = a⁻¹ / a^(q-1) := by
    rw [Real.rpow_sub ha, Real.rpow_one, Real.rpow_neg ha.le]
    field_simp
  rw [average, hp]
  have hc' : (∫ u in (0 : ℝ)..1, J (a*u) * u^(q-1)) =
      (a⁻¹ * ∫ t in (0 : ℝ)..a, J t * t^(q-1)) / a^(q-1) := by
    apply (eq_div_iff ha0).mpr
    rwa [mul_comm]
  rw [hc']
  ring

lemma weighted_continuousOn {J : ℝ → ℝ} (hJ : ContinuousOn J (Ici 0)) (q : ℝ) :
    ContinuousOn (fun t => J t * t^(q-1)) (Ioi 0) :=
  (hJ.mono Ioi_subset_Ici_self).mul
    (continuousOn_id.rpow_const fun _ ht => Or.inl ht.ne')

lemma average_hasDerivAt {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (average q J) (q/a * (J a - average q J a)) a := by
  let F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, J u * u^(q-1)
  have hc := weighted_continuousOn hJ q
  have hF : HasDerivAt F (J a * a^(q-1)) a :=
    intervalIntegral.integral_hasDerivAt_right (integrable_weighted hq hJ ha.le)
      (hc.stronglyMeasurableAtFilter isOpen_Ioi a ha)
      (hc.continuousAt (Ioi_mem_nhds ha))
  have hd := (((hasDerivAt_id a).rpow_const (p := -q) (Or.inl ha.ne')).const_mul q).mul hF
  have he : average q J =ᶠ[𝓝 a] (fun t => q * t^(-q) * F t) := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    exact average_rescale ht J
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp only [id_eq]
  rw [average_rescale ha J]
  change q * (1 * -q * a^(-q-1)) * F a + q * a^(-q) * (J a * a^(q-1)) = _
  have hp : a^(-q-1) = a^(-q)/a := by rw [Real.rpow_sub ha, Real.rpow_one]
  have hp' : a^(-q) * a^(q-1) = a⁻¹ := by
    rw [← Real.rpow_add ha]
    ring_nf
    exact Real.rpow_neg_one a
  rw [hp]
  calc
    _ = -(q^2/a) * (a^(-q) * F a) + q * J a * (a^(-q) * a^(q-1)) := by ring
    _ = _ := by rw [hp']; simp only [F]; ring

lemma average_ode {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) {a : ℝ} (ha : 0 < a) :
    a * deriv (average q J) a = q * (J a - average q J a) := by
  rw [(average_hasDerivAt hq hJ ha).deriv]
  field_simp

lemma average_pos {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    (hJ : ContinuousOn J (Ici 0)) (hpos : ∀ t ≥ 0, 0 < J t)
    {a : ℝ} (ha : 0 ≤ a) : 0 < average q J a := by
  apply mul_pos hq
  have hfi := integrable_average hq hJ ha
  have hpos' : ∀ u ∈ Ioc (0 : ℝ) 1, 0 < J (a*u)*u^(q-1) := by
    intro u hu
    exact mul_pos (hpos _ (mul_nonneg ha hu.1.le)) (Real.rpow_pos_of_pos hu.1 _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun u => J (a*u)*u^(q-1)) := by
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun _ hu => (hpos' _ hu).le
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg hfi).mpr
  refine ⟨zero_lt_one, ?_⟩
  have he : Function.support (fun u => J (a*u)*u^(q-1)) ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 := by
    apply inter_eq_right.mpr
    intro u hu
    exact (hpos' u hu).ne'
  rw [he, Real.volume_Ioc]
  norm_num

lemma mul_weight {q u : ℝ} (hu : 0 < u) : u * u^(q-1) = u^q := by
  conv_lhs => lhs; rw [← Real.rpow_one u]
  rw [← Real.rpow_add hu]
  congr 1
  ring

lemma average_hasDerivWithinAt_zero {q : ℝ} (hq : 0 < q) {J : ℝ → ℝ}
    {K : ℝ≥0} (hLip : LipschitzOnWith K J (Ici 0)) {d : ℝ}
    (hd : HasDerivWithinAt J d (Ici 0) 0) :
    HasDerivWithinAt (average q J) (q/(q+1)*d) (Ici 0) 0 := by
  have hJ := hLip.continuousOn
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hi : ∀ t ≥ 0, Integrable (fun u => ((J (t*u)-J 0)/t)*u^(q-1)) μ := by
    intro t ht
    have h := ((integrable_average hq hJ ht).1.sub
      ((integrable_weight hq 1).1.const_mul (J 0))).div_const t
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp only [Pi.sub_apply]
    ring
  have hu : ∀ᵐ u ∂μ, u ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hlim : Tendsto (fun t => ∫ u, ((J (t*u)-J 0)/t)*u^(q-1) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, d*u^q ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => (K : ℝ)*u^q)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hi t ht.le).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (0 : ℝ) < t at ht
      filter_upwards [hu] with u hu
      have hb := hLip.dist_le_mul (t*u) (mul_pos ht hu.1).le 0 (by simp)
      simp only [Real.dist_eq, sub_zero, abs_of_pos (mul_pos ht hu.1)] at hb
      have hdiv : ‖(J (t*u)-J 0)/t‖ ≤ (K : ℝ)*u := by
        simp only [norm_div, Real.norm_eq_abs, abs_of_pos ht]
        apply (div_le_iff₀ ht).mpr
        nlinarith
      rw [norm_mul]
      rw [Real.norm_eq_abs (u ^ (q-1)), abs_of_nonneg (Real.rpow_nonneg hu.1.le _)]
      calc
        _ ≤ ((K : ℝ)*u)*u^(q-1) := mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hu.1.le _)
        _ = (K : ℝ)*u^q := by rw [mul_assoc, mul_weight hu.1]
    · exact ((intervalIntegral.intervalIntegrable_rpow' (show -1 < q by linarith)
        (a := 0) (b := 1)).1.const_mul (K : ℝ))
    · filter_upwards [hu] with u hu
      have hd' : HasDerivWithinAt (fun t => J (t*u)) (d*u) (Ici 0) 0 := by
        have hd0 : HasDerivWithinAt J d (Ici 0) (0*u) := by simpa only [zero_mul] using hd
        have hdu : HasDerivWithinAt (fun t : ℝ => t*u) u (Ici 0) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).hasDerivWithinAt (s := Ici 0)
        exact hd0.comp 0 hdu (fun t ht => mul_nonneg ht hu.1.le)
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd'
      have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (fun s => J (s*u)) 0 t) _ _ at ht
      simp only [hs, slope_def_field, zero_mul, sub_zero] at ht
      convert ht.mul_const (u^(q-1)) using 1
      all_goals try with_reducible_and_instances rfl
      rw [mul_assoc, mul_weight hu.1]
  have heq (t : ℝ) (ht : 0 < t) :
      q * (∫ u, ((J (t*u)-J 0)/t)*u^(q-1) ∂μ) =
        (average q J t - J 0)/t := by
    have hi1 : Integrable (fun u => J (t*u)*u^(q-1)) μ := (integrable_average hq hJ ht.le).1
    have hi0 : Integrable (fun u : ℝ => J 0*u^(q-1)) μ := (integrable_weight hq 1).1.const_mul _
    have hf : (fun u => ((J (t*u)-J 0)/t)*u^(q-1)) =
        (fun u => (J (t*u)*u^(q-1)-J 0*u^(q-1))/t) := by funext u; ring
    rw [hf, integral_div, integral_sub hi1 hi0, integral_const_mul]
    have hw : (∫ u : ℝ, u^(q-1) ∂μ) = 1/q := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      exact weight_integral hq
    rw [hw]
    have hj : (∫ u, J (t*u)*u^(q-1) ∂μ) =
        ∫ u in (0 : ℝ)..1, J (t*u)*u^(q-1) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    rw [hj, average]
    field_simp
  have hdlim := hlim.const_mul q
  have hlimval : q * (∫ u, d*u^q ∂μ) = q/(q+1)*d := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (show -1 < q by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (show q+1 ≠ 0 by linarith), sub_zero]
    ring
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0 : ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  rw [hlimval] at hdlim
  apply hdlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [heq t ht, slope_def_field, average_zero hq, sub_zero]

end CAT0Fillings.ChordAverage

namespace CAT0Fillings.ChordTransform
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

theorem distribution_bound {b : α → ℝ} (hb : Integrable b μ)
    (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) {n : ℝ} (hn : 2 < n)
    (hvar : ∀ a > 0, (transform μ n b a)^((n-2)/n) ≤
      ChordAverage.average ((n-2)/2) (transform μ n b) a)
    {a : ℝ} (ha : 0 ≤ a) :
    transform μ n b a ≤ (1 + 2 * (∫ x, b x ∂μ) * a)^(-n/2) := by
  by_cases ha0 : a = 0
  · subst a
    simp [transform_zero]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let q := (n-2)/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hn0 : 0 ≤ n := by linarith
  have hnne : n ≠ 0 := by linarith
  have hqp : q+1 ≠ 0 := by linarith
  have hnq : n = 2*(q+1) := by dsimp [q]; ring
  have hmean : 0 ≤ ∫ x, b x ∂μ := integral_nonneg_of_ae hb0
  have hlip := transform_lipschitzOn μ hb hb0 hn0
  have hc := hlip.continuousOn
  have hG0 : ChordAverage.average q (transform μ n b) 0 = 1 := by
    rw [ChordAverage.average_zero hq, transform_zero]
  have hd0 := ChordAverage.average_hasDerivWithinAt_zero hq hlip
    (transform_hasDerivWithinAt_zero μ hb hb0 hn0)
  have hd0' : HasDerivWithinAt (ChordAverage.average q (transform μ n b))
      (-q * (2 * ∫ x, b x ∂μ)) (Ici 0) 0 := by
    convert hd0 using 1
    all_goals try with_reducible_and_instances rfl
    rw [hnq]
    field_simp
  have hde : -(q+1) = -n/2 := by dsimp [q]; ring
  rw [← hde]
  apply chord_scalar_bound hq (mul_nonneg (by norm_num) hmean) hG0 hd0'
    (fun t ht => ChordAverage.average_pos hq hc (fun u hu => transform_pos μ
      hb.aestronglyMeasurable hb0 hn0 hu) ht.le)
    (fun t ht => transform_nonneg μ hb0 ht.le)
    (fun t ht => (ChordAverage.average_hasDerivAt hq hc ht).differentiableAt) ?_
    (fun t ht => ChordAverage.average_ode hq hc ht) ha'
  intro t ht
  have he : q/(q+1) = (n-2)/n := by
    apply (div_eq_div_iff hqp hnne).mpr
    dsimp [q]
    ring
  rw [he]
  exact hvar t ht

end CAT0Fillings.ChordTransform

open Set Filter MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_NonnegativeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
lemma isProbability (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (hW : 0 < total μ ρ) :
    IsProbabilityMeasure (probability μ ρ) := by
  constructor
  rw [probability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (hρ.mono fun x hx => div_nonneg hx hW.le)]
  rw [integral_div]
  change ENNReal.ofReal (total μ ρ / total μ ρ) = 1
  rw [div_self hW.ne',ENNReal.ofReal_one]
lemma integral_probability (hi : AEStronglyMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ)
    (hW : 0 < total μ ρ) (f : α → ℝ) :
    (∫ x, f x ∂probability μ ρ) = (∫ x, ρ x*f x ∂μ)/total μ ρ := by
  rw [probability,integral_withDensity_eq_integral_toReal_smul₀
    (hi.aemeasurable.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hW.le),smul_eq_mul]
  ring
lemma integrable_probability {f : α → ℝ} (hi : AEStronglyMeasurable ρ μ)
    (hρ : 0 ≤ᵐ[μ] ρ) (hW : 0 < total μ ρ) (hf : AEStronglyMeasurable f μ)
    (hprod : Integrable (fun x => ρ x*f x) μ) : Integrable f (probability μ ρ) := by
  refine ⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
  apply Integrable.hasFiniteIntegral
  rw [probability]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (hi.aemeasurable.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    ).mpr
  apply (hprod.div_const _).congr
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hW.le),smul_eq_mul]
  ring
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
lemma lintegral_probability (hρ : AEMeasurable ρ μ) (hW : 0 < total μ ρ)
    (F : α → ℝ≥0∞) (hF : AEMeasurable F μ) :
    ENNReal.ofReal (total μ ρ)*(∫⁻ x, F x ∂probability μ ρ) =
      ∫⁻ x, ENNReal.ofReal (ρ x)*F x ∂μ := by
  rw [probability,lintegral_withDensity_eq_lintegral_mul₀
    (hρ.div_const _).ennreal_ofReal hF,
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply]
  rw [ENNReal.ofReal_div_of_pos hW,div_eq_mul_inv]
  calc
    _ = (ENNReal.ofReal (total μ ρ)*(ENNReal.ofReal (total μ ρ))⁻¹)*
        (ENNReal.ofReal (ρ x)*F x) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hW) ENNReal.ofReal_ne_top,one_mul]
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Coordinates
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma map_coordinateMeasure_le (i : ℕ) :
    (q.coordinateMeasure i).map (q.chart i).paramExtended ≤ MassMeasure.currentMassMeasure hT := by
  rw [q.measure_eq]
  exact Measure.le_sum (fun index =>
    (q.coordinateMeasure index).map (q.chart index).paramExtended) i
lemma lintegral_coordinate_le (i : ℕ) (F : X → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in (q.chart i).domain, ENNReal.ofReal (q.density i z)*F ((q.chart i).paramExtended z)) ≤
      ∫⁻ x, F x ∂MassMeasure.currentMassMeasure hT := by
  have h := lintegral_mono' (q.map_coordinateMeasure_le i) (le_refl F)
  rw [lintegral_map hF (q.chart i).measurable_paramExtended] at h
  rw [coordinateMeasure,lintegral_withDensity_eq_lintegral_mul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (show AEMeasurable (fun z => F ((q.chart i).paramExtended z)) (volume.restrict (q.chart i).domain) from
      (hF.comp (q.chart i).measurable_paramExtended).aemeasurable)] at h
  exact h
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
lemma lintegral_affine (f : E → ℝ≥0∞) (z : E) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ h, f (z+ε • h) ∂μ) =
      ENNReal.ofReal ((ε^Module.finrank ℝ E)⁻¹) * ∫⁻ x, f x ∂μ := by
  have hs := lintegral_map_equiv (μ := μ) (fun x => f (z+x))
    (Homeomorph.smul (Units.mk0 ε hε.ne')).toMeasurableEquiv
  change (∫⁻ x, f (z+x) ∂μ.map (fun h => ε • h)) = (∫⁻ h, f (z+ε • h) ∂μ) at hs
  rw [←hs,Measure.map_addHaar_smul μ hε.ne',lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  congr 1
  exact (measurePreserving_add_left μ z).lintegral_comp_emb
    (Homeomorph.addLeft z).measurableEmbedding f
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Blowup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity

lemma tangent_kernel_mono {t u β c : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (hb : 0 ≤ β) (hc : 0 ≤ c) (n : ℕ) :
    t^(2*(n:ℝ)*β)/(1+c*t^(2*β))^n ≤ u^(2*(n:ℝ)*β)/(1+c*u^(2*β))^n := by
  have hu := ht.trans htu
  have htp : 0 ≤ t^(2*β) := Real.rpow_nonneg ht _
  have hup : 0 ≤ u^(2*β) := Real.rpow_nonneg hu _
  have hmono : t^(2*β) ≤ u^(2*β) := Real.rpow_le_rpow ht htu (by positivity)
  have hdenT : 0 < 1+c*t^(2*β) := by positivity
  have hdenU : 0 < 1+c*u^(2*β) := by positivity
  have hdiv : t^(2*β)/(1+c*t^(2*β)) ≤ u^(2*β)/(1+c*u^(2*β)) := by
    apply (div_le_div_iff₀ hdenT hdenU).mpr
    nlinarith [hmono]
  have he (a : ℝ) (ha : 0 ≤ a) : a^(2*(n:ℝ)*β) = (a^(2*β))^n := by
    rw [←Real.rpow_mul_natCast ha]
    congr 1; ring
  rw [he t ht,he u hu,←div_pow,←div_pow]
  exact pow_le_pow_left₀ (div_nonneg htp hdenT.le) hdiv n

lemma boundedCoordinate_nonneg {N : ℝ} (hN : 0 ≤ N) (u : ℝ) :
    0 ≤ boundedCoordinate u N := le_min (le_max_right _ _) hN
lemma boundedCoordinate_le {u N : ℝ} (hu : 0 ≤ u) : boundedCoordinate u N ≤ u := by
  simp only [boundedCoordinate,max_eq_left hu]
  exact min_le_left _ _
lemma boundedCoordinate_eq {u N : ℝ} (hu : 0 ≤ u) (hN : u ≤ N) : boundedCoordinate u N = u := by
  simp [boundedCoordinate,hu,hN]

lemma integrable_coordinate_truncation {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {s : Set E} (hs : MeasurableSet s) (hfin : μ s ≠ ∞) {u : E → ℝ} (hu : Measurable u)
    {N : ℝ} (hN : 0 ≤ N) : Integrable (s.indicator (fun z => boundedCoordinate (u z) N)) μ := by
  let : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hfin
  apply IntegrableOn.integrable_indicator _ hs
  have hm : Measurable (fun z => boundedCoordinate (u z) N) := (hu.max measurable_const).min measurable_const
  apply (MemLp.of_bound hm.aestronglyMeasurable N ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (boundedCoordinate_nonneg hN _)]
  exact min_le_right _ _
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {s : Set E} {φ : s → X} {p : Seminorm ℝ E}

lemma rescaled_distance_tendsto {z : s} (hp : HasCenteredMetricDifferentialWithin s φ p z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (h : E) (q : ℕ → s) (hq : ∀ᶠ j in atTop, (q j : E) = z+ε j • h) :
    Tendsto (fun j => dist (φ (q j)) (φ z)/ε j) atTop (𝓝 (p h)) := by
  have ht : Tendsto q atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_const_nhds (x := (z:E))).add (hε0.smul_const h)
    simp only [zero_smul,add_zero] at hh
    exact hh.congr' (hq.mono fun _ h => h.symm)
  have hb : (fun j => (q j : E)-(z:E)) =O[atTop] ε := by
    apply IsBigO.of_bound ‖h‖
    filter_upwards [hq] with j hj
    rw [hj,add_sub_cancel_left,norm_smul]
    exact le_of_eq (mul_comm _ _)
  have hl := ((hp.comp_tendsto ht).trans_isBigO hb).tendsto_div_nhds_zero
  have ha := hl.add_const (p h)
  simp only [zero_add] at ha
  apply ha.congr'
  filter_upwards [hq] with j hj
  change (dist (φ (q j)) (φ z)-p ((q j:E)-(z:E)))/ε j+p h = _
  rw [hj,add_sub_cancel_left,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (hε j)]
  field_simp [ne_of_gt (hε j)]
  ring
end CAT0Fillings.MetricDifferentiation
end

section
open Set Filter MeasureTheory Metric
open scoped Topology Pointwise

namespace CAT0Fillings.TangentDensity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]

lemma integral_affine_closedBall [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) (z : E) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (∫ h in closedBall (0:E) R, f (z+ε • h) ∂μ) =
      (ε ^ Module.finrank ℝ E)⁻¹ • ∫ x in closedBall z (ε*R), f x ∂μ := by
  rw [Measure.setIntegral_comp_smul_of_pos μ (fun x => f (z+x)) _ hε,
    smul_closedBall' hε.ne',smul_zero,Real.norm_eq_abs,abs_of_pos hε]
  congr 1
  have ht := (measurePreserving_add_left μ z).setIntegral_preimage_emb
    (Homeomorph.addLeft z).measurableEmbedding f (closedBall z (ε*R))
  have he : (fun x : E => z+x) ⁻¹' closedBall z (ε*R) = closedBall 0 (ε*R) := by
    ext x
    simp only [mem_preimage,mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero]
  rwa [he] at ht

lemma integral_affine_eq_average [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (z : E) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    (∫ h in closedBall (0:E) R, f (z+ε • h) ∂μ) =
      μ.real (closedBall (0:E) R) • (⨍ x in closedBall z (ε*R), f x ∂μ) := by
  rw [integral_affine_closedBall μ f z hε,setAverage_eq]
  have hball : 0 < μ.real (ball (0:E) 1) := ENNReal.toReal_pos
    (isOpen_ball.measure_ne_zero μ (Metric.nonempty_ball.mpr (by norm_num)))
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0:E) 1).measure_lt_top).ne
  rw [Measure.addHaar_real_closedBall μ 0 hR.le,
    Measure.addHaar_real_closedBall μ z (mul_pos hε hR).le,smul_smul,mul_pow]
  congr 1
  field_simp

lemma integrable_affine [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (hf : Integrable f μ) (z : E)
    {ε : ℝ} (hε : ε ≠ 0) : Integrable (fun h => f (z+ε • h)) μ :=
  ((measurePreserving_add_left μ z).integrable_comp_emb
    (Homeomorph.addLeft z).measurableEmbedding |>.mpr hf).comp_smul hε

lemma tendsto_integral_blowup [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} {z : E} {ε : ℕ → ℝ} {R : ℝ}
    (hε : ∀ j, 0 < ε j) (hR : 0 < R)
    (havg : Tendsto (fun j => ⨍ x in closedBall z (ε j*R), ‖f x-f z‖ ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ h in closedBall (0:E) R, ‖f (z+ε j • h)-f z‖ ∂μ)
      atTop (𝓝 0) := by
  simp_rw [integral_affine_eq_average μ (fun x => ‖f x-f z‖) z (hε _) hR]
  simpa using havg.const_smul (μ.real (closedBall (0:E) R))

lemma tendstoInMeasure_blowup [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} (hf : Integrable f μ) {z : E}
    {ε : ℕ → ℝ} {R : ℝ} (hε : ∀ j, 0 < ε j) (hR : 0 < R)
    (havg : Tendsto (fun j => ⨍ x in closedBall z (ε j*R), ‖f x-f z‖ ∂μ)
      atTop (𝓝 0)) :
    TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => f (z+ε j • h)) atTop (fun _ => f z) := by
  let : IsFiniteMeasure (μ.restrict (closedBall (0:E) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:E) R).measure_lt_top.ne
  have hi (j) : Integrable (fun h => f (z+ε j • h)) (μ.restrict (closedBall (0:E) R)) :=
    (integrable_affine μ f hf z (hε j).ne').integrableOn
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by simp)
    (fun j => (hi j).aestronglyMeasurable) aestronglyMeasurable_const
  have hl := (ENNReal.continuous_ofReal.tendsto 0).comp
    (tendsto_integral_blowup μ hε hR havg)
  simp only [ENNReal.ofReal_zero] at hl
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  rw [eLpNorm_one_eq_lintegral_enorm,
    ←ofReal_integral_norm_eq_lintegral_enorm ((hi j).sub (integrable_const _))]
  rfl
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Kernel
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings.TangentDensity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_all_blowup_inMeasure {f : E → F} (hf : Integrable f μ) :
    ∀ᵐ z ∂μ, ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
      ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
        (fun j h => f (z+ε j • h)) atTop (fun _ => f z) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub μ hf.locallyIntegrable (1:ℝ)] with z hz
  intro ε hε hε0 R hR
  apply tendstoInMeasure_blowup μ hf hε hR
  apply hz (fun _ : ℕ => z) (fun j => ε j*R)
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun j => mul_pos (hε j) hR)⟩
    simpa using hε0.mul_const R
  · filter_upwards [] with j
    exact mem_closedBall_self (by simpa using (mul_pos (hε j) hR).le)

lemma common_subsequence_three {α A B C : Type*} [MeasurableSpace α]
    [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
    {μ : Measure α} {f : ℕ → α → A} {g : ℕ → α → B} {h : ℕ → α → C}
    {f₀ : α → A} {g₀ : α → B} {h₀ : α → C}
    (hf : TendstoInMeasure μ f atTop f₀) (hg : TendstoInMeasure μ g atTop g₀)
    (hh : TendstoInMeasure μ h atTop h₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂μ,
      Tendsto (fun j => f (σ j) x) atTop (𝓝 (f₀ x)) ∧
      Tendsto (fun j => g (σ j) x) atTop (𝓝 (g₀ x)) ∧
      Tendsto (fun j => h (σ j) x) atTop (𝓝 (h₀ x)) := by
  obtain ⟨σ,hσ,hf⟩ := hf.exists_seq_tendsto_ae
  obtain ⟨τ,hτ,hg⟩ := (hg.comp hσ.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨υ,hυ,hh⟩ := (hh.comp (hσ.comp hτ).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨σ ∘ τ ∘ υ,hσ.comp (hτ.comp hυ),?_⟩
  filter_upwards [hf,hg,hh] with x hf hg hh
  exact ⟨hf.comp (hτ.comp hυ).tendsto_atTop,hg.comp hυ.tendsto_atTop,hh⟩

lemma indicator_one_eventually {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
    {q : ℕ → α} (h : Tendsto (fun j => s.indicator (fun _ => (1:ℝ)) (q j))
      atTop (𝓝 1)) : ∀ᶠ j in atTop, q j ∈ s := by
  filter_upwards [(tendsto_order.1 h).1 (1/2) (by norm_num)] with j hj
  by_contra hn
  simp only [indicator_of_notMem hn] at hj
  norm_num at hj
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma lintegral_limit_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ j, AEMeasurable (f j) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞} (hB : ∀ j, ∫⁻ x, f j x ∂μ ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) : ∫⁻ x, g x ∂μ ≤ L := by
  calc
    ∫⁻ x, g x ∂μ = ∫⁻ x, liminf (fun j => f j x) atTop ∂μ :=
      lintegral_congr_ae (hg.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun j => ∫⁻ x, f j x ∂μ) atTop := lintegral_liminf_le' hf
    _ ≤ liminf B atTop := liminf_le_liminf (Eventually.of_forall hB)
    _ = L := hL.liminf_eq

end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X]

lemma kernel_tendsto {u ρ R : ℕ → ℝ} {u₀ ρ₀ R₀ κ β p : ℝ} (n : ℕ)
    (hu₀ : 0 < u₀) (hu : Tendsto u atTop (𝓝 u₀))
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (hR : Tendsto R atTop (𝓝 R₀)) :
    Tendsto (fun j => u j^p*ρ j/(1+κ^2*R j^2*u j^(2*β))^n) atTop
      (𝓝 (u₀^p*ρ₀/(1+κ^2*R₀^2*u₀^(2*β))^n)) := by
  exact ((hu.rpow_const (.inl hu₀.ne')).mul hρ).div
    ((tendsto_const_nhds.add ((tendsto_const_nhds.mul (hR.pow 2)).mul
      (hu.rpow_const (.inl hu₀.ne')))).pow n)
    (pow_ne_zero n (ne_of_gt (by positivity)))

lemma chartExtension_rescaled_tendsto {s : Set E} {φ : s → X} {z : s}
    {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0)) (h : E)
    (hs : ∀ᶠ j in atTop, (z:E)+ε j • h ∈ s) :
    Tendsto (fun j => dist (chartExtension φ z ((z:E)+ε j • h)) (φ z)/ε j)
      atTop (𝓝 (d h)) := by
  classical
  let q : ℕ → s := fun j => if hx : (z:E)+ε j • h ∈ s then ⟨(z:E)+ε j • h,hx⟩ else z
  have hq : ∀ᶠ j in atTop, (q j:E) = (z:E)+ε j • h := by
    filter_upwards [hs] with j hj
    simp [q,hj]
  have ht := MetricDifferentiation.rescaled_distance_tendsto hd hε hε0 h q hq
  apply ht.congr'
  filter_upwards [hs] with j hj
  simp [q,chartExtension,hj]

lemma chart_kernel_tendsto {s : Set E} {φ : s → X} {z : s}
    {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z) (h : E)
    (hu : Tendsto (fun j => u ((z:E)+ε j • h)) atTop (𝓝 (u z)))
    (hρ : Tendsto (fun j => ρ ((z:E)+ε j • h)) atTop (𝓝 (ρ z)))
    (hχ : Tendsto (fun j => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h))
      atTop (𝓝 1)) :
    Tendsto (fun j => s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) atTop
      (𝓝 (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n)) := by
  classical
  have hs := indicator_one_eventually hχ
  have ht := kernel_tendsto (κ := κ) (β := β) (p := p) n hu₀ hu hρ
    (chartExtension_rescaled_tendsto hd hε hε0 h hs)
  apply ht.congr'
  filter_upwards [hs] with j hj
  rw [indicator_of_mem hj]
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_LocalChart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_kernel_blowup_le (i : ℕ) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (u : Euc n → ℝ) (hu : ∀ z, 0 ≤ u z)
    (huU : ∀ z ∈ (q.chart i).domain, u z ≤ U ((q.chart i).paramExtended z))
    (z : (q.chart i).domain) {ε β κ : ℝ} (hε : 0 < ε) (hb : 0 ≤ β) :
    let ρ := (q.chart i).domain.indicator (q.density i)
    (∫⁻ h, ENNReal.ofReal ((q.chart i).domain.indicator
      (fun x => (u x)^(2*(n:ℝ)*β)*ρ x /
        (1+κ^2*(dist (chartExtension (q.chart i).param z x) ((q.chart i).param z)/ε)^2*(u x)^(2*β))^n)
      ((z:Euc n)+ε • h))) ≤
    ENNReal.ofReal ((ε^n)⁻¹) * ∫⁻ x, ENNReal.ofReal
      ((U x)^(2*(n:ℝ)*β)/(1+κ^2*(dist x ((q.chart i).param z)/ε)^2*(U x)^(2*β))^n)
        ∂MassMeasure.currentMassMeasure hT := by
  classical
  let ρ := (q.chart i).domain.indicator (q.density i)
  let C := q.chart i
  let F : X → ℝ≥0∞ := fun x => ENNReal.ofReal
    ((U x)^(2*(n:ℝ)*β)/(1+κ^2*(dist x (C.param z)/ε)^2*(U x)^(2*β))^n)
  have hF : Measurable F := ((hU.pow_const _).div
    ((measurable_const.add ((measurable_const.mul
      (((measurable_id.dist measurable_const).div_const ε).pow_const 2)).mul
      (hU.pow_const _))).pow_const n)).ennreal_ofReal
  let g : Euc n → ℝ := fun x => (u x)^(2*(n:ℝ)*β)*ρ x /
    (1+κ^2*(dist (chartExtension C.param z x) (C.param z)/ε)^2*(u x)^(2*β))^n
  change (∫⁻ h, ENNReal.ofReal (C.domain.indicator g ((z:Euc n)+ε • h))) ≤ _
  rw [lintegral_affine volume (fun x => ENNReal.ofReal (C.domain.indicator g x)) (z:Euc n) hε]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  gcongr 1
  apply le_trans ?_ (q.lintegral_coordinate_le i F hF)
  have hi : (fun x => ENNReal.ofReal (C.domain.indicator g x)) =
      C.domain.indicator (fun x => ENNReal.ofReal (g x)) := by
    ext x
    by_cases hx : x ∈ C.domain <;> simp [hx]
  change (∫⁻ x, ENNReal.ofReal (C.domain.indicator g x)) ≤ _
  rw [hi,lintegral_indicator C.borel]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem C.borel] with x hx
  have he : chartExtension C.param z x = C.paramExtended x := by
    simp only [chartExtension,IntegerChart.paramExtended,dite_eq_left hx]
  have density_nonneg : 0 ≤ q.density i x :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  change ENNReal.ofReal (g x) ≤ ENNReal.ofReal (q.density i x)*F (C.paramExtended x)
  dsimp only [F]
  have kernel_nonneg : 0 ≤
      (U (C.paramExtended x))^(2*(n:ℝ)*β) /
        (1+κ^2*(dist (C.paramExtended x) (C.param z)/ε)^2*
          (U (C.paramExtended x))^(2*β))^n := by
    apply div_nonneg (Real.rpow_nonneg (hU0 _) _)
    exact pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (sq_nonneg κ) (sq_nonneg _))
        (Real.rpow_nonneg (hU0 _) _))) _
  rw [←ENNReal.ofReal_mul' kernel_nonneg]
  apply ENNReal.ofReal_le_ofReal
  have hm := tangent_kernel_mono (hu x) (huU x hx) hb
    (mul_nonneg (sq_nonneg κ) (sq_nonneg (dist (C.paramExtended x) (C.param z)/ε))) n
  dsimp only [g]
  rw [show ρ x = q.density i x from indicator_of_mem hx _,he]
  convert mul_le_mul_of_nonneg_right hm density_nonneg using 1 <;> first | rfl | ring
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma chart_kernel_aemeasurable (i : ℕ) (u : Euc n → ℝ) (hu : Measurable u)
    (z : (q.chart i).domain) {ε : ℝ} (hε : 0 < ε) (p β κ : ℝ) :
    let ρ := (q.chart i).domain.indicator (q.density i)
    AEMeasurable (fun h : Euc n => ENNReal.ofReal ((q.chart i).domain.indicator
      (fun x => u x^p*ρ x /
        (1+κ^2*(dist (chartExtension (q.chart i).param z x) ((q.chart i).param z)/ε)^2*u x^(2*β))^n)
      ((z:Euc n)+ε • h))) volume := by
  classical
  let C := q.chart i
  let ρ := C.domain.indicator (q.density i)
  let A : Euc n → Euc n := fun h => (z:Euc n)+ε • h
  have hA : Measurable A := by
    dsimp [A]
    fun_prop
  have hρ : Integrable ρ := IntegrableOn.integrable_indicator (q.density_integrable i) C.borel
  have hρA := (integrable_affine volume ρ hρ (z:Euc n) hε.ne').aestronglyMeasurable.aemeasurable
  have huA := hu.comp hA
  have hdA : Measurable (fun h => dist (C.paramExtended (A h)) (C.param z)/ε) :=
    (((C.measurable_paramExtended.comp hA).dist measurable_const).div_const ε)
  have hm : AEMeasurable (fun h => u (A h)^p*ρ (A h) /
      (1+κ^2*(dist (C.paramExtended (A h)) (C.param z)/ε)^2*u (A h)^(2*β))^n) volume :=
    ((huA.pow_const p).aemeasurable.mul hρA).div
    ((measurable_const.add ((measurable_const.mul (hdA.pow_const 2)).mul
      (huA.pow_const (2*β)))).pow_const n).aemeasurable
  have hi := (hm.indicator (C.borel.preimage hA)).ennreal_ofReal
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  by_cases hh : A h ∈ C.domain
  · dsimp [A,C] at hh
    simp [A,C,ρ,chartExtension,IntegerChart.paramExtended,hh]
  · dsimp [A,C] at hh
    simp [A,C,ρ,hh]
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {X : Type*} [MetricSpace X] {μ : Measure E}

lemma local_density_bound {s : Set E} {φ : s → X} {z : s} {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z)
    (hu : TendstoInMeasure μ (fun j h => u ((z:E)+ε j • h)) atTop (fun _ => u z))
    (hρ : TendstoInMeasure μ (fun j h => ρ ((z:E)+ε j • h)) atTop (fun _ => ρ z))
    (hχ : TendstoInMeasure μ (fun j h => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h))
      atTop (fun _ => 1))
    (hK : ∀ j, AEMeasurable (fun h => ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h))) μ)
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hB : ∀ j, (∫⁻ h, ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) ∂μ) ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) :
    (∫⁻ h, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L := by
  obtain ⟨σ,hσ,ht⟩ := common_subsequence_three hu hρ hχ
  apply lintegral_limit_le (fun j => hK (σ j)) (B := B ∘ σ) (L := L) ?_
    (fun j => hB (σ j)) (hL.comp hσ.tendsto_atTop)
  filter_upwards [ht] with h hh
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (chart_kernel_tendsto hd (fun j => hε (σ j)) (hε0.comp hσ.tendsto_atTop) u ρ n hu₀ h
      hh.1 hh.2.1 hh.2.2)
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Quadratic
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings

lemma exists_hilbert_norm_equiv {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ e : Euc k ≃L[ℝ] Euc k, (∀ v, ‖e v‖ = p v) ∧
      |LinearMap.det e.toLinearEquiv.toLinearMap| =
        Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix p b
  have hQ : Q.PosDef := polarizationMatrix_posDef b p hp hpara
  let L : Euc k →ₗ[ℝ] Euc k := Matrix.toEuclideanLin (CFC.sqrt Q)
  have hdet : LinearMap.det L = Real.sqrt Q.det := by
    rw [show L = Matrix.toLin b b (CFC.sqrt Q) from rfl,LinearMap.det_toLin]
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact (Real.sqrt_pos.mpr hQ.det_pos).ne'
  let e := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv
  refine ⟨e,?_,?_⟩
  · intro v
    have hnorm : ‖e v‖^2 = p v^2 := by
      rw [←real_inner_self_eq_norm_sq]
      change inner ℝ (L v) (L v) = _
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
      change (CFC.sqrt Q).mulVec (WithLp.ofLp v) ⬝ᵥ
        (CFC.sqrt Q).mulVec (WithLp.ofLp v) = p v^2
      rw [←dot_mulVec_sqrt Q hQ.posSemidef]
      have hrepr : b.repr v = WithLp.ofLp v := by ext j; simp [b]
      rw [←hrepr]
      exact polarizationMatrix_quadratic b p hp hpara v
    nlinarith [norm_nonneg (e v),apply_nonneg p v]
  · change |LinearMap.det L| = _
    rw [hdet,abs_of_nonneg (Real.sqrt_nonneg _)]

end CAT0Fillings
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology

namespace CAT0Fillings.TangentDensity

lemma integral_comp_linear_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) (f : E → F) :
    (∫ x, f (e x) ∂μ) = |LinearMap.det e.toLinearEquiv.toLinearMap|⁻¹ • (∫ x, f x ∂μ) := by
  have hi := e.toHomeomorph.measurableEmbedding.integral_map (μ := μ) f
  change (∫ x, f x ∂Measure.map e μ) = (∫ x, f (e x) ∂μ) at hi
  rw [←hi]
  have he := Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  change Measure.map e μ = _ at he
  rw [he,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),abs_inv]

lemma quadratic_bubble_mass {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {a : ℝ} (ha : 0 < a) :
    a^n * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det *
      (∫ h : Euc n, (1+a^2*(d h)^2)^(-(n:ℝ))) = sphereArea n/(2:ℝ)^n := by
  obtain ⟨e,he,hdet⟩ := exists_hilbert_norm_equiv d hd hpara
  have hJ : 0 < Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det :=
    Real.sqrt_pos.mpr (polarizationMatrix_posDef _ _ hd hpara).det_pos
  have hnorm (h : Euc n) : ‖a • e h‖^2 = a^2*(d h)^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha,he,mul_pow]
  have hi : (∫ h : Euc n, (1+a^2*(d h)^2)^(-(n:ℝ))) =
      |LinearMap.det e.toLinearEquiv.toLinearMap|⁻¹ *
      (a^n)⁻¹ * (sphereArea n/(2:ℝ)^n) := by
    simp_rw [←hnorm]
    rw [integral_comp_linear_equiv volume e (fun x => (1+‖a • x‖^2)^(-(n:ℝ))),
      Measure.integral_comp_smul_of_nonneg volume (fun x : Euc n => (1+‖x‖^2)^(-(n:ℝ))) a (hR := ha.le)]
    simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,
      RadialSobolev.integral_euclidean_bubble hn]
    ring
  rw [hi,hdet]
  field_simp
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity

lemma integral_tangent_density {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) (θ : ℤ) :
    (∫ h : Euc n, u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| *Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n) = |(θ:ℝ)| *(sphereArea n/(2:ℝ)^n) := by
  let J := Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det
  have ha : 0 < u^(2*β) := Real.rpow_pos_of_pos hu _
  have hm : (u^β)^2 = u^(2*β) := by
    rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have hpow : (u^(2*β))^n = u^(2*(n:ℝ)*β) := by
    rw [←Real.rpow_mul_natCast hu.le]; congr 1; ring
  have he (h : Euc n) : 1+(u^β)^2*(d h)^2*u^(2*β) = 1+(u^(2*β))^2*(d h)^2 := by
    rw [hm]; ring
  simp_rw [he]
  have hi : (∫ h : Euc n, u^(2*(n:ℝ)*β)*(|(θ:ℝ)| *J) /
      (1+(u^(2*β))^2*(d h)^2)^n) =
      u^(2*(n:ℝ)*β)*(|(θ:ℝ)| *J)*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ))) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    simp only [Real.rpow_neg_natCast, _root_.zpow_neg,zpow_natCast,div_eq_mul_inv]
  change _ = |(θ:ℝ)| *(sphereArea n/(2:ℝ)^n)
  rw [hi]
  have hq := quadratic_bubble_mass hn d hd hpara ha
  rw [hpow] at hq
  change u^(2*(n:ℝ)*β)*J*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ))) = _ at hq
  calc
    _ = |(θ:ℝ)| *(u^(2*(n:ℝ)*β)*J*(∫ h : Euc n, (1+(u^(2*β))^2*(d h)^2)^(-(n:ℝ)))) := by ring
    _ = _ := by rw [hq]

lemma tangent_density_lower_bound {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) {θ : ℤ} (hθ : θ ≠ 0) :
    sphereArea n/(2:ℝ)^n ≤ (∫ h : Euc n, u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| *Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n) := by
  rw [integral_tangent_density hn d hd hpara hu θ]
  have hθ1 : (1:ℝ) ≤ |(θ:ℝ)| := by exact_mod_cast (Int.one_le_abs hθ)
  apply le_mul_of_one_le_left
  · unfold sphereArea
    exact div_nonneg (mul_nonneg (by positivity) (by unfold omega; exact ENNReal.toReal_nonneg)) (by positivity)
  · exact hθ1
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Transfer
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {X : Type*} [MetricSpace X] {μ : Measure E}

lemma global_density_bound {s : Set E} {φ : s → X} {z : s} {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z)
    (hu : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => u ((z:E)+ε j • h)) atTop (fun _ => u z))
    (hρ : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => ρ ((z:E)+ε j • h)) atTop (fun _ => ρ z))
    (hχ : ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h)) atTop (fun _ => 1))
    (hK : ∀ j, AEMeasurable (fun h => ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h))) μ)
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hB : ∀ j, (∫⁻ h, ENNReal.ofReal (s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) ∂μ) ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) :
    (∫⁻ h, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L := by
  have hloc {R : ℝ} (hR : 0 < R) :
      (∫⁻ h in closedBall (0:E) R, ENNReal.ofReal (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n) ∂μ) ≤ L :=
    local_density_bound hd hε hε0 u ρ n hu₀ (hu R hR) (hρ R hR) (hχ R hR)
      (fun j => (hK j).mono_measure Measure.restrict_le_self)
      (fun j => (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hB j)) hL
  rw [←Measure.restrict_univ (μ := μ),←iUnion_closedBall_nat (0:E),setLIntegral_iUnion_of_directed]
  · apply iSup_le
    intro j
    exact (lintegral_mono' (Measure.restrict_mono (closedBall_subset_closedBall (show (j:ℝ) ≤ j+1 by linarith)) le_rfl)
      le_rfl).trans (hloc (R := (j:ℝ)+1) (by positivity))
  · intro i j
    exact ⟨max i j,closedBall_subset_closedBall (Nat.cast_le.mpr (le_max_left i j)),
      closedBall_subset_closedBall (Nat.cast_le.mpr (le_max_right i j))⟩

lemma tangent_coefficient_of_bound {n : ℕ} (hn : 2 < n) (d : Seminorm ℝ (Euc n))
    (hd : ∀ h, d h = 0 ↔ h = 0)
    (hpara : ∀ h h', d (h+h')^2+d (h-h')^2 = 2*d h^2+2*d h'^2)
    {u β : ℝ} (hu : 0 < u) {θ : ℤ} (hθ : θ ≠ 0) {L : ℝ≥0∞}
    (hL : (∫⁻ h : Euc n, ENNReal.ofReal (u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n)) ≤ L) :
    ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L := by
  have hc := tangent_density_lower_bound hn d hd hpara (β := β) hu hθ
  apply (ENNReal.ofReal_le_ofReal hc).trans
  apply le_trans ?_ hL
  by_cases hi : Integrable (fun h : Euc n => u^(2*(n:ℝ)*β)*
      (|(θ:ℝ)| * Real.sqrt (polarizationMatrix d (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).det) /
      (1+(u^β)^2*(d h)^2*u^(2*β))^n)
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun h => by positivity)]
  · rw [integral_undef hi,ENNReal.ofReal_zero]
    exact bot_le
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_chart_tangent_density (hn : 2 < n) (i : ℕ) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 ≤ β) :
    ∀ᵐ z ∂q.coordinateMeasure i, 0 < U ((q.chart i).paramExtended z) →
      ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
      ∀ (B : ℕ → ℝ≥0∞) (L : ℝ≥0∞),
      (∀ j, ENNReal.ofReal ((ε j^n)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
          (1+(U ((q.chart i).paramExtended z)^β)^2*
            (dist x ((q.chart i).paramExtended z)/ε j)^2*U x^(2*β))^n)
          ∂MassMeasure.currentMassMeasure hT ≤ B j) →
      Tendsto B atTop (𝓝 L) →
      ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L := by
  classical
  let C := q.chart i
  let ρ := C.domain.indicator (q.density i)
  let u (N : ℕ) := C.domain.indicator
    (fun z => boundedCoordinate (U (C.paramExtended z)) (N:ℝ))
  have hρ : Integrable ρ := IntegrableOn.integrable_indicator (q.density_integrable i) C.borel
  have hχ : Integrable (C.domain.indicator (fun _ => (1:ℝ))) := by
    exact IntegrableOn.integrable_indicator (integrableOn_const C.bounded.measure_lt_top.ne) C.borel
  have hu (N : ℕ) : Integrable (u N) := integrable_coordinate_truncation C.borel
    C.bounded.measure_lt_top.ne (hU.comp C.measurable_paramExtended) (Nat.cast_nonneg N)
  have hmu (N : ℕ) : Measurable (u N) :=
    (((hU.comp C.measurable_paramExtended).max measurable_const).min measurable_const).indicator C.borel
  have ha : ∀ᵐ z ∂volume, ∀ N : ℕ, ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) →
      Tendsto ε atTop (𝓝 0) → ∀ R : ℝ, 0 < R →
      TendstoInMeasure (volume.restrict (closedBall (0:Euc n) R))
        (fun j h => u N (z+ε j • h)) atTop (fun _ => u N z) := by
    exact ae_all_iff.mpr (fun N => ae_all_blowup_inMeasure volume (hu N))
  rw [coordinateMeasure]
  apply (ae_withDensity_iff' (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal).mpr
  filter_upwards [ha.filter_mono (ae_mono Measure.restrict_le_self),
    (ae_all_blowup_inMeasure volume hρ).filter_mono (ae_mono Measure.restrict_le_self),
    (ae_all_blowup_inMeasure volume hχ).filter_mono (ae_mono Measure.restrict_le_self),
    q.differential i,ae_restrict_mem C.borel] with z hu' hρ' hχ' hd hz
  intro hρ0 hUz ε hε hε0 B L hupper hL
  have hzC : z ∈ C.domain := hz
  obtain ⟨N,hN⟩ := exists_nat_ge (U (C.paramExtended z))
  have huz : u N z = U (C.paramExtended z) := by
    simp only [u,indicator_of_mem hzC]
    exact boundedCoordinate_eq (hU0 _) hN
  have hθ : C.multiplicity z ≠ 0 := by
    intro hh
    apply hρ0
    simp [density,hh,C]
  have hρz : ρ z = q.density i z := indicator_of_mem hz _
  have hχz : C.domain.indicator (fun _ => (1:ℝ)) z = 1 := indicator_of_mem hz _
  have he : C.param ⟨z,hz⟩ = C.paramExtended z := by simp only [IntegerChart.paramExtended,dite_eq_left hzC]
  have heq : (q.chart i).param ⟨z,hz⟩ = (q.chart i).paramExtended z := he
  have hu₀ : ∀ x, 0 ≤ u N x := by
    intro x
    apply indicator_nonneg
    exact fun y hy => boundedCoordinate_nonneg (Nat.cast_nonneg N) _
  have huU : ∀ x ∈ C.domain, u N x ≤ U (C.paramExtended x) := by
    intro x hx
    simp only [u,indicator_of_mem hx]
    exact boundedCoordinate_le (hU0 _)
  have hbound := global_density_bound (κ := U (C.paramExtended z)^β) (β := β)
    (p := 2*(n:ℝ)*β) (μ := volume) (hd.1 hz) hε hε0 (u N) ρ n
    (show 0 < u N z by rw [huz]; exact hUz)
    (hu' N ε hε hε0) (hρ' ε hε hε0)
    (by simpa only [hχz] using hχ' ε hε hε0)
    (fun j => q.chart_kernel_aemeasurable i (u N) (hmu N) ⟨z,hz⟩ (hε j) _ _ _)
    (fun j => (q.chart_kernel_blowup_le i U hU hU0 (u N) hu₀ huU ⟨z,hz⟩
      (κ := U (C.paramExtended z)^β) (hε j) hb).trans (by simpa only [heq] using hupper j))
    hL
  apply tangent_coefficient_of_bound hn (q.field i z) hd.2.2 hd.2.1 hUz hθ
  simpa only [huz,hρz,density,gram,he] using hbound
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
lemma ae_map_of_ae_on_embedding {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) {f : E → X} (hf : Measurable f)
    (hfs : MeasurableEmbedding (fun z : s => f z)) (hmem : ∀ᵐ z ∂μ, z ∈ s)
    {P : X → Prop} (hP : ∀ᵐ z ∂μ, P (f z)) : ∀ᵐ x ∂μ.map f, P x := by
  let ν := μ.comap (fun z : s => (z:E))
  have hmap : ν.map (fun z : s => (z:E)) = μ := by
    rw [(MeasurableEmbedding.subtype_coe hs).map_comap]
    simp only [Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem hmem
  have hmap' : ν.map (fun z : s => f z) = μ.map f := by
    change ν.map (f ∘ Subtype.val) = μ.map f
    rw [←Measure.map_map hf measurable_subtype_coe,hmap]
  rw [←hmap']
  apply hfs.ae_map_iff.mpr
  exact ae_of_ae_map (μ := ν) (p := fun z => P (f z))
    measurable_subtype_coe.aemeasurable (by rw [hmap]; exact hP)
end CAT0Fillings.TangentDensity
namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma ae_current_of_ae_coordinates {P : X → Prop}
    (hP : ∀ i, ∀ᵐ z ∂q.coordinateMeasure i, P ((q.chart i).paramExtended z)) :
    ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, P x := by
  rw [q.measure_eq]
  apply Measure.ae_sum_iff.mpr
  intro i
  change ∀ᵐ x ∂(q.coordinateMeasure i).map (q.chart i).paramExtended, P x
  apply TangentDensity.ae_map_of_ae_on_embedding (q.chart i).borel
    (q.chart i).measurable_paramExtended ?_ ?_ (hP i)
  · convert (q.chart i).measurableEmbedding_param using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [IntegerChart.paramExtended,z.property]
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (q.chart i).borel)
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_CurrentDensity
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
lemma kernel_rescaled (n : ℕ) {u ε β κ r : ℝ} (hu : 0 ≤ u) :
    u^(2*(n:ℝ)*β)/(1+κ^2*(r/ε)^2*u^(2*β))^n =
    u^(2*(n:ℝ)*β)*ChordTransform.kernel n ((κ*r*u^β)^2) ((ε^2)⁻¹) := by
  have hp : (u^β)^2 = u^(2*β) := by
    rw [←Real.rpow_mul_natCast hu]; congr 1; ring
  have he : 1+κ^2*(r/ε)^2*u^(2*β) = 1+(ε^2)⁻¹*(κ*r*u^β)^2 := by
    simp only [mul_pow,hp,div_eq_mul_inv]
    ring
  rw [he]
  simp [ChordTransform.kernel,Real.rpow_neg_natCast,_root_.zpow_neg,zpow_natCast,div_eq_mul_inv]

lemma rescaled_transform_identity (μ : Measure X) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (n : ℕ) (β κ ε : ℝ) (o : X)
    (hi : Integrable (fun x => U x^(2*(n:ℝ)*β)) μ)
    (hW : 0 < ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β))) :
    let ρ := fun x => U x^(2*(n:ℝ)*β)
    let ν := ChordMeasure.probability μ ρ
    (∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
      (1+κ^2*(dist x o/ε)^2*U x^(2*β))^n) ∂μ) =
    ENNReal.ofReal (ChordMeasure.total μ ρ *
      ChordTransform.transform ν n (fun x => (κ*dist o x*U x^β)^2) ((ε^2)⁻¹)) := by
  let ρ := fun x => U x^(2*(n:ℝ)*β)
  let ν := ChordMeasure.probability μ ρ
  let b := fun x => (κ*dist o x*U x^β)^2
  have hb : Measurable b := ((measurable_const.mul ((continuous_const.dist continuous_id).measurable)).mul (hU.pow_const β)).pow_const 2
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ ρ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW
  have hki := ChordTransform.kernel_integrable ν hb.aestronglyMeasurable
    (Eventually.of_forall fun x => sq_nonneg _) (Nat.cast_nonneg n)
    (inv_nonneg.mpr (sq_nonneg ε))
  change _ = ENNReal.ofReal (ChordMeasure.total μ ρ * ChordTransform.transform ν n b ((ε^2)⁻¹))
  rw [ENNReal.ofReal_mul hW.le,ChordTransform.transform,
    ofReal_integral_eq_lintegral_ofReal hki (Eventually.of_forall fun x =>
      (ChordTransform.kernel_pos (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg ε))).le),
    ChordMeasure.lintegral_probability μ ρ (hU.pow_const _).aemeasurable hW _
      ((ChordTransform.kernel_aestronglyMeasurable μ hb.aestronglyMeasurable _ _).aemeasurable.ennreal_ofReal)]
  apply lintegral_congr
  intro x
  rw [kernel_rescaled n (hU0 x),dist_comm x o,ENNReal.ofReal_mul (Real.rpow_nonneg (hU0 x) _)]
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v : X → ℝ}
lemma exists_nonnegative_borel (hv : AEStronglyMeasurable v μ) (hpos : 0 ≤ᵐ[μ] v) :
    ∃ U : X → ℝ, Measurable U ∧ (∀ x, 0 ≤ U x) ∧ U =ᵐ[μ] v := by
  refine ⟨fun x => max (hv.mk v x) 0,hv.measurable_mk.max measurable_const,fun x => le_max_right _ _,?_⟩
  filter_upwards [hv.ae_eq_mk,hpos] with x hx hp
  change 0 ≤ v x at hp
  rw [←hx,max_eq_left hp]
lemma ae_positive_probability {U : X → ℝ} (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {p : ℝ} (hp : 0 < p) :
    ∀ᵐ y ∂probability μ (fun x => U x^p), 0 < U y := by
  rw [probability]
  apply (ae_withDensity_iff' ((hU.pow_const _).div_const _).ennreal_ofReal.aemeasurable).mpr
  filter_upwards [] with y hy
  by_contra hh
  have hu := le_antisymm (le_of_not_gt hh) (hU0 y)
  apply hy
  simp [hu,Real.zero_rpow hp.ne']
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
include q in
lemma ae_current_tangent_density_imp (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 ≤ β) :
    ∀ᵐ y ∂MassMeasure.currentMassMeasure hT, 0 < U y →
      TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y := by
  exact q.ae_current_of_ae_coordinates (P := fun y => 0 < U y →
    TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y)
    (fun i => q.ae_chart_tangent_density hn i U hU hU0 hb)

include q in
lemma ae_current_tangent_density (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β) :
    ∀ᵐ y ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2*(n:ℝ)*β)),
      TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y := by
  have hp : 0 < 2*(n:ℝ)*β := mul_pos (mul_pos (by norm_num) (by exact_mod_cast (show 0<n by omega))) hb
  have hd := q.ae_current_tangent_density_imp hn U hU hU0 hb.le
  have hd' := (withDensity_absolutelyContinuous (MassMeasure.currentMassMeasure hT)
    (fun x => ENNReal.ofReal (U x^(2*(n:ℝ)*β)/ChordMeasure.total (MassMeasure.currentMassMeasure hT)
      (fun x => U x^(2*(n:ℝ)*β))))).ae_le hd
  filter_upwards [ChordMeasure.ae_positive_probability hU hU0 hp,hd'] with y hy hd
  exact hd hy
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
lemma rescaled_power_eq (n : ℕ) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    (ε^n)⁻¹*(1+C*(ε^2)⁻¹)^(-(n:ℝ)/2) = (ε^2+C)^(-(n:ℝ)/2) := by
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  have he : 1+C*(ε^2)⁻¹ = (ε^2+C)/(ε^2) := by field_simp
  have hp : (ε^2)^(-(n:ℝ)/2) = (ε^n)⁻¹ := by
    rw [←Real.rpow_natCast ε 2,←Real.rpow_mul hε.le]
    rw [Nat.cast_ofNat,show (2:ℝ)*(-(n:ℝ)/2) = -(n:ℝ) by ring,Real.rpow_neg_natCast,
      _root_.zpow_neg,zpow_natCast]
  rw [he,Real.div_rpow (by positivity) hs.le,hp]
  have hn : (ε^n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hε.ne')
  exact mul_div_cancel₀ _ hn

lemma rescaled_spherical_limit (n : ℕ) {ε : ℕ → ℝ}
    (hε : ∀ j, 0 < ε j) (h0 : Tendsto ε atTop (𝓝 0)) (W : ℝ) :
    Tendsto (fun j => ENNReal.ofReal ((ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)))
      atTop (𝓝 (ENNReal.ofReal (W/(2:ℝ)^n))) := by
  have he (j) : (ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2) =
      W*((ε j)^2+4)^(-(n:ℝ)/2) := by
    calc
      _ = W*((ε j^n)⁻¹*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)) := by ring
      _ = _ := by rw [rescaled_power_eq n (hε j) (by norm_num : (0:ℝ)≤4)]
  simp_rw [he]
  have hfour : (4:ℝ)^(-(n:ℝ)/2) = ((2:ℝ)^n)⁻¹ := by
    rw [show (4:ℝ) = 2^2 by norm_num,←Real.rpow_natCast (2:ℝ) 2,
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [Nat.cast_ofNat,show (2:ℝ)*(-(n:ℝ)/2) = -(n:ℝ) by ring,Real.rpow_neg_natCast,
      _root_.zpow_neg,zpow_natCast]
  apply ENNReal.tendsto_ofReal
  have h := (tendsto_const_nhds (x := W)).mul
    (((h0.pow 2).add_const 4).rpow_const (p := -(n:ℝ)/2) (Or.inl (by norm_num)))
  simp only [zero_pow (by norm_num : 2≠0),zero_add] at h
  change Tendsto (fun j => W*(ε j^2+4)^(-(n:ℝ)/2)) atTop
    (𝓝 (W*(4:ℝ)^(-(n:ℝ)/2))) at h
  rw [hfour] at h
  simpa only [div_eq_mul_inv] using h
end CAT0Fillings.TangentDensity
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Barycenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
lemma moment_lt_two (μ : Measure X) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (n : ℕ) {β : ℝ} (y : X)
    (hi : Integrable (fun x => U x^(2*(n:ℝ)*β)) μ)
    (hW : 0 < ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β)))
    (hWs : ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β)) < sphereArea n)
    (ht : HasTangentBound μ U n β y)
    (hd : ∀ a : ℝ, 0 ≤ a →
      ChordTransform.transform (ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β))) n
        (fun x => (U y^β*dist y x*U x^β)^2) a ≤
      (1+2*(∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β)))*a)^(-(n:ℝ)/2)) :
    (∫ x, (U y^β*dist y x*U x^β)^2
      ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β))) < 2 := by
  by_contra hh
  have hm : 2 ≤ ∫ x, (U y^β*dist y x*U x^β)^2
      ∂ChordMeasure.probability μ (fun x => U x^(2*(n:ℝ)*β)) := le_of_not_gt hh
  let ε (j : ℕ) : ℝ := ((j:ℝ)+1)⁻¹
  have he : ∀ j, 0 < ε j := fun j => inv_pos.mpr (by positivity)
  have he0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let W := ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β))
  have hb := ht ε he he0
    (fun j => ENNReal.ofReal ((ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)))
    (ENNReal.ofReal (W/(2:ℝ)^n)) (fun j => ?_)
    (rescaled_spherical_limit n he he0 W)
  · have hreal : sphereArea n/(2:ℝ)^n ≤ W/(2:ℝ)^n :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
    exact (not_le_of_gt hWs) ((div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<2^n)).mp hreal)
  · rw [rescaled_transform_identity μ U hU hU0 n β (U y^β) (ε j) y hi hW,
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (ε j^n)⁻¹)]
    apply ENNReal.ofReal_le_ofReal
    conv_rhs => rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (he j).le n))
    apply mul_le_mul_of_nonneg_left _ hW.le
    refine (hd _ (by positivity)).trans ?_
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · have ha : 0 ≤ (ε j^2)⁻¹ := by positivity
      nlinarith
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num)
end CAT0Fillings.TangentDensity
end

section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma integrable_dist_sq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] (y : X) :
    Integrable (fun x => dist y x ^ 2) μ :=
  (by fun_prop : Continuous (fun x => dist y x ^ 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma continuous_squaredPotential {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (squaredPotential μ) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := μ) (by fun_prop : Continuous (Function.uncurry (fun y x : X => dist y x ^ 2)))
    (isCompact_univ : IsCompact (univ : Set X))
  change Continuous (fun y => ∫ x, dist y x ^ 2 ∂μ)
  simpa only [Measure.restrict_univ] using h

theorem exists_barycenter_variance (hX : IsCAT0 X) (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ o : X, ∀ y : X,
      squaredPotential μ o + μ.real univ * dist o y ^ 2 ≤ squaredPotential μ y := by
  obtain ⟨o,_,ho⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set X).Nonempty)
    (continuous_squaredPotential μ).continuousOn
  obtain ⟨seg,_,hs⟩ := hX.exists_squared_distance_convex
  refine ⟨o,fun y => ?_⟩
  have hbound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
      squaredPotential μ o + (1-t)*μ.real univ*dist o y^2 ≤ squaredPotential μ y := by
    have hI : Integrable (fun x => (1-t)*dist o x^2+t*dist y x^2) μ :=
      ((integrable_dist_sq μ o).const_mul (1-t)).add ((integrable_dist_sq μ y).const_mul t)
    have hh := integral_mono (integrable_dist_sq μ (seg o y t))
      (((integrable_dist_sq μ o).const_mul (1-t)).add ((integrable_dist_sq μ y).const_mul t) |>.sub (integrable_const _))
      (fun x => hs o y x t ⟨ht.le,ht1⟩)
    simp only [Pi.sub_apply,Pi.add_apply] at hh
    rw [integral_sub hI
      (integrable_const _),integral_add ((integrable_dist_sq μ o).const_mul (1-t))
      ((integrable_dist_sq μ y).const_mul t),integral_const_mul,integral_const_mul,integral_const,smul_eq_mul] at hh
    have hmin := ho (mem_univ (seg o y t))
    change squaredPotential μ o ≤ squaredPotential μ (seg o y t) at hmin
    change squaredPotential μ (seg o y t) ≤ (1-t)*squaredPotential μ o+t*squaredPotential μ y-
      μ.real univ*(t*(1-t)*dist o y^2) at hh
    have hm : t*(squaredPotential μ o+(1-t)*μ.real univ*dist o y^2-squaredPotential μ y) ≤ 0 := by
      nlinarith [hmin.trans hh]
    nlinarith
  have hlim : Tendsto (fun t : ℝ => squaredPotential μ o+(1-t)*μ.real univ*dist o y^2)
      (𝓝[>] (0:ℝ)) (𝓝 (squaredPotential μ o+μ.real univ*dist o y^2)) := by
    have h : Continuous (fun t : ℝ => squaredPotential μ o+(1-t)*μ.real univ*dist o y^2) := by fun_prop
    simpa only [sub_zero,one_mul] using (h.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
  exact hbound ht ht1.le

theorem double_distance_lower_bound (hX : IsCAT0 X) (μ : Measure X) [IsFiniteMeasure μ]
    {W : ℝ} (hall : ∀ y, W^2 ≤ μ.real univ * squaredPotential μ y) :
    2*W^2 ≤ ∫ y, squaredPotential μ y ∂μ := by
  obtain ⟨o,ho⟩ := exists_barycenter_variance hX μ
  have hi : Integrable (squaredPotential μ) μ := (continuous_squaredPotential μ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have h := integral_mono ((integrable_const _).add ((integrable_dist_sq μ o).const_mul (μ.real univ))) hi ho
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((integrable_dist_sq μ o).const_mul (μ.real univ)),
    integral_const,smul_eq_mul,integral_const_mul] at h
  change μ.real univ*squaredPotential μ o+μ.real univ*squaredPotential μ o ≤ _ at h
  linarith [hall o]
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_DoubleAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma integral_density_nonnegative {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hm : AEStronglyMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (f : X → ℝ) :
    (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x))) = ∫ x, ρ x*f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul]

lemma density_real_univ {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) :
    (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).real univ = ∫ x, ρ x ∂μ := by
  rw [measureReal_def,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi hρ,ENNReal.toReal_ofReal (integral_nonneg_of_ae hρ)]

lemma density_finite {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi hρ]
  exact ENNReal.ofReal_lt_top

lemma weighted_double_distance_lower (hX : IsCAT0 X) (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) {W : ℝ}
    (hall : ∀ y, W^2 ≤ (∫ x, ρ x ∂μ)*(∫ x, dist y x^2*ρ x ∂μ)) :
    2*W^2 ≤ ∫ y, (∫ x, dist y x^2*ρ x ∂μ)*ρ y ∂μ := by
  let η := μ.withDensity (fun x => ENNReal.ofReal (ρ x))
  let : IsFiniteMeasure η := density_finite μ hi hρ
  have hpot (y : X) : squaredPotential η y = ∫ x, dist y x^2*ρ x ∂μ := by
    rw [squaredPotential,integral_density_nonnegative μ hi.aestronglyMeasurable hρ]
    simp_rw [mul_comm (ρ _) (dist _ _^2)]
  have h := double_distance_lower_bound hX η (W := W) (fun y => by
    rw [show η.real univ = ∫ x, ρ x ∂μ from density_real_univ μ hi hρ,hpot]
    exact hall y)
  rw [integral_density_nonnegative μ hi.aestronglyMeasurable hρ] at h
  simpa only [hpot,mul_comm] using h
end CAT0Fillings
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
lemma chord_weight_identity {β : ℝ} (hb : 0 < β) {u v r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v^(2+4*β)*(u^β*r*v^β)^2 = u^(2*β)*(r^2*v^(2+6*β)) := by
  rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hu,←Real.rpow_mul_natCast hv,Nat.cast_ofNat]
  rw [show (2+6*β:ℝ) = (2+4*β)+β*2 by ring,
    Real.rpow_add' hv (by linarith : 2+4*β+β*2 ≠ 0),show β*2=2*β by ring]
  ring

lemma chord_moment_identity {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
    (hU : AEStronglyMeasurable U μ) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hW : 0 < total μ (fun x => U x^(2+4*β))) (y : X) :
    (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β))) =
    U y^(2*β)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)/total μ (fun x => U x^(2+4*β)) := by
  rw [integral_probability μ _ (hU.aemeasurable.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW]
  simp_rw [chord_weight_identity hb (hU0 y) (hU0 _)]
  rw [integral_const_mul]

lemma chord_double_identity (hU : AEStronglyMeasurable U μ) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hW : 0 < total μ (fun x => U x^(2+4*β))) :
    (∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β))) =
    (∫ y, (∫ x, dist y x^2*U x^(2+6*β) ∂μ)*U y^(2+6*β) ∂μ)/
      (total μ (fun x => U x^(2+4*β)))^2 := by
  simp_rw [chord_moment_identity μ hU hU0 hb hW]
  rw [integral_probability μ _ (hU.aemeasurable.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW]
  have he (y : X) : U y^(2+4*β)*(U y^(2*β)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)/
      total μ (fun x => U x^(2+4*β))) =
      ((∫ x, dist y x^2*U x^(2+6*β) ∂μ)*U y^(2+6*β))/total μ (fun x => U x^(2+4*β)) := by
    rw [show (2+6*β:ℝ) = (2+4*β)+2*β by ring,
      Real.rpow_add' (hU0 y) (by linarith : 2+4*β+2*β ≠ 0)]
    ring
  simp_rw [he]
  rw [integral_div]
  ring

lemma opposite_average (hX : IsCAT0 X) (hU : AEStronglyMeasurable U μ)
    (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β)
    (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β)))
    (hall : ∀ y, (total μ (fun x => U x^(2+4*β)))^2 ≤
      (∫ x, U x^(2+6*β) ∂μ)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)) :
    2 ≤ ∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β)) := by
  rw [chord_double_identity μ hU hU0 hb hW]
  apply (le_div_iff₀ (sq_pos_of_pos hW)).mpr
  exact weighted_double_distance_lower hX μ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hall
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_DensityContradiction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
lemma chord_average_integrable (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β))) :
    Integrable (fun y => ∫ x, (U y^β*dist y x*U x^β)^2
      ∂probability μ (fun x => U x^(2+4*β)))
      (probability μ (fun x => U x^(2+4*β))) := by
  let η := μ.withDensity (fun x => ENNReal.ofReal (U x^(2+6*β)))
  let : IsFiniteMeasure η := density_finite μ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _)
  have he (y : X) : squaredPotential η y = ∫ x, dist y x^2*U x^(2+6*β) ∂μ := by
    rw [squaredPotential,integral_density_nonnegative μ hi.aestronglyMeasurable
      (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _)]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hc := continuous_squaredPotential η
  have hf : AEStronglyMeasurable (fun y => U y^(2*β)*squaredPotential η y /
      total μ (fun x => U x^(2+4*β))) μ :=
    (((hU.pow_const _).mul hc.measurable).div_const _).aestronglyMeasurable
  simp_rw [chord_moment_identity μ hU.aestronglyMeasurable hU0 hb hW,←he]
  apply integrable_probability μ _ (hU.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW hf
  have hh : Integrable (fun y => U y^(2+6*β)*squaredPotential η y) μ := by
    simpa only [integrableOn_univ] using hi.integrableOn.mul_continuousOn hc.continuousOn isCompact_univ
  apply (hh.div_const _).congr
  filter_upwards [] with y
  rw [show (2+6*β:ℝ) = (2+4*β)+2*β by ring,
    Real.rpow_add' (hU0 y) (by linarith : 2+4*β+2*β ≠ 0)]
  ring

lemma average_lt_two (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hi0 : Integrable (fun x => U x^(2+4*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β)))
    (hpoint : ∀ᵐ y ∂probability μ (fun x => U x^(2+4*β)),
      (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β))) < 2) :
    (∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β))) < 2 := by
  let : IsProbabilityMeasure (probability μ (fun x => U x^(2+4*β))) :=
    isProbability μ _ hi0 (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW
  let ν := probability μ (fun x => U x^(2+4*β))
  let M (y : X) := ∫ x, (U y^β*dist y x*U x^β)^2 ∂ν
  have hiM : Integrable M ν := chord_average_integrable μ hU hU0 hb hi hW
  have hd : Integrable (fun y => 2-M y) ν := (integrable_const (2:ℝ)).sub hiM
  have hs : Function.support (fun y => 2-M y) =ᵐ[ν] (univ : Set X) := by
    filter_upwards [hpoint] with y hy
    change (2-M y ≠ 0) = True
    exact propext (iff_true_intro (sub_pos.mpr hy).ne')
  have hpos : 0 < ∫ y, (2-M y) ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpoint.mono fun y hy => (sub_pos.mpr hy).le) hd).mpr
    rw [measure_congr hs]
    simp
  rw [integral_sub (integrable_const (2:ℝ)) hiM,integral_const,
    measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hpos
  exact sub_pos.mp hpos
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
include q in
theorem density_contradiction (hX : IsCAT0 X) (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β)
    (hnb : (n:ℝ)*β = 1+2*β)
    (hi : Integrable (fun x => U x^(2+6*β)) (MassMeasure.currentMassMeasure hT))
    (hi0 : Integrable (fun x => U x^(2+4*β)) (MassMeasure.currentMassMeasure hT))
    (hW : 0 < ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))
    (hWs : ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)) < sphereArea n)
    (hall : ∀ y, (ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))^2 ≤
      (∫ x, U x^(2+6*β) ∂MassMeasure.currentMassMeasure hT)*
        (∫ x, dist y x^2*U x^(2+6*β) ∂MassMeasure.currentMassMeasure hT))
    (hd : ∀ (y : X) (a : ℝ), 0 ≤ a →
      ChordTransform.transform (ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2+4*β))) n (fun x => (U y^β*dist y x*U x^β)^2) a ≤
      (1+2*(∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β)))*a)^(-(n:ℝ)/2)) :
    False := by
  have he : 2*(n:ℝ)*β = 2+4*β := by linarith
  have ht := q.ae_current_tangent_density hn U hU hU0 hb
  have hi' : Integrable (fun x => U x^(2*(n:ℝ)*β)) (MassMeasure.currentMassMeasure hT) := by
    simpa only [he] using hi0
  have hW' : 0 < ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2*(n:ℝ)*β)) := by
    simpa only [he] using hW
  have hWs' : ChordMeasure.total (MassMeasure.currentMassMeasure hT) (fun x => U x^(2*(n:ℝ)*β)) < sphereArea n := by
    simpa only [he] using hWs
  have hm : ∀ᵐ y ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2+4*β)),
      (∫ x, (U y^β*dist y x*U x^β)^2
        ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT) (fun x => U x^(2+4*β))) < 2 := by
    conv at ht => rw [he]
    filter_upwards [ht] with y hy
    have h := TangentDensity.moment_lt_two (MassMeasure.currentMassMeasure hT) U hU hU0 n y
      hi' hW' hWs' hy (by simpa only [he] using hd y)
    simpa only [he] using h
  have hlo := ChordMeasure.opposite_average (MassMeasure.currentMassMeasure hT) hX
    hU.aestronglyMeasurable hU0 hb hi hW hall
  have hup := ChordMeasure.average_lt_two (MassMeasure.currentMassMeasure hT) hU hU0 hb hi hi0 hW hm
  exact (not_lt_of_ge hlo) hup
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_CriticalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma criticalMass_integrable (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H)
    (h : MemLp (I u) (ENNReal.ofReal p) μ) : Integrable (fun x => |(I u) x|^p) μ := by
  simpa only [toReal_ofReal hp.le,Real.norm_eq_abs] using h.integrable_norm_rpow (by positivity) ofReal_ne_top

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_EulerMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_power_iff {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) {a b : ℝ} (ha : 0 < a) :
    MemLp (fun x => (f x)^a) (ENNReal.ofReal b) μ ↔ MemLp f (ENNReal.ofReal (a*b)) μ := by
  have he : ENNReal.ofReal (a*b) / ENNReal.ofReal a = ENNReal.ofReal b := by
    rw [←ENNReal.ofReal_div_of_pos ha]
    congr 1
    field_simp
  have hh := memLp_norm_rpow_iff (p := ENNReal.ofReal (a*b)) hf
    (show ENNReal.ofReal a ≠ 0 by positivity) ENNReal.ofReal_ne_top
  rw [he,ENNReal.toReal_ofReal ha.le] at hh
  have hae : (fun x => ‖f x‖^a) =ᵐ[μ] (fun x => (f x)^a) := by
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg hx]
  exact (memLp_congr_ae hae).symm.trans hh

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Powers_PolynomialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [IsFiniteMeasure μ]
lemma power_memLp_two {f : α → ℝ} (hp : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hm : ∀ b : ℝ, 0 < b → MemLp f (ENNReal.ofReal b) μ) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x => (f x)^a) 2 μ := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa only [Real.rpow_zero] using (memLp_const (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ)
  · have h := (memLp_power_iff (hm 2 (by norm_num)).aestronglyMeasurable hp ha (b := 2)).mpr
      (hm (a*2) (by positivity))
    simpa using h

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CAT0Fillings.Conformal
lemma beta_dimension {n β : ℝ} (hb : 0 < β) (hn : n*β = 1+2*β) : 2 < n := by
  exact (mul_lt_mul_iff_of_pos_right hb).mp (by linarith : 2*β < n*β)
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  (μ : Measure X) [IsFiniteMeasure μ] {v : X → ℝ}
omit [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ] in
lemma chord_measurable [CompactSpace X] [Nonempty X] [IsFiniteMeasure μ]
    (o : X) (hv : AEStronglyMeasurable v μ) (κ β : ℝ) :
    AEStronglyMeasurable (fun x => κ*dist o x*(v x)^β) μ := by
  exact (aestronglyMeasurable_const.mul (continuous_const.dist continuous_id).aestronglyMeasurable).mul
    (hv.aemeasurable.pow_const _).aestronglyMeasurable
omit [MetricSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma integral_power [MetricSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp v (ENNReal.ofReal b) μ) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x => (v x)^p) μ :=
  (ClosedCalculus.power_memLp_two hv hm hp).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
lemma chord_second_moment (o : X) (hv : ∀ᵐ x ∂μ, 0 ≤ v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp v (ENNReal.ofReal b) μ) {β : ℝ} (hb : 0 < β)
    (hW : 0 < total μ (fun x => |v x|^(2+4*β))) (κ : ℝ) :
    Integrable (fun x => (κ*dist o x*(v x)^β)^2)
      (probability μ (fun x => |v x|^(2+4*β))) := by
  have hvm := (hm 2 (by norm_num)).aestronglyMeasurable
  have hsm := chord_measurable μ o hvm κ β
  apply integrable_probability μ _ (hvm.aemeasurable.abs.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _) hW (hsm.pow 2)
  have hp := integral_power μ hv hm (p := 2+6*β) (by positivity)
  have hi : Integrable (fun x => |v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2) μ := by
    apply (hp.const_mul (κ^2*Metric.diam (univ : Set X)^2)).mono'
      (((hvm.aemeasurable.abs.pow_const _).aestronglyMeasurable).mul (hsm.pow 2))
    filter_upwards [hv] with x hx
    have hpw : |v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2 = κ^2*dist o x^2*(v x)^(2+6*β) := by
      rw [abs_of_nonneg hx,mul_pow,mul_pow,←Real.rpow_mul_natCast hx,Nat.cast_ofNat]
      rw [show (2+6*β:ℝ) = (2+4*β)+β*2 by ring,
        Real.rpow_add' hx (by linarith : 2+4*β+β*2 ≠ 0)]
      ring
    change ‖|v x|^(2+4*β)*(κ*dist o x*(v x)^β)^2‖ ≤ _
    rw [hpw,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hdist := ChartGeometry.radius_bound o x
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ dist_nonneg hdist 2) (sq_nonneg κ)) (Real.rpow_nonneg hx _)
  exact hi
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
theorem chord_distribution (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β : ℝ}
    (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) {a : ℝ} (ha : 0 ≤ a) :
    let μ := MassMeasure.currentMassMeasure hT
    let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
    let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
    ChordTransform.transform ν (k+1) b a ≤
      (1+2*(∫ x, b x ∂ν)*a)^(-(k+1:ℝ)/2) := by
  let μ := MassMeasure.currentMassMeasure hT
  let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
  have hp : 0 < 2+4*β := by positivity
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ _
    (AnalyticMinimizer.criticalMass_integrable q.inclusion hp v (hm _ hp))
    (Eventually.of_forall fun point => Real.rpow_nonneg (abs_nonneg (q.inclusion v point)) _) hW
  apply ChordTransform.distribution_bound ν
    (ChordMeasure.chord_second_moment μ o hv hm hb hW κ)
    (Eventually.of_forall fun point => sq_nonneg (κ*dist o point*(q.inclusion v point)^β))
    (beta_dimension hb hn) ?_ ha
  intro a ha
  exact q.chord_scalar_average hz o v hb ha hn hv hm hpow heuler hr hW hE hmin
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Euler_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ σ : X → ℝ}
lemma total_congr (h : ρ =ᵐ[μ] σ) : total μ ρ = total μ σ := integral_congr_ae h
lemma probability_congr (h : ρ =ᵐ[μ] σ) : probability μ ρ = probability μ σ := by
  rw [probability,probability,total_congr h]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]
lemma ae_of_ae (h : ∀ᵐ x ∂μ, ρ x = σ x) (w : X → ℝ) :
    ρ =ᵐ[probability μ w] σ := withDensity_absolutelyContinuous _ _ h
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Euler_Contradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
theorem euler_chord_contradiction_oai (hX : IsCAT0 X) (hk : 2 < k+1) (hz : IsCycle T)
    (v : q.Sobolev) {β : ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (o : X) (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < criticalMass q.inclusion (2+4*β) v)
    (hWs : criticalMass q.inclusion (2+4*β) v < sphereArea (k+1))
    (hE : energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (criticalNorm q.inclusion (2+4*β) P)^2 ≤
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (criticalNorm q.inclusion (2+4*β) v)^2) : False := by
  let μ := MassMeasure.currentMassMeasure hT
  obtain ⟨U,hU,hU0,heq⟩ := ChordMeasure.exists_nonnegative_borel (hm 2 (by norm_num)).aestronglyMeasurable hv
  have hpowEq (p : ℝ) : (fun x => U x^p) =ᵐ[μ] (fun x => q.inclusion v x^p) :=
    heq.mono fun x hx => congrArg (fun t : ℝ => t^p) hx
  have hρ : (fun x => U x^(2+4*β)) =ᵐ[μ] (fun x => |q.inclusion v x|^(2+4*β)) := by
    filter_upwards [heq,hv] with x hx hp
    rw [hx,abs_of_nonneg hp]
  have hmass : ChordMeasure.total μ (fun x => U x^(2+4*β)) = criticalMass q.inclusion (2+4*β) v :=
    integral_congr_ae hρ
  have hip (p : ℝ) (hp : 0 ≤ p) : Integrable (fun x => U x^p) μ :=
    (ChordMeasure.integral_power μ hv hm hp).congr (hpowEq p).symm
  have hν := ChordMeasure.probability_congr hρ
  have heν := ChordMeasure.ae_of_ae heq (fun x => |q.inclusion v x|^(2+4*β))
  apply q.density_contradiction hX hk U hU hU0 hb (by simpa only [Nat.cast_add,Nat.cast_one] using hn)
    (hip _ (by positivity)) (hip _ (by positivity)) (by rwa [hmass]) (by rwa [hmass])
  · intro y
    have hI : (∫ x, dist y x^2*U x^(2+6*β) ∂μ) =
        ∫ x, dist y x^2*(q.inclusion v x)^(2+6*β) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpowEq (2+6*β)] with x hx
      rw [hx]
    rw [ChordMeasure.total,integral_congr_ae (hpowEq (2+4*β)),
      integral_congr_ae (hpowEq (2+6*β)),hI]
    exact q.opposite_all_center hz y v hb hn hv hm hpow heuler (hr y)
  · intro y a ha
    have hP : (fun x => (U y^β*dist y x*U x^β)^2) =ᵐ[ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))] (fun x => (U y^β*dist y x*(q.inclusion v x)^β)^2) := by
      filter_upwards [heν] with x hx
      rw [hx]
    have htrans : ChordTransform.transform (ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))) (k+1)
        (fun x => (U y^β*dist y x*U x^β)^2) a =
        ChordTransform.transform (ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))) (k+1)
        (fun x => (U y^β*dist y x*(q.inclusion v x)^β)^2) a := by
      apply integral_congr_ae
      filter_upwards [hP] with x hx
      simp only [hx]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hν,htrans,integral_congr_ae hP]
    exact q.chord_distribution hz y v hb hn hv hm (fun γ hγ => by
      obtain ⟨R,_,hR⟩ := hpow γ hγ
      exact ⟨R,hR⟩) heuler (hr y) hW hE hmin ha
end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction_oai.{u_1}
