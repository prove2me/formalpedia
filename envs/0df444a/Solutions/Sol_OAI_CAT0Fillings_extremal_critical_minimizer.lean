-- Prove2me | solution 1 for OAI.CAT0Fillings.extremal_critical_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:08:53.208923+00:00
-- url     : https://prove2.me/submissions/ff5c7c86-ae1f-44de-a376-50368805d73c

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_inclusion_compact
import Theorems.Thm_OAI_CAT0Fillings_extremal_closed_sobolev
import Theorems.Thm_OAI_CAT0Fillings_small_restriction_mass_bound

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

lemma beta_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x^(a-1)*(1-x)^(b-1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (b:ℂ)) ha hb
  have hr : IntervalIntegrable
      (fun x : ℝ => ((x:ℂ)^((a:ℂ)-1)*(1-(x:ℂ))^((b:ℂ)-1)).re) volume 0 1 :=
    ⟨hc.1.re,hc.2.re⟩
  apply hr.congr_uIoo
  rw [uIoo_of_le zero_le_one]
  intro x hx
  dsimp only
  rw [←beta_integrand_coe a b x ⟨hx.1.le,hx.2.le⟩]
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

lemma bubble_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r^(2*a-1)*(1+r^2)^(-(a+b))) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1)*(1-t)^(b-1)) (Ioo 0 1) :=
    (beta_integrable ha hb).1.mono_set Ioo_subset_Ioc_self
  rw [←betaRadius_image] at hi
  have h := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioi (fun r _ => (betaRadius_deriv r).hasDerivWithinAt)
    betaRadius_mono _).mp hi
  have h' : IntegrableOn (fun r : ℝ => 2*(r^(2*a-1)*(1+r^2)^(-(a+b)))) (Ioi 0) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    exact bubble_substitution_algebra hr
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℝ) ≠ 0)) _).mp h'

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

lemma sobolev_exponents {n : ℕ} (hn : 2 < n) :
    0 < sobolevP n ∧ 1 ≤ sobolevQ n ∧ sobolevQ n+sobolevP n/(n:ℝ)=sobolevP n ∧
      2*(sobolevQ n-1)=sobolevP n ∧ 2*sobolevQ n-sobolevP n=2 := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  dsimp [sobolevP,sobolevQ]
  have hd : 0 < (n:ℝ)-2 := by linarith
  refine ⟨div_pos (by positivity) hd, (le_div_iff₀ hd).mpr (by linarith), ?_, ?_, ?_⟩ <;>
    field_simp <;> ring

lemma bubble_pos (n : ℕ) (r : ℝ) : 0 < bubble n r :=
  Real.rpow_pos_of_pos (by positivity) _

lemma bubble_continuous (n : ℕ) : Continuous (bubble n) := by
  apply Continuous.rpow_const
  · fun_prop
  · intro r
    exact Or.inl (by positivity)

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

lemma bubble_moments_integrable {n : ℕ} (hn : 2 < n) :
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevP n)) (Ioi 0) ∧
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevQ n)) (Ioi 0) ∧
    IntegrableOn (fun r : ℝ => r^(n-1)*(bubble n r)^(sobolevP n)*r^2) (Ioi 0) := by
  have h : (2:ℝ) < n := by exact_mod_cast hn
  refine ⟨?_,?_,?_⟩
  · apply (bubble_integrable (a := (n:ℝ)/2) (b := (n:ℝ)/2) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).1.symm) measurableSet_Ioi
  · apply (bubble_integrable (a := (n:ℝ)/2) (b := (n:ℝ)/2-1) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).2.1.symm) measurableSet_Ioi
  · apply (bubble_integrable (a := (n:ℝ)/2+1) (b := (n:ℝ)/2-1) (by linarith) (by linarith)).congr_fun
      (fun r hr => (bubbleMoment_algebra hn hr).2.2.symm) measurableSet_Ioi

lemma bubble_mass_pos {n : ℕ} (hn : 2 < n) : 0 < bubbleMass n := by
  have h : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact div_pos (sq_pos_of_pos (Real.Gamma_pos_of_pos (by positivity)))
    (mul_pos (by norm_num) (Real.Gamma_pos_of_pos h))

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

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_LevelLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma LipschitzWith.ae_fderiv_zero_on_level {F : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (c : ℝ) :
    ∀ᵐ x ∂μ, F x = c → fderiv ℝ F x = 0 := by
  have hset : MeasurableSet {x | F x = c} := isClosed_eq hF.continuous continuous_const |>.measurableSet
  apply (ae_restrict_iff' hset).mp
  have heq : EqOn F (fun _ => c) {x | F x = c} := fun _ hx => hx
  filter_upwards [ae_uniqueDiffWithinAt μ {x | F x = c},ae_restrict_mem hset,
    (hF.ae_differentiableAt (μ := μ)).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hx hxc hd
  rw [← fderivWithin_eq_fderiv hx hd, fderivWithin_congr' heq hxc]
  simpa only [Function.const_def,Pi.zero_apply] using
    congrFun (fderivWithin_const (𝕜 := ℝ) (E := E) (s := {x | F x = c}) c) x

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Chart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators Matrix.Norms.L2Operator

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

attribute [local instance] OAI.CAT0Fillings.ChartGeometry.instMeasurableSpaceMatrixFinReal
local instance instBorelSpaceMatrixFinReal : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

lemma aestronglyMeasurable_normSq (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.normSq i u)
      (volume.restrict (q.chart i).domain) := by
  have hc : Continuous (fun r : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
      r.1 ⬝ᵥ r.2.mulVec r.1) := by fun_prop
  exact hc.comp_aestronglyMeasurable ((q.aestronglyMeasurable_covector i hu).prodMk
    (measurable_matrix_inverse _ (q.measurable_gram i)).aestronglyMeasurable)

lemma aestronglyMeasurable_duNorm (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.duNorm i u)
      (volume.restrict (q.chart i).domain) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable (q.aestronglyMeasurable_normSq i hu)

lemma ae_duNorm_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.duNorm i u z ∧ q.duNorm i u z ≤ (K : ℝ) ∧
      q.duNorm i u z ^2 = q.normSq i u z := by
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left K.coe_nonneg).mpr hz.2, Real.sq_sqrt hz.1⟩

lemma integrable_gradient (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Integrable (fun z => q.density i z * q.duNorm i u z)
      (volume.restrict (q.chart i).domain) := by
  apply ((q.density_integrable i).mul_const (K : ℝ)).mono'
    ((q.density_integrable i).aestronglyMeasurable.mul (q.aestronglyMeasurable_duNorm i hu))
  filter_upwards [q.ae_duNorm_bounds i hu] with z hz
  have density_nonneg : 0 ≤ q.density i z :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg density_nonneg hz.1)]
  exact mul_le_mul_of_nonneg_left hz.2.1 density_nonneg

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators MatrixOrder

namespace CAT0Fillings

lemma abs_det_le_prod_dual_norm {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    |L.det| ≤ (∏ i, Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i))) * Real.sqrt P.det := by
  let Q := CFC.sqrt P⁻¹
  have hQsym : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P⁻¹).posSemidef.isHermitian).eq
  have hQdet : Q.det = (Real.sqrt P.det)⁻¹ := by
    have hh := hP.inv.posSemidef.det_sqrt
    simpa only [Q,RCLike.sqrt_real,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
      Real.sqrt_inv] using hh
  have hJ : 0 < Real.sqrt P.det := Real.sqrt_pos.mpr hP.det_pos
  have hrow (i : Fin n) : (L * Q) i = Q.mulVec (L i) := by
    ext j
    change (∑ t, L i t * Q t j) = ∑ t, Q j t * L i t
    apply Finset.sum_congr rfl
    intro t ht
    have hs : Q t j = Q j t := congrFun (congrFun hQsym j) t
    rw [hs,mul_comm]
  have hnorm (i : Fin n) :
      ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i)) := by
    have hn : ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖^2 =
        L i ⬝ᵥ P⁻¹.mulVec (L i) := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hrow]
      exact (dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef (L i)).symm
    rw [←hn,Real.sqrt_sq (norm_nonneg _)]
  have heq : |L.det| = |(L*Q).det| * Real.sqrt P.det := by
    rw [Matrix.det_mul,abs_mul,hQdet,abs_of_pos (inv_pos.mpr hJ)]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hJ.le
  simpa only [hnorm] using abs_det_le_prod_row_norm (L*Q)

lemma abs_det_le_first_dual_norm {n : ℕ} (L P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef)
    (hL : ∀ i : Fin n, Real.sqrt (L i.succ ⬝ᵥ P⁻¹.mulVec (L i.succ)) ≤ 1) :
    |L.det| ≤ Real.sqrt (L 0 ⬝ᵥ P⁻¹.mulVec (L 0)) * Real.sqrt P.det := by
  apply (abs_det_le_prod_dual_norm L P hP).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [Fin.prod_univ_succ]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _)
    (Finset.prod_le_one (fun i _ => Real.sqrt_nonneg _) (fun i _ => hL i))

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem ae_jacobian_le_duNorm (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      |(q.chart i).jacobian (Fin.cons u π) z| ≤
        q.duNorm i u z * Real.sqrt (q.gram i z).det := by
  have hp : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ∀ j, q.duNorm i ((Fin.cons u π : Fin (k+1) → X → ℝ) j) z ≤
        (Fin.cons (K : ℝ) (fun _ => (1 : ℝ)) : Fin (k+1) → ℝ) j := by
    rw [eventually_all]
    intro coordinate
    refine Fin.cases ?_ (fun tail => ?_) coordinate
    · exact (q.ae_duNorm_bounds i hu).mono fun _ bounds => bounds.2.1
    · exact (q.ae_duNorm_bounds i (hπ tail)).mono fun _ bounds => by simpa using bounds.2.1
  filter_upwards [q.differential i,hp] with z hz hpz
  apply abs_det_le_first_dual_norm _ _
    (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1)
  intro j
  exact hpz j.succ

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_HilbertAtlas
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma weightedMeasure_le {v : ℕ → Euc k → ℝ} {c : ℝ≥0}
    (hv : ∀ i, ∀ᵐ z ∂volume.restrict (q.chart i).domain, v i z ≤ c) :
    q.weightedMeasure v ≤ c • MassMeasure.currentMassMeasure hT := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedMeasure,Measure.sum_apply _ hs,Measure.smul_apply,q.measure_eq,
    Measure.sum_apply _ hs]
  change _ ≤ (c : ℝ≥0∞) * _
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  have hi := densityPush_mono_ae (q.chart i).measurable_paramExtended
    ((hv i).mono fun z hz => (mul_le_mul_of_nonneg_left hz (q.density_nonneg i z)).trans_eq
      (mul_comm _ _))
  rw [densityPush_const_mul _ _ _ _ (q.chart i).measurable_paramExtended] at hi
  exact hi s

lemma gradientMeasure_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.gradientMeasure u ≤ K • MassMeasure.currentMassMeasure hT :=
  q.weightedMeasure_le (fun i => (q.ae_duNorm_bounds i hu).mono fun _ hz => hz.2.1)

lemma energyMeasure_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.energyMeasure u ≤ K^2 • MassMeasure.currentMassMeasure hT := by
  apply q.weightedMeasure_le
  intro i
  simpa only [NNReal.coe_pow] using (q.ae_normSq_bounds i hu).mono (fun _ hz => hz.2)

lemma gradientMeasure_finite {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    IsFiniteMeasure (q.gradientMeasure u) :=
  isFiniteMeasure_of_le _ (q.gradientMeasure_le hu)

lemma energyMeasure_finite {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    IsFiniteMeasure (q.energyMeasure u) :=
  isFiniteMeasure_of_le _ (q.energyMeasure_le hu)

lemma integral_gradientMeasure {u w : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hw : Continuous w) :
    (∫ x, w x ∂q.gradientMeasure u) = ∑' i, ∫ z,
      (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain := by
  let := q.gradientMeasure_finite hu
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := q.gradientMeasure u)
  rw [gradientMeasure,weightedMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_gradient i hu)
    (Eventually.of_forall fun z => mul_nonneg (q.density_nonneg i z) (Real.sqrt_nonneg _)) hw

lemma gradient_summable {u w : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hw : Continuous w) :
    Summable (fun i => ∫ z,
      (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) := by
  let := q.gradientMeasure_finite hu
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := q.gradientMeasure u)
  apply (hasSum_integral_measure hi).summable.congr
  intro i
  exact integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_gradient i hu)
    (Eventually.of_forall fun z => mul_nonneg (q.density_nonneg i z) (Real.sqrt_nonneg _)) hw

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_ClosedLinear
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma norm_value {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖value (hT := hT) hu‖ = lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  rw [value,Lp.norm_toLp,toReal_eLpNorm hu.continuous.aestronglyMeasurable]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_TestDensity
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma integrable_gradient_weight (i : ℕ) {u w : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hw : Continuous w) :
    Integrable (fun z => (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z))
      (volume.restrict (q.chart i).domain) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
  exact (q.integrable_gradient i hu).mul_bdd
    (hw.measurable.comp (q.chart i).measurable_paramExtended).aestronglyMeasurable
    (Eventually.of_forall fun z => hB _ (mem_univ _))

lemma chart_action_le_gradient (i : ℕ) {u b : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |(q.chart i).action b (Fin.cons u π)| ≤ ∫ z,
      (q.density i z * q.duNorm i u z)*|b ((q.chart i).paramExtended z)|
      ∂volume.restrict (q.chart i).domain := by
  have hc : ∀ j : Fin (k+1), ∃ L : ℝ≥0, LipschitzWith L ((Fin.cons u π : Fin (k+1) → X → ℝ) j) :=
    by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨K,hu⟩
      · exact ⟨1,hπ j⟩
  rw [IntegerChart.action,ite_eq_left ⟨hb,hc⟩]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_ae ((q.chart i).integrable_action_integrand hb hc).abs
    (q.integrable_gradient_weight i hu hb.continuous.abs)
  filter_upwards [q.ae_jacobian_le_duNorm i hu π hπ,ae_restrict_mem (q.chart i).borel]
    with z hz hzi
  simp only [abs_mul,(q.chart i).scalar_eq hzi,IntegerChart.paramExtended,dite_eq_left hzi]
  calc
    _ ≤ |((q.chart i).multiplicity z : ℝ)| * |b ((q.chart i).param ⟨z,hzi⟩)| *
        (q.duNorm i u z * Real.sqrt (q.gram i z).det) := by gcongr
    _ = _ := by simp only [density]; ring

lemma action_le_gradient {u b : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |T b (Fin.cons u π)| ≤ ∫ x, |b x| ∂q.gradientMeasure u := by
  have hs := q.gradient_summable hu hb.continuous.abs
  have hbnd := fun i => q.chart_action_le_gradient i hu hb π hπ
  have hsa : Summable (fun i => (q.chart i).action b (Fin.cons u π)) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hbnd i)
  rw [q.action,q.integral_gradientMeasure hu hb.continuous.abs]
  calc
    |∑' i, (q.chart i).action b (Fin.cons u π)| ≤
        ∑' i, |(q.chart i).action b (Fin.cons u π)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsa.norm
    _ ≤ _ := hsa.abs.tsum_le_tsum hbnd hs

theorem list_action_le_gradient {N : ℕ} {u w : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hw : BoundedLip w)
    (b : Fin N → X → ℝ) (hb : ∀ i, BoundedLip (b i))
    (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    |∑ i, T (fun x => w x*b i x) (Fin.cons u (π i))| ≤
      ∫ x, |w x| ∂q.gradientMeasure u := by
  let := q.gradientMeasure_finite hu
  have hi i : Integrable (fun x => |w x*b i x|) (q.gradientMeasure u) :=
    (BorelCoefficients.integrable_boundedLip _ (hw.mul (hb i))).abs
  calc
    _ ≤ ∑ i, |T (fun x => w x*b i x) (Fin.cons u (π i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∫ x, |w x*b i x| ∂q.gradientMeasure u := Finset.sum_le_sum fun i _ =>
      q.action_le_gradient hu (hw.mul (hb i)) _ (hπ i)
    _ = ∫ x, ∑ i, |w x*b i x| ∂q.gradientMeasure u :=
      (integral_finsetSum _ fun i _ => hi i).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum _ fun i _ => hi i)
        (BorelCoefficients.integrable_boundedLip _ hw).abs
      intro x
      simp_rw [abs_mul,←Finset.mul_sum]
      exact mul_le_of_le_one_right (abs_nonneg _) (hbudget x)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma l2ToL1_coe (f : Lp ℝ 2 μ) : (l2ToL1 μ f : X → ℝ) =ᵐ[μ] f :=
  (integrable_l2 μ f).coeFn_toL1

variable [MetricSpace X] [CompactSpace X] [BorelSpace X]

theorem exists_coefficient_density {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (hμ : Controls T μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∃ ρ : X → ℝ, AEStronglyMeasurable ρ μ ∧ Integrable ρ μ ∧
      (∀ᵐ x ∂μ, |ρ x| ≤ 1) ∧
      ∀ b : X → ℝ, BoundedLip b → T b π = ∫ x, b x *ρ x ∂μ := by
  let L := (l1Action μ hT π (fun i => ⟨1,hπ i⟩)).comp (l2ToL1 μ)
  let f : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm L
  have hrepr (v : Lp ℝ 2 μ) : L v = ∫ x, f x *v x ∂μ := by
    have hh := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Lp ℝ 2 μ)
      (x := v) (y := L)
    simpa only [f,L2.inner_def,RCLike.inner_apply,conj_trivial,mul_comm] using hh.symm
  have hbound (v : Lp ℝ 2 μ) : |∫ x, f x*v x ∂μ| ≤ ∫ x, |v x| ∂μ := by
    rw [←hrepr]
    have hh := l1Action_bound μ hT hμ π (fun _ => 1) hπ (l2ToL1 μ v)
    simp only [NNReal.coe_one,Finset.prod_const_one,one_mul] at hh
    apply hh.trans_eq
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [l2ToL1_coe μ v] with x hx
    rw [hx,Real.norm_eq_abs]
  have hfi : Integrable (fun x => f x) μ := integrable_l2 μ f
  have hdom : ∀ s : Set X, MeasurableSet s → |∫ x in s, f x ∂μ| ≤ μ.real s := by
    intro s hs
    let v := indicatorConstLp 2 hs (measure_ne_top μ s) (1:ℝ)
    have hh := hbound v
    have hveq : (v : X → ℝ) =ᵐ[μ] s.indicator (fun _ => 1) :=
      indicatorConstLp_coeFn
    have hv1 : (fun x => f x*v x) =ᵐ[μ] s.indicator (fun x => f x) := by
      filter_upwards [hveq] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    have hv2 : (fun x => |v x|) =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := by
      filter_upwards [hveq] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [integral_congr_ae hv1,integral_congr_ae hv2,integral_indicator hs,
      integral_indicator hs] at hh
    simpa using hh
  have hle : ∀ᵐ x ∂μ, f x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le hfi (integrable_const (1:ℝ))
    intro s hs hsf
    simpa using (le_abs_self (∫ x in s, f x ∂μ)).trans (hdom s hs)
  have hge : ∀ᵐ x ∂μ, -f x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le hfi.neg (integrable_const (1:ℝ))
    intro s hs hsf
    simp only [Pi.neg_apply,integral_neg]
    simpa using (neg_le_abs (∫ x in s, f x ∂μ)).trans (hdom s hs)
  refine ⟨f,Lp.aestronglyMeasurable f,hfi,?_,?_⟩
  · filter_upwards [hle,hge] with x hx hy
    exact abs_le.mpr ⟨by linarith,hx⟩
  · intro b hb
    let B : C(X,ℝ) := ⟨b,hb.continuous⟩
    let v := ContinuousMap.toLp 2 μ ℝ B
    have hveq : (v : X → ℝ) =ᵐ[μ] b := ContinuousMap.coeFn_toLp μ B
    have hv : l2ToL1 μ v = (integrable_boundedLip μ hb).toL1 b := by
      apply Lp.ext
      exact ((l2ToL1_coe μ v).trans hveq).trans
        (integrable_boundedLip μ hb).coeFn_toL1.symm
    have hh := hrepr v
    change l1Action μ hT π (fun i => ⟨1,hπ i⟩) (l2ToL1 μ v) = _ at hh
    rw [hv,←borelAction_of_integrable μ hT (integrable_boundedLip μ hb),
      borelAction_eq μ hT hμ ⟨hb,fun i => ⟨1,hπ i⟩⟩] at hh
    rw [hh]
    apply integral_congr_ae
    filter_upwards [hveq] with x hx
    rw [hx,mul_comm]

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Approximation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ}

theorem exists_measurable_coefficient_density {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : Controls T μ) (π : Fin k → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∃ ρ : X → ℝ, Measurable ρ ∧ (∀ x, |ρ x| ≤ 1) ∧
      ∀ b : X → ℝ, BoundedLip b → T b π = ∫ x, b x * ρ x ∂μ := by
  obtain ⟨r,hrm,hri,hr1,hr⟩ := exists_coefficient_density μ hT hμ π hπ
  let ρ := fun x => max (-1) (min 1 (hrm.mk r x))
  have heq : ρ =ᵐ[μ] r := by
    filter_upwards [hrm.ae_eq_mk,hr1] with x hx hy
    dsimp only [ρ]
    rw [←hx,min_eq_right (abs_le.mp hy).2,max_eq_right (abs_le.mp hy).1]
  refine ⟨ρ,measurable_const.max (measurable_const.min hrm.stronglyMeasurable_mk.measurable),?_,?_⟩
  · intro x
    exact abs_le.mpr ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · intro b hb
    rw [hr b hb]
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]

theorem exists_mass_spectrum (k : ℕ) :
    ∃ π : ℕ → Fin k → X → ℝ, (∀ j i, LipschitzWith 1 (π j i)) ∧
      ∀ {T : Functional X k} (hT : IsMetricCurrent T),
      ∃ ρ : ℕ → X → ℝ,
        (∀ j, Measurable (ρ j)) ∧ (∀ j x, |ρ j x| ≤ 1) ∧
        (∀ j b, BoundedLip b → T b (π j) =
          ∫ x, b x * ρ j x ∂MassMeasure.currentMassMeasure hT) ∧
        mass T = ∫ x, ⨆ j, |ρ j x| ∂MassMeasure.currentMassMeasure hT := by
  obtain ⟨b,π,ht,hdet⟩ := Foundations.exists_countable_mass_tests (X := X) k
  let tup j := π (Nat.unpair j).1 (Nat.unpair j).2
  refine ⟨tup,fun j => (ht _ _).2,?_⟩
  intro T hT
  let μ := MassMeasure.currentMassMeasure hT
  have hμ : Controls T μ := MassMeasure.currentMassMeasure_controls hT
  choose ρ hρm hρ1 hρ using fun j =>
    exists_measurable_coefficient_density hT μ hμ (tup j) ((ht _ _).2)
  let R x := ⨆ j, |ρ j x|
  have hbd x : BddAbove (range (fun j => |ρ j x|)) := ⟨1,by rintro _ ⟨j,rfl⟩; exact hρ1 j x⟩
  have hR0 x : 0 ≤ R x := (abs_nonneg (ρ 0 x)).trans (le_ciSup (hbd x) 0)
  have hR1 x : R x ≤ 1 := ciSup_le (hρ1 · x)
  have hRm : Measurable R := Measurable.iSup (fun j => (hρm j).abs)
  have hRi : Integrable R μ := Integrable.mono' (integrable_const (1:ℝ)) hRm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 x)]; exact hR1 x)
  let ν := μ.withDensity (fun x => ENNReal.ofReal (R x))
  have hνle : ν ≤ μ := by
    calc ν ≤ μ.withDensity (fun _ => 1) := withDensity_mono (Eventually.of_forall fun x => by
          simpa using ENNReal.ofReal_le_ofReal (hR1 x))
         _ = μ := withDensity_one
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hνint (f : X → ℝ) : (∫ x, f x ∂ν) = ∫ x, R x*f x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul (hRm.ennreal_ofReal)]
    · simp only [ENNReal.toReal_ofReal (hR0 _),smul_eq_mul]
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hνc : Controls T ν := by
    apply hdet T hT ν inferInstance
    intro K j
    have hh := hρ (Nat.pair K j) (b K j) (ht K j).1
    simp only [tup,Nat.unpair_pair] at hh
    rw [hh,hνint]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono
    · exact ((BorelCoefficients.integrable_boundedLip μ (ht K j).1).abs).mono'
        (((ht K j).1.continuous.measurable.mul (hρm _)).abs.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs,abs_abs,abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hρ1 _ _))
    · exact (BorelCoefficients.integrable_boundedLip μ (ht K j).1).abs.bdd_mul hRm.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 x)]; exact hR1 x)
    · intro x
      dsimp only
      rw [abs_mul,mul_comm (R x)]
      exact mul_le_mul_of_nonneg_left (le_ciSup (hbd x) (Nat.pair K j)) (abs_nonneg _)
  have htotal : mass T ≤ ∫ x, R x ∂μ := by
    calc mass T ≤ ν.real univ := mass_le_measure inferInstance hνc
         _ = ∫ x, (1:ℝ) ∂ν := by simp
         _ = ∫ x, R x ∂μ := by rw [hνint]; simp
  refine ⟨ρ,hρm,hρ1,hρ,le_antisymm htotal ?_⟩
  calc (∫ x, R x ∂μ) ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hRi (integrable_const _) hR1
       _ = mass T := by simpa only [integral_const,smul_eq_mul,mul_one] using
          MassMeasure.currentMassMeasure_total hT

end BorelCoefficients
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients

lemma abs_div_sub_div_le {a b A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hb : |b| ≤ B) : |a/A-b/B| ≤ |a-b|+|A-B| := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  calc |a/A-b/B| = |(a-b)/A+b*(B-A)/(A*B)| := by
         congr 1; field_simp; ring
       _ ≤ |(a-b)/A|+|b*(B-A)/(A*B)| := abs_add_le _ _
       _ = |a-b|/A+|b| *|A-B|/(A*B) := by
         rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hA0,abs_of_pos hB0,abs_sub_comm B A]
       _ ≤ |a-b|+|A-B| := by
         apply add_le_add
         · exact div_le_self (abs_nonneg _) hA
         · apply (div_le_iff₀ (mul_pos hA0 hB0)).mpr
           calc |b| *|A-B| ≤ B*|A-B| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
                _ ≤ |A-B| *(A*B) := by
                  have hh := mul_le_mul_of_nonneg_left hA hB0.le
                  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (A-B))]

variable {ι : Type*} [Fintype ι]

lemma coefficientScale_one_le (v : ι → ℝ) : 1 ≤ coefficientScale v := le_max_left _ _
lemma abs_le_coefficientScale (v : ι → ℝ) (i : ι) : |v i| ≤ coefficientScale v :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans (le_max_right _ _)
lemma normalizeCoefficients_budget (v : ι → ℝ) : ∑ i, |normalizeCoefficients v i| ≤ 1 := by
  simp only [normalizeCoefficients,abs_div,abs_of_pos (lt_of_lt_of_le zero_lt_one (coefficientScale_one_le v)),
    ←Finset.sum_div]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (coefficientScale_one_le v))).mpr (le_max_right _ _)
lemma normalizeCoefficients_fixed (v : ι → ℝ) (hv : ∑ i, |v i| ≤ 1) :
    normalizeCoefficients v = v := by
  funext i
  simp only [normalizeCoefficients,coefficientScale,max_eq_left hv,div_one]

lemma abs_coefficientScale_sub_le (v w : ι → ℝ) :
    |coefficientScale v-coefficientScale w| ≤ ∑ i, |v i-w i| := by
  calc |coefficientScale v-coefficientScale w| ≤ |(∑ i, |v i|)-(∑ i, |w i|)| := by
         simpa [coefficientScale,Real.dist_eq,max_comm] using
           (LipschitzWith.id.max (LipschitzWith.const (1:ℝ))).dist_le_mul
             (∑ i, |v i|) (∑ i, |w i|)
       _ ≤ ∑ i, |v i-w i| := by
         rw [←Finset.sum_sub_distrib]
         exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_abs_sub_abs_le _ _)

lemma normalizeCoefficients_dist_le (v w : ι → ℝ) (i : ι) :
    |normalizeCoefficients v i-normalizeCoefficients w i| ≤ 2*∑ j, |v j-w j| := by
  exact (abs_div_sub_div_le (coefficientScale_one_le v) (coefficientScale_one_le w)
    (abs_le_coefficientScale w i)).trans (by
      have hi := Finset.single_le_sum (fun j _ => abs_nonneg (v j-w j)) (Finset.mem_univ i)
      linarith [abs_coefficientScale_sub_le v w])

variable {X : Type*} [MetricSpace X]

lemma normalizeCoefficients_boundedLip [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    {f : ι → X → ℝ} (hf : ∀ i, BoundedLip (f i))
    (i : ι) : BoundedLip (fun x => normalizeCoefficients (fun j => f j x) i) := by
  choose K hK using fun j => (hf j).1
  refine ⟨⟨2*∑ j, K j,?_⟩,1,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc |normalizeCoefficients (fun j => f j x) i-normalizeCoefficients (fun j => f j y) i| ≤
          2*∑ j, |f j x-f j y| := normalizeCoefficients_dist_le _ _ i
         _ ≤ 2*∑ j, (K j:ℝ)*dist x y := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
            by simpa only [Real.dist_eq] using (hK j).dist_le_mul x y) (by norm_num)
         _ = _ := by push_cast; rw [←Finset.sum_mul]; ring
  · intro x
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (normalizeCoefficients (fun l => f l x) j))
      (Finset.mem_univ i)).trans (normalizeCoefficients_budget _)

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma exists_lip_l1_approx {b : X → ℝ} (hb : Integrable b μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → ℝ, BoundedLip f ∧ (∫ x, |f x-b x| ∂μ) < ε := by
  obtain ⟨f,hf⟩ := (lipToL1_dense μ).exists_dist_lt (hb.toL1 b) hε
  refine ⟨f.val,f.property,?_⟩
  rw [dist_comm,dist_eq_norm,L1.norm_eq_integral_norm] at hf
  have he : (fun x => ‖(lipToL1 μ f-hb.toL1 b : Lp ℝ 1 μ) x‖) =ᵐ[μ]
      (fun x => |f.val x-b x|) := by
    filter_upwards [Lp.coeFn_sub (lipToL1 μ f) (hb.toL1 b),hb.coeFn_toL1,
      ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ f.val] with x h1 h2 h3
    rw [h1,Pi.sub_apply,h2]
    change ‖(ContinuousMap.toLp 1 μ ℝ f.val : Lp ℝ 1 μ) x-b x‖ = _
    rw [h3,Real.norm_eq_abs]
  simpa only [integral_congr_ae he] using hf

theorem exists_admissible_coefficient_approx (b : ι → X → ℝ)
    (hb : ∀ i, Measurable (b i)) (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ι → X → ℝ, (∀ i, BoundedLip (f i)) ∧
      (∀ x, ∑ i, |f i x| ≤ 1) ∧ (∑ i, ∫ x, |f i x-b i x| ∂μ) < ε := by
  let N : ℝ := Fintype.card ι
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let δ := ε/(2*(N+1)^2)
  have hδ : 0 < δ := div_pos hε (by dsimp only [N]; positivity)
  have hbi i : Integrable (b i) μ := Integrable.mono' (integrable_const (1:ℝ)) (hb i).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (Finset.single_le_sum (fun j _ => abs_nonneg (b j x)) (Finset.mem_univ i)).trans (hbudget x))
  choose a ha happrox using fun i => exists_lip_l1_approx μ (hbi i) hδ
  let f i x := normalizeCoefficients (fun j => a j x) i
  have hfi i : BoundedLip (f i) := normalizeCoefficients_boundedLip ha i
  have hdi i : Integrable (fun x => |a i x-b i x|) μ :=
    ((integrable_boundedLip μ (ha i)).sub (hbi i)).abs
  have hfd i : Integrable (fun x => |f i x-b i x|) μ :=
    ((integrable_boundedLip μ (hfi i)).sub (hbi i)).abs
  refine ⟨f,hfi,fun x => normalizeCoefficients_budget _,?_⟩
  have hbound i : (∫ x, |f i x-b i x| ∂μ) ≤ 2*∑ j, ∫ x, |a j x-b j x| ∂μ := by
    rw [←integral_finsetSum _ (fun j _ => hdi j),←integral_const_mul]
    apply integral_mono (hfd i) ((integrable_finsetSum _ fun j _ => hdi j).const_mul _)
    intro x
    have hh := normalizeCoefficients_dist_le (fun j => a j x) (fun j => b j x) i
    rw [normalizeCoefficients_fixed _ (hbudget x)] at hh
    exact hh
  have hs : (∑ i, ∫ x, |a i x-b i x| ∂μ) ≤ N*δ := by
    calc _ ≤ ∑ i : ι, δ := Finset.sum_le_sum fun i _ => (happrox i).le
         _ = _ := by simp [N]
  calc _ ≤ ∑ i : ι, (2*∑ j, ∫ x, |a j x-b j x| ∂μ) := Finset.sum_le_sum fun i _ => hbound i
       _ = 2*N*(∑ j, ∫ x, |a j x-b j x| ∂μ) := by simp [N]; ring
       _ ≤ 2*N*(N*δ) := mul_le_mul_of_nonneg_left hs (by positivity)
       _ < ε := by
         dsimp only [δ]
         have hden : 0 < 2*(N+1)^2 := by positivity
         rw [show 2*N*(N*(ε/(2*(N+1)^2))) = ε*(N^2/(N+1)^2) by field_simp]
         apply (mul_lt_iff_lt_one_right hε).mpr
         apply (div_lt_one (by positivity : 0 < (N+1)^2)).mpr
         nlinarith

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Duality
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*}

lemma exists_measurable_max_selector [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (ρ : ℕ → X → ℝ) (hρ : ∀ j, Measurable (ρ j)) (N : ℕ) :
    ∃ σ : X → ℕ, Measurable σ ∧ (∀ x, σ x ≤ N) ∧
      ∀ x j, j ≤ N → |ρ j x| ≤ |ρ (σ x) x| := by
  classical
  let p x i := i ≤ N ∧ ∀ j, j ≤ N → |ρ j x| ≤ |ρ i x|
  have hp : ∀ x, ∃ i, p x i := by
    intro x
    obtain ⟨i,hi,hh⟩ := Finset.exists_max_image (Finset.range (N+1))
      (fun i => |ρ i x|) (by simp)
    refine ⟨i,Nat.le_of_lt_succ (Finset.mem_range.mp hi),fun j hj => hh j ?_⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  refine ⟨fun x => Nat.find (hp x),measurable_find hp ?_,fun x => (Nat.find_spec (hp x)).1,
    fun x => (Nat.find_spec (hp x)).2⟩
  intro i
  have hm : MeasurableSet {x : X | ∀ j, j ≤ N → |ρ j x| ≤ |ρ i x|} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (hρ j).abs (hρ i).abs
  exact (MeasurableSet.const (i ≤ N)).inter hm

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma exists_measurable_max_coefficients (ρ : ℕ → X → ℝ) (hρ : ∀ j, Measurable (ρ j)) (N : ℕ) :
    ∃ b : Fin (N+1) → X → ℝ, (∀ i, Measurable (b i)) ∧
      (∀ x, ∑ i, |b i x| ≤ 1) ∧
      ∀ x, (∑ i, b i x * ρ i x) = ⨆ i : Fin (N+1), |ρ i x| := by
  classical
  obtain ⟨σ,hσm,hσN,hσ⟩ := exists_measurable_max_selector ρ hρ N
  let b (i : Fin (N+1)) (x : X) : ℝ := if σ x = i then (if 0 ≤ ρ i x then 1 else -1) else 0
  have hb i : Measurable (b i) :=
    Measurable.ite (measurableSet_eq_fun hσm measurable_const)
      (Measurable.ite (measurableSet_le measurable_const (hρ i)) measurable_const measurable_const)
      measurable_const
  have hid (x : X) : (⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ : Fin (N+1)).val = σ x := rfl
  have hsum x (F : Fin (N+1) → ℝ) :
      (∑ i : Fin (N+1), if σ x = i then F i else 0) = F ⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ := by
    rw [Finset.sum_eq_single (⟨σ x,Nat.lt_succ_of_le (hσN x)⟩ : Fin (N+1))]
    · simp
    · intro i hi hneq
      have hh : ¬σ x = i := by intro he; apply hneq; apply Fin.ext; exact he.symm
      simp [hh]
    · simp
  refine ⟨b,hb,?_,?_⟩
  · intro x
    have he : (∑ i, |b i x|) = ∑ i : Fin (N+1), if σ x = i then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [b]
      split_ifs <;> norm_num
    rw [he,hsum]
  · intro x
    have he : (∑ i, b i x*ρ i x) = ∑ i : Fin (N+1), if σ x = i then |ρ i x| else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [b]
      split_ifs <;> simp_all [abs_of_nonneg,abs_of_neg]
    rw [he,hsum]
    apply le_antisymm
    · exact le_ciSup (Finite.bddAbove_range (fun i : Fin (N+1) => |ρ i x|)) _
    · exact ciSup_le fun i => hσ x i (Nat.le_of_lt_succ i.isLt)

theorem mass_le_of_finite_tests {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (π : ℕ → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i))
    (ρ : ℕ → X → ℝ) (hρm : ∀ j, Measurable (ρ j)) (hρ1 : ∀ j x, |ρ j x| ≤ 1)
    (hρ : ∀ j b, BoundedLip b → T b (π j) =
      ∫ x, b x*ρ j x ∂MassMeasure.currentMassMeasure hT)
    (hmass : mass T = ∫ x, ⨆ j, |ρ j x| ∂MassMeasure.currentMassMeasure hT)
    {C : ℝ} (hC : ∀ N (b : Fin (N+1) → X → ℝ), (∀ i, BoundedLip (b i)) →
      (∀ x, ∑ i, |b i x| ≤ 1) → (∑ i, T (b i) (π i)) ≤ C) : mass T ≤ C := by
  classical
  let μ := MassMeasure.currentMassMeasure hT
  let R (N : ℕ) (x : X) : ℝ := ⨆ i : Fin (N+1), |ρ i x|
  have hR0 N x : 0 ≤ R N x := (abs_nonneg (ρ 0 x)).trans (le_ciSup (Finite.bddAbove_range (fun i : Fin (N+1) => |ρ i x|)) (0:Fin (N+1)))
  have hR1 N x : R N x ≤ 1 := ciSup_le fun i => hρ1 i x
  have hRN N : (∫ x, R N x ∂μ) ≤ C := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hbm,hb1,hbmax⟩ := exists_measurable_max_coefficients ρ hρm N
    obtain ⟨f,hf,hf1,happrox⟩ := exists_admissible_coefficient_approx μ b hbm hb1 hε
    have hfAdm (index : Fin (N+1)) : Admissible (f index) (π index) :=
      ⟨hf index,fun coordinate => ⟨1,hπ index coordinate⟩⟩
    have hbi i : Integrable (b i) μ := Integrable.mono' (integrable_const (1:ℝ)) (hbm i).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (Finset.single_le_sum (fun j _ => abs_nonneg (b j x)) (Finset.mem_univ i)).trans (hb1 x))
    have hri (g : X → ℝ) (hg : Integrable g μ) (i : ℕ) : Integrable (fun x => g x*ρ i x) μ :=
      hg.mul_bdd (hρm i).aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hρ1 i x)
    have hdiff i : (∫ x, b i x*ρ i x ∂μ) ≤ T (f i) (π i)+(∫ x, |f i x-b i x| ∂μ) := by
      rw [hρ i (f i) (hfAdm i).1]
      have he : (∫ x, b i x*ρ i x ∂μ)-(∫ x, f i x*ρ i x ∂μ) =
          ∫ x, (b i x-f i x)*ρ i x ∂μ := by
        rw [←integral_sub (hri _ (hbi i) _) (hri _ (integrable_boundedLip μ (hf i)) _)]
        congr 1; funext x; ring
      apply sub_le_iff_le_add'.mp
      rw [he]
      apply ((le_abs_self _).trans (abs_integral_le_integral_abs)).trans
      apply integral_mono ((hri _ ((hbi i).sub (integrable_boundedLip μ (hf i))) _).abs)
        (((integrable_boundedLip μ (hf i)).sub (hbi i)).abs)
      intro x
      change |(b i x-f i x)*ρ i x| ≤ |f i x-b i x|
      rw [abs_mul,abs_sub_comm (b i x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hρ1 i x)
    calc (∫ x, R N x ∂μ) = ∑ i, ∫ x, b i x*ρ i x ∂μ := by
          rw [←integral_finsetSum _ (fun i _ => hri _ (hbi i) _)]
          apply integral_congr_ae (Eventually.of_forall fun x => (hbmax x).symm)
         _ ≤ ∑ i, (T (f i) (π i)+(∫ x, |f i x-b i x| ∂μ)) := Finset.sum_le_sum fun i _ => hdiff i
         _ ≤ C+ε := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (hC N f hf hf1) happrox.le
  have hlim : Tendsto (fun N => ∫ x, R N x ∂μ) atTop (𝓝 (mass T)) := by
    rw [hmass]
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro N
      exact (Measurable.iSup fun i : Fin (N+1) => (hρm i).abs).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hR0 N x)]; exact hR1 N x
    · apply Eventually.of_forall
      intro x
      have hmono : Monotone (fun N => R N x) := by
        intro N M hNM
        apply ciSup_le
        intro i
        exact le_ciSup (Finite.bddAbove_range (fun i : Fin (M+1) => |ρ i x|)) (⟨i,Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hNM)⟩:Fin (M+1))
      have hbd : BddAbove (range (fun N => R N x)) := ⟨1,by rintro _ ⟨N,rfl⟩; exact hR1 N x⟩
      have he : (⨆ N, R N x) = ⨆ j, |ρ j x| := by
        have hb : BddAbove (range (fun j => |ρ j x|)) := ⟨1,by rintro _ ⟨j,rfl⟩; exact hρ1 j x⟩
        apply le_antisymm
        · apply ciSup_le
          intro N
          exact ciSup_le fun i => le_ciSup hb i
        · apply ciSup_le
          intro j
          exact (le_ciSup (Finite.bddAbove_range (fun i : Fin (j+1) => |ρ i x|)) (⟨j,Nat.lt_succ_self j⟩:Fin (j+1))).trans (le_ciSup hbd j)
      simpa only [he] using tendsto_atTop_ciSup hmono hbd
  exact le_of_tendsto hlim (Eventually.of_forall hRN)

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Convolution
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma coefficientList_eval_continuous {k N : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    Continuous (fun b : CoefficientList (X := X) N => ∑ i, T (b.val i) (π i)) := by
  apply continuous_finsetSum
  intro i hi
  apply LipschitzWith.continuous (K := ⟨mass T,mass_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro b c
  have hh := Foundations.IsMetricCurrent.first_difference_bound hT (b.property.1 i) (c.property.1 i)
    (π i) 1 (hπ i) (nndist b c) (fun x =>
      (ContinuousMap.dist_apply_le_dist x).trans (dist_le_pi_dist b.val c.val i))
  change |T (b.val i) (π i)-T (c.val i) (π i)| ≤ mass T*dist b c
  simpa only [Real.dist_eq,NNReal.coe_one,one_pow,one_mul,coe_nndist,mul_comm] using hh

lemma finite_list_le_mass {k N : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (b : Fin N → X → ℝ) (hb : ∀ i, BoundedLip (b i))
    (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    (∑ i, T (b i) (π i)) ≤ mass T := by
  let μ := MassMeasure.currentMassMeasure hT
  have hi i : Integrable (fun x => |b i x|) μ := (integrable_boundedLip μ (hb i)).abs
  calc (∑ i, T (b i) (π i)) ≤ ∑ i, |T (b i) (π i)| :=
        Finset.sum_le_sum fun i _ => le_abs_self _
       _ ≤ ∑ i, ∫ x, |b i x| ∂μ := Finset.sum_le_sum fun i _ =>
        MassMeasure.currentMassMeasure_controls hT _ _ (hb i) (hπ i)
       _ = ∫ x, ∑ i, |b i x| ∂μ := (integral_finsetSum _ (fun i _ => hi i)).symm
       _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono (integrable_finsetSum _ fun i _ => hi i)
          (integrable_const _) hbudget
       _ = mass T := by simpa using MassMeasure.currentMassMeasure_total hT

theorem exists_countable_mass_lists (k : ℕ) :
    ∃ (π : ℕ → Fin k → X → ℝ) (b : (N : ℕ) → ℕ → Fin (N+1) → X → ℝ),
      (∀ j i, LipschitzWith 1 (π j i)) ∧
      (∀ N j i, BoundedLip (b N j i)) ∧
      (∀ N j x, ∑ i, |b N j i x| ≤ 1) ∧
      ∀ {T : Functional X k}, IsMetricCurrent T → ∀ C : ℝ,
        mass T ≤ C ↔ ∀ N j, (∑ i : Fin (N+1), T (b N j i) (π i)) ≤ C := by
  classical
  obtain ⟨π,hπ,hspec⟩ := exists_mass_spectrum (X := X) k
  choose bs hbs using fun N : ℕ => TopologicalSpace.exists_dense_seq (CoefficientList (X := X) (N+1))
  refine ⟨π,fun N j i => (bs N j).val i,hπ,fun N j => (bs N j).property.1,
    fun N j => (bs N j).property.2,?_⟩
  intro T hT C
  constructor
  · intro h N j
    exact (finite_list_le_mass hT _ (bs N j).property.1 (bs N j).property.2
      (fun i => π i) (fun i => hπ i)).trans h
  · intro h
    obtain ⟨ρ,hρm,hρ1,hρ,hmass⟩ := hspec hT
    apply mass_le_of_finite_tests hT π hπ ρ hρm hρ1 hρ hmass
    intro N a ha hbudget
    let q : CoefficientList (X := X) (N+1) := ⟨fun i => ⟨a i,(ha i).continuous⟩,ha,hbudget⟩
    change (∑ i, T (q.val i) (π i)) ≤ C
    apply (hbs N).induction_on (p := fun r : CoefficientList (X := X) (N+1) =>
      (∑ i, T (r.val i) (π i)) ≤ C) q
    · exact isClosed_le (coefficientList_eval_continuous hT _ (fun i => hπ i)) continuous_const
    · exact h N

theorem ae_mass_le_of_listwise {A : Type*} [MeasurableSpace A] (ν : Measure A)
    {k : ℕ} {T : A → Functional X k} {C : A → ℝ}
    (hT : ∀ᵐ a ∂ν, IsMetricCurrent (T a))
    (h : ∀ N (b : Fin (N+1) → X → ℝ) (π : Fin (N+1) → Fin k → X → ℝ),
      (∀ i, BoundedLip (b i)) → (∀ x, ∑ i, |b i x| ≤ 1) →
      (∀ j i, LipschitzWith 1 (π j i)) →
      ∀ᵐ a ∂ν, (∑ i, T a (b i) (π i)) ≤ C a) :
    ∀ᵐ a ∂ν, mass (T a) ≤ C a := by
  obtain ⟨π,b,hπ,hb,hbudget,hmass⟩ := exists_countable_mass_lists (X := X) k
  have hh : ∀ᵐ a ∂ν, ∀ N j, (∑ i : Fin (N+1), T a (b N j i) (π i)) ≤ C a :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun j =>
      h N (b N j) (fun i => π i) (hb N j) (hbudget N j) (fun i => hπ i)
  filter_upwards [hT,hh] with a hta ha
  exact (hmass hta (C a)).mpr ha

end BorelCoefficients
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SmoothCutoff

lemma dprofile_integrable_measure (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ≥0) (t : ℝ) :
    Integrable (dprofile a t) μ := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  exact Integrable.of_bound (hC a t).2.1.continuous.aestronglyMeasurable ((C*a:ℝ≥0):ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hC a t).2.2 x)

theorem ae_tendsto_dprofile_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => ∫ x : ℝ,
      dprofile ((n:ℝ≥0)+1) t x ∂μ) atTop (𝓝 ((μ.rnDeriv volume t).toReal)) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  let σ := μ.singularPart volume
  let f : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal
  have hf : Integrable f := μ.integrable_toReal_rnDeriv
  let a : ℕ → ℝ≥0 := fun n => (n:ℝ≥0)+1
  let r : ℕ → ℝ := fun n => ((a n:ℝ))⁻¹
  have hap n : 0 < a n := by dsimp [a]; positivity
  have harp n : 0 < (a n:ℝ) := hap n
  have hrp n : 0 < r n := inv_pos.mpr (harp n)
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => hrp n⟩
    exact tendsto_inv_atTop_zero.comp
      (show Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop from by
        simpa only [a,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
          tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [ae_tendsto_dprofile_integral hf,Besicovitch.ae_tendsto_rnDeriv σ volume,
    μ.rnDeriv_singularPart volume] with t ht hσ hz
  have hz' : σ.rnDeriv volume t = 0 := hz
  have hs : Tendsto (fun n => ∫ x : ℝ, dprofile (a n) t x ∂σ) atTop (𝓝 0) := by
    have hratio := (ENNReal.continuousAt_toReal (by simpa only [hz'] using ENNReal.zero_ne_top)).tendsto.comp
      (hσ.comp hrt)
    have hbound n : ‖∫ x : ℝ, dprofile (a n) t x ∂σ‖ ≤
        (2*(C:ℝ)) * (σ (closedBall t (r n))/volume (closedBall t (r n))).toReal := by
      have hnz (x : ℝ) (hx : x ∉ closedBall t (r n)) : dprofile (a n) t x = 0 := by
        apply dprofile_zero (hap n)
        intro hi
        apply hx
        rw [Real.closedBall_eq_Icc]
        change t-r n ≤ x ∧ x ≤ t+r n
        exact ⟨by linarith [hi.1,hrp n],hi.2⟩
      calc
        _ ≤ ∫ x : ℝ, ‖dprofile (a n) t x‖ ∂σ := norm_integral_le_integral_norm _
        _ = ∫ x in closedBall t (r n), ‖dprofile (a n) t x‖ ∂σ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hnz x hx,norm_zero])).symm
        _ ≤ ∫ _x in closedBall t (r n), (C:ℝ)*(a n:ℝ) ∂σ := by
          apply integral_mono (dprofile_integrable_measure σ _ _).norm.integrableOn (integrable_const _)
          intro x
          simpa only [Real.norm_eq_abs,NNReal.coe_mul] using (hC (a n) t).2.2 x
        _ = _ := by
          rw [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,ENNReal.toReal_div]
          change σ.real (closedBall t (r n)) * ((C:ℝ)*(a n:ℝ)) =
            (2*(C:ℝ))*(σ.real (closedBall t (r n))/volume.real (closedBall t (r n)))
          rw [Real.volume_real_closedBall (hrp n).le]
          dsimp only [r]
          field_simp
    apply squeeze_zero_norm hbound
    simpa only [hz',ENNReal.toReal_zero,mul_zero,Function.comp_apply] using hratio.const_mul (2*(C:ℝ))
  have heq n : (∫ x : ℝ, dprofile (a n) t x ∂μ) =
      (∫ x : ℝ, dprofile (a n) t x ∂σ) +
        ∫ x : ℝ, dprofile (a n) t x*f x := by
    calc
      _ = (∫ x : ℝ, dprofile (a n) t x ∂σ) +
          ∫ x : ℝ, dprofile (a n) t x ∂volume.withDensity (μ.rnDeriv volume) := by
        rw [←integral_add_measure (dprofile_integrable_measure σ _ _)
          (dprofile_integrable_measure (volume.withDensity (μ.rnDeriv volume)) _ _)]
        rw [show σ + volume.withDensity (μ.rnDeriv volume) = μ from μ.singularPart_add_rnDeriv volume]
      _ = _ := by
        congr 1
        rw [integral_withDensity_eq_integral_toReal_smul (μ.measurable_rnDeriv volume)
          (μ.rnDeriv_lt_top volume)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
  change Tendsto (fun n => ∫ x : ℝ, dprofile (a n) t x ∂μ) atTop (𝓝 (f t))
  simp_rw [heq]
  simpa only [zero_add] using hs.add ht

end CAT0Fillings.SmoothCutoff
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_Gradient
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem ae_coarea_mass_le_gradient {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {S : ℝ → Functional X k}
    (hS : ∀ᵐ t : ℝ, IsMetricCurrent (S t))
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) :
    ∀ᵐ t : ℝ, mass (S t) ≤ (((q.gradientMeasure u).map u).rnDeriv volume t).toReal := by
  let := q.gradientMeasure_finite hu
  have hub : BoundedLip u := ⟨⟨K,hu⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  apply BorelCoefficients.ae_mass_le_of_listwise volume hS
  intro N b π hb hbudget hπ
  have hab i : Admissible (b i) (π i) := ⟨hb i,fun j => ⟨1,hπ i j⟩⟩
  have hi : Integrable (fun t => ∑ i, S t (b i) (π i)) :=
    integrable_finsetSum _ (fun i _ => (hact _ _ (hab i)).1)
  filter_upwards [SmoothCutoff.ae_tendsto_dprofile_integral hi,
    SmoothCutoff.ae_tendsto_dprofile_measure ((q.gradientMeasure u).map u)] with t ht hγ
  have hle (n : ℕ) : (∫ s : ℝ, SmoothCutoff.dprofile ((n:ℝ≥0)+1) t s *
      (∑ i, S s (b i) (π i))) ≤
      ∫ s, SmoothCutoff.dprofile ((n:ℝ≥0)+1) t s ∂(q.gradientMeasure u).map u := by
    let φ := SmoothCutoff.dprofile ((n:ℝ≥0)+1) t
    have hφ : BoundedLip (φ ∘ u) := Slicing.dprofile_comp_boundedLip hub _ t
    have hφ0 x : 0 ≤ φ x := mul_nonneg (NNReal.coe_nonneg _)
      Real.smoothTransition.monotone.deriv_nonneg
    have heq i : T (fun x => φ (u x)*b i x) (Fin.cons u (π i)) =
        ∫ s : ℝ, φ s * S s (b i) (π i) := by
      change T (fun x => (φ ∘ u) x*b i x) (Matrix.vecCons u (π i)) = _
      rw [(hact _ _ ⟨hφ.mul (hb i),(hab i).2⟩).2]
      exact integral_congr_ae (hweight _ _ (hab i) φ hφ)
    calc
      _ = ∑ i, ∫ s : ℝ, φ s * S s (b i) (π i) := by
        simp_rw [Finset.mul_sum]
        exact integral_finsetSum _ (fun i _ => SmoothCutoff.dprofile_mul_integrable (hact _ _ (hab i)).1 _ _)
      _ = ∑ i, T (fun x => φ (u x)*b i x) (Fin.cons u (π i)) := by simp_rw [heq]
      _ ≤ |∑ i, T (fun x => φ (u x)*b i x) (Fin.cons u (π i))| := le_abs_self _
      _ ≤ ∫ x, |φ (u x)| ∂q.gradientMeasure u :=
        q.list_action_le_gradient hu hφ b hb hbudget π hπ
      _ = ∫ x, φ (u x) ∂q.gradientMeasure u := by
        simp only [abs_of_nonneg (hφ0 _)]
      _ = _ := (integral_map hu.continuous.measurable.aemeasurable
        (SmoothCutoff.dprofile_integrable_measure ((q.gradientMeasure u).map u) _ _).aestronglyMeasurable).symm
  exact le_of_tendsto_of_tendsto ht hγ (Eventually.of_forall hle)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings

lemma densityPush_add_of_nonneg {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {ρ σ : α → ℝ}
    (hρm : AEMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (hσ : 0 ≤ᵐ[μ] σ) :
    densityPush μ φ (fun z => ρ z+σ z) = densityPush μ φ ρ + densityPush μ φ σ := by
  have hwd : μ.withDensity (fun z => ENNReal.ofReal (ρ z+σ z)) =
      μ.withDensity (fun z => ENNReal.ofReal (ρ z)) +
        μ.withDensity (fun z => ENNReal.ofReal (σ z)) := by
    apply Measure.ext
    intro s hs
    simp only [withDensity_apply _ hs,Measure.add_apply]
    calc
      _ = ∫⁻ z in s, ENNReal.ofReal (ρ z)+ENNReal.ofReal (σ z) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hρ,ae_restrict_of_ae hσ] with z hz hzs
        exact ENNReal.ofReal_add hz hzs
      _ = _ := lintegral_add_left' (hρm.ennreal_ofReal.restrict) _
  simp only [densityPush,hwd,Measure.map_add _ _ hφ]

lemma weighted_young_real (c ρ d e : ℝ) (hρ : 0 ≤ ρ) (he : d^2 = e) :
    (2*c)*(ρ*d) ≤ c^2*ρ+ρ*e := by
  rw [←he]
  nlinarith [mul_nonneg hρ (sq_nonneg (c-d))]

lemma densityPush_quadratic_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) (ρ d e : α → ℝ)
    (hρm : AEMeasurable ρ μ) (hρ : ∀ z, 0 ≤ ρ z)
    (hd : ∀ᵐ z ∂μ, d z^2 = e z) (c : ℝ≥0) :
    (2*c) • densityPush μ φ (fun z => ρ z*d z) ≤
      c^2 • densityPush μ φ ρ + densityPush μ φ (fun z => ρ z*e z) := by
  have hpoint : (fun z => (2*(c:ℝ))*(ρ z*d z)) ≤ᵐ[μ]
      (fun z => (c:ℝ)^2*ρ z + ρ z*e z) :=
    hd.mono fun z hz => weighted_young_real _ _ _ _ (hρ z) hz
  have hi := densityPush_mono_ae hφ hpoint
  have hadd : densityPush μ φ (fun z => (c:ℝ)^2*ρ z + ρ z*e z) =
      densityPush μ φ (fun z => (c:ℝ)^2*ρ z) + densityPush μ φ (fun z => ρ z*e z) :=
    densityPush_add_of_nonneg hφ (hρm.const_mul _)
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hρ z))
      (hd.mono fun z hz => mul_nonneg (hρ z) (hz ▸ sq_nonneg (d z)))
  rw [hadd] at hi
  have hl : densityPush μ φ (fun z => (2*(c:ℝ))*(ρ z*d z)) =
      (2*c) • densityPush μ φ (fun z => ρ z*d z) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      densityPush_const_mul μ φ (fun z => ρ z*d z) (2*c) hφ
  have hr : densityPush μ φ (fun z => (c:ℝ)^2*ρ z) =
      c^2 • densityPush μ φ ρ := by
    simpa only [NNReal.coe_pow] using densityPush_const_mul μ φ ρ (c^(2:ℕ)) hφ
  rwa [hl,hr] at hi

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_gradient_quadratic_le (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (c : ℝ≥0) :
    (2*c) • densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (fun z => q.density i z*q.duNorm i u z) ≤
    c^2 • densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (q.density i) +
    densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended
      (fun z => q.density i z*q.normSq i u z) :=
  densityPush_quadratic_le (q.chart i).measurable_paramExtended _ _ _
    (q.density_integrable i).aestronglyMeasurable.aemeasurable (q.density_nonneg i)
    ((q.ae_duNorm_bounds i hu).mono fun _ hz => hz.2.2) c

lemma gradient_quadratic_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (c : ℝ≥0) : (2*c) • q.gradientMeasure u ≤
      c^2 • MassMeasure.currentMassMeasure hT + q.energyMeasure u := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,q.measure_eq]
  simp only [gradientMeasure,energyMeasure,weightedMeasure,Measure.sum_apply _ hs]
  change (2*(c:ℝ≥0∞)) * _ ≤ (c:ℝ≥0∞)^2 * _ + _
  rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  exact q.chart_gradient_quadratic_le i hu c s

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Mass_IntrinsicCoarea
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SmoothCutoff

lemma dprofile_nonneg (a : ℝ≥0) (t x : ℝ) : 0 ≤ dprofile a t x :=
  mul_nonneg a.coe_nonneg Real.smoothTransition.monotone.deriv_nonneg

lemma ae_density_smul_le (γ μ : Measure ℝ) [IsFiniteMeasure γ] [IsFiniteMeasure μ]
    (c : ℝ≥0) (hle : γ ≤ c • μ) :
    ∀ᵐ t : ℝ, (γ.rnDeriv volume t).toReal ≤ (c:ℝ)*(μ.rnDeriv volume t).toReal := by
  filter_upwards [ae_tendsto_dprofile_measure γ,ae_tendsto_dprofile_measure μ] with t hγ hμ
  apply le_of_tendsto_of_tendsto hγ (hμ.const_mul (c:ℝ))
  apply Eventually.of_forall
  intro n
  have h := integral_mono_measure hle
    (Eventually.of_forall fun x => dprofile_nonneg ((n:ℝ≥0)+1) t x)
    (dprofile_integrable_measure (c • μ) _ _)
  simpa only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul] using h

lemma quadratic_implies_cauchy {g a e : ℝ} (hg : 0 ≤ g) (ha : 0 ≤ a) (he : 0 ≤ e)
    (h : ∀ c : ℝ≥0, 2*(c:ℝ)*g ≤ (c:ℝ)^2*a+e) : g^2 ≤ a*e := by
  by_cases hz : a = 0
  · simp only [hz,mul_zero,zero_mul,zero_add] at h ⊢
    by_contra hpos
    have hgp : 0 < g := lt_of_le_of_ne hg (by intro hh; simp [←hh] at hpos)
    have hh := h ⟨(e+1)/(2*g),by positivity⟩
    change 2*((e+1)/(2*g))*g ≤ e at hh
    have heq : 2*((e+1)/(2*g))*g = e+1 := by field_simp
    linarith
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hh := h ⟨g/a,div_nonneg hg ha⟩
    change 2*(g/a)*g ≤ (g/a)^2*a+e at hh
    have hi := mul_le_mul_of_nonneg_right hh hap.le
    field_simp [hz] at hi
    nlinarith

lemma ae_density_cauchy (γ μ ζ : Measure ℝ) [IsFiniteMeasure γ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ζ]
    (hle : ∀ c : ℝ≥0, (2*c) • γ ≤ c^2 • μ + ζ) :
    ∀ᵐ t : ℝ, (γ.rnDeriv volume t).toReal^2 ≤
      (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal := by
  filter_upwards [ae_tendsto_dprofile_measure γ,ae_tendsto_dprofile_measure μ,
    ae_tendsto_dprofile_measure ζ] with t hγ hμ hζ
  apply quadratic_implies_cauchy ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  intro c
  apply le_of_tendsto_of_tendsto (hγ.const_mul (2*(c:ℝ)))
    ((hμ.const_mul ((c:ℝ)^2)).add hζ)
  apply Eventually.of_forall
  intro n
  have hb := integral_mono_measure (hle c)
    (Eventually.of_forall fun x => dprofile_nonneg ((n:ℝ≥0)+1) t x)
    (dprofile_integrable_measure (c^2 • μ + ζ) _ _)
  rw [integral_add_measure (dprofile_integrable_measure (c^2 • μ) _ _)
    (dprofile_integrable_measure ζ _ _)] at hb
  simpa only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,NNReal.coe_mul,
    NNReal.coe_ofNat,NNReal.coe_pow] using hb

end CAT0Fillings.SmoothCutoff
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_distribution_gradient_bounds {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ,
      (((q.gradientMeasure u).map u).rnDeriv volume t).toReal^2 ≤
        (((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal *
        (((q.energyMeasure u).map u).rnDeriv volume t).toReal ∧
      (((q.gradientMeasure u).map u).rnDeriv volume t).toReal ≤
        (K:ℝ)*(((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal := by
  let := q.gradientMeasure_finite hu
  let := q.energyMeasure_finite hu
  have hlin : (q.gradientMeasure u).map u ≤ K • (MassMeasure.currentMassMeasure hT).map u := by
    have h := Measure.map_mono (q.gradientMeasure_le hu) hu.continuous.measurable
    simpa only [Measure.map_smul] using h
  have hquad (c : ℝ≥0) : (2*c) • (q.gradientMeasure u).map u ≤
      c^2 • (MassMeasure.currentMassMeasure hT).map u + (q.energyMeasure u).map u := by
    have h := Measure.map_mono (q.gradient_quadratic_le hu c) hu.continuous.measurable
    simpa only [Measure.map_smul,
      Measure.map_add _ _ hu.continuous.measurable] using h
  exact (SmoothCutoff.ae_density_cauchy _ _ _ hquad).and
    (SmoothCutoff.ae_density_smul_le _ _ K hlin)

theorem ae_intrinsic_coarea (hI : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ,
      IsIntegral (k+1) (BorelRestriction.restrictCurrent hT {x | t < u x}) ∧
      (mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})))^2 ≤
        (((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal *
        (((q.energyMeasure u).map u).rnDeriv volume t).toReal ∧
      mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})) ≤
        (K:ℝ)*(((MassMeasure.currentMassMeasure hT).map u).rnDeriv volume t).toReal := by
  have hub : BoundedLip u := ⟨⟨K,hu⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT hI.2.1 hX hu
  have hSm := hS.mono (fun _ ht => ht.1)
  have hmass := q.ae_coarea_mass_le_gradient hu hSm hact hweight
  have heq := Slicing.ae_superlevelSlice_eq_coarea hT hI.2.1 hI.2.2.1 hub hSm hact hweight
  obtain ⟨H,hH,hH0,hHI,hR⟩ := Slicing.ae_integral_restrict hI hX hu
  filter_upwards [hmass,heq,hR,q.ae_distribution_gradient_bounds hu] with t hm he hr hd
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have he' : BorelRestriction.restrictCurrent hI.2.2.1 {x | t < u x} -
      boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x}) = S t := he
  rw [Slicing.restrictCurrent_zero_of_eq_zero hI.2.2.1 hz hE,zero_sub] at he'
  have hp : mass (boundarySucc (BorelRestriction.restrictCurrent hT {x | t < u x})) =
      mass (S t) := by rw [←he',mass_neg]
  refine ⟨hr.1,?_,?_⟩
  · rw [hp]
    nlinarith [mass_nonneg (S t), ENNReal.toReal_nonneg
      (a := ((q.gradientMeasure u).map u).rnDeriv volume t)]
  · rw [hp]
    exact hm.trans hd.2

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_BrezisLieb
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer

lemma rpow_abs_difference {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ C ≥ (0:ℝ), ∀ a b : ℝ,
      abs (|a+b|^p-|a|^p) ≤ ε*|a|^p+C*|b|^p := by
  have ht : Tendsto (fun t : ℝ => abs (|1+t|^p-1)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => abs (|1+t|^p-1)) := by
      have hp0 := hp.le
      fun_prop
    simpa using hc.tendsto 0
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds hε))
  let D := δ⁻¹+1
  let C := D^p+(δ⁻¹)^p
  have hC : 0 ≤ C := add_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨C,hC,fun a b => ?_⟩
  by_cases ha : a = 0
  · subst a
    simp only [zero_add,abs_zero,Real.zero_rpow hp.ne',sub_zero,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg b) p),mul_zero,zero_add]
    have hD : 1 ≤ D := by dsimp [D]; have := inv_nonneg.mpr hδ.le; linarith
    have hc1 : 1 ≤ C := by
      have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hD hp.le
      simp only [Real.one_rpow] at hh
      exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
    nlinarith [Real.rpow_nonneg (abs_nonneg b) p]
  have hap : 0 < |a| := abs_pos.mpr ha
  by_cases hs : |b/a| < δ
  · have hh : abs (|1+b/a|^p-1) < ε := hd (by simpa only [mem_ball,Real.dist_eq,sub_zero] using hs)
    have he : |a+b|^p = |a|^p*|1+b/a|^p := by
      rw [←Real.mul_rpow (abs_nonneg _) (abs_nonneg _),←abs_mul]
      congr 2
      field_simp
    rw [he,←mul_sub_one,abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact (mul_le_mul_of_nonneg_left hh.le (Real.rpow_nonneg (abs_nonneg _) _)).trans
      (by nlinarith [mul_nonneg hC (Real.rpow_nonneg (abs_nonneg b) p)])
  · have hratio : δ ≤ |b|/|a| := by simpa only [abs_div] using le_of_not_gt hs
    have hab : |a| ≤ δ⁻¹*|b| := by
      have hh := (le_div_iff₀ hap).mp hratio
      rw [mul_comm,←div_eq_mul_inv]
      exact (le_div_iff₀ hδ).mpr (by simpa [mul_comm] using hh)
    have hab' : |a+b| ≤ D*|b| := by
      have := abs_add_le a b
      dsimp [D]
      nlinarith
    have habp := Real.rpow_le_rpow (abs_nonneg _) hab hp.le
    have habp' := Real.rpow_le_rpow (abs_nonneg _) hab' hp.le
    rw [Real.mul_rpow (inv_nonneg.mpr hδ.le) (abs_nonneg _)] at habp
    rw [Real.mul_rpow (by dsimp [D]; positivity) (abs_nonneg _)] at habp'
    have hh := abs_sub (|a+b|^p) (|a|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hh
    dsimp [C] at hC ⊢
    nlinarith [mul_nonneg hε.le (Real.rpow_nonneg (abs_nonneg a) p)]

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma brezis_lieb_remainder {p : ℝ} (hp : 0 < p) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ j, Integrable (fun x => |f j x|^p) μ)
    (hg : Integrable (fun x => |g x|^p) μ)
    (hz : ∀ j, Integrable (fun x => |f j x-g x|^p) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (M : ℝ) (hM : ∀ j, ∫ x, |f j x-g x|^p ∂μ ≤ M) :
    Tendsto (fun j => ∫ x, abs (|f j x|^p-|f j x-g x|^p-|g x|^p) ∂μ) atTop (𝓝 0) := by
  let R := fun j x => |f j x|^p-|f j x-g x|^p-|g x|^p
  have hR (j : ℕ) : Integrable (R j) μ := ((hf j).sub (hz j)).sub hg
  have hRlim : ∀ᵐ x ∂μ, Tendsto (fun j => R j x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hj := ((hx.abs.rpow_const (Or.inr hp.le)).sub
      ((hx.sub_const (g x)).abs.rpow_const (Or.inr hp.le))).sub_const (|g x|^p)
    simpa only [R,sub_self,abs_zero,Real.zero_rpow hp.ne',sub_zero] using hj
  have hM0 : 0 ≤ M := (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _).trans (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η := ε/(2*(M+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C,hC,hbound⟩ := rpow_abs_difference hp hη
  let H := fun j x => max (abs (R j x)-η*|f j x-g x|^p) 0
  have hH (j : ℕ) : Integrable (H j) μ := (((hR j).abs).sub ((hz j).const_mul η)).sup (integrable_zero _ _ _)
  have hHbound (j : ℕ) (x : α) : ‖H j x‖ ≤ (C+1)*|g x|^p := by
    have hb := hbound (f j x-g x) (g x)
    rw [sub_add_cancel] at hb
    have ht := abs_sub (|f j x|^p-|f j x-g x|^p) (|g x|^p)
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at ht
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · dsimp [R]
      nlinarith
    · positivity
  have hHlim : ∀ᵐ x ∂μ, Tendsto (fun j => H j x) atTop (𝓝 0) := by
    filter_upwards [hRlim,hlim] with x hx hfx
    have ht := (hx.abs.sub (((hfx.sub_const (g x)).abs.rpow_const (Or.inr hp.le)).const_mul η)).max (tendsto_const_nhds (x := (0:ℝ)))
    simpa only [H,sub_self,abs_zero,Real.zero_rpow hp.ne',mul_zero,sub_zero,max_self] using ht
  have hc := tendsto_integral_of_dominated_convergence (fun x => (C+1)*|g x|^p)
    (fun j => (hH j).aestronglyMeasurable) (hg.const_mul (C+1))
    (fun j => Eventually.of_forall (hHbound j)) hHlim
  simp only [integral_zero] at hc
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun j hj => ?_⟩
  have hupper : ∫ x, abs (R j x) ∂μ ≤ ∫ x, H j x ∂μ + η*M := by
    have hh := integral_mono ((hR j).abs) ((hH j).add ((hz j).const_mul η)) (fun x => by
      have h := le_max_left (abs (R j x)-η*|f j x-g x|^p) 0
      dsimp [H]
      linarith)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hH j) ((hz j).const_mul η),integral_const_mul] at hh
    exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hM j) hη.le) _)
  have ht := hN j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => le_max_right _ _)] at ht
  have hηM : η*M < ε/2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(M+1))).mpr
    nlinarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)]
  exact hupper.trans_lt (by linarith)

lemma brezis_lieb_splitting {p : ℝ} (hp : 0 < p) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ j, Integrable (fun x => |f j x|^p) μ)
    (hg : Integrable (fun x => |g x|^p) μ)
    (hz : ∀ j, Integrable (fun x => |f j x-g x|^p) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (M : ℝ) (hM : ∀ j, ∫ x, |f j x-g x|^p ∂μ ≤ M) :
    Tendsto (fun j => (∫ x, |f j x|^p ∂μ)-(∫ x, |f j x-g x|^p ∂μ)-(∫ x, |g x|^p ∂μ))
      atTop (𝓝 0) := by
  have hh := brezis_lieb_remainder hp f g hf hg hz hlim M hM
  apply squeeze_zero_norm (fun j => ?_) hh
  have he := integral_sub ((hf j).sub (hz j)) hg
  simp only [Pi.sub_apply] at he
  rw [integral_sub (hf j) (hz j)] at he
  rw [←he]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x =>
    |f j x|^p-|f j x-g x|^p-|g x|^p)

end CAT0Fillings.AnalyticMinimizer
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

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma lpNorm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    lpNorm f (ENNReal.ofReal p) μ ^ 2 = (∫ x, |f x|^p ∂μ)^(2/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs]
  rw [←Real.rpow_mul_natCast (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) ]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

lemma no_loss {a Λ S t : ℝ} (ha : a ≤ 1) (hΛ : 0 ≤ Λ) (hS : Λ < S)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : Λ*t^a+S*(1-t)^a ≤ Λ) : t = 1 := by
  have ht' := Real.self_le_rpow_of_le_one ht ht1 ha
  have hd' := Real.self_le_rpow_of_le_one (by linarith : 0 ≤ 1-t) (by linarith : 1-t ≤ 1) ha
  have h1 := mul_le_mul_of_nonneg_left ht' hΛ
  have h2 := mul_le_mul_of_nonneg_left hd' (hΛ.trans hS.le)
  nlinarith

lemma concentration_inequality {a Λ S t q : ℝ} (_ : 0 < a) (_ : 0 ≤ t)
    (_ : t ≤ 1) (hS : 0 < S)
    (hQ : Λ*t^a ≤ q)
    (hb : ∀ ε : ℝ, 0 < ε → ε < S → (S-ε)*(1-t)^a ≤ Λ-q) :
    Λ*t^a+S*(1-t)^a ≤ Λ := by
  have hlim : Tendsto (fun ε : ℝ => (S-ε)*(1-t)^a) (𝓝[>] 0)
      (𝓝 (S*(1-t)^a)) := by
    simpa using (((tendsto_const_nhds.sub tendsto_id).mul_const ((1-t)^a)).mono_left inf_le_left :
      Tendsto (fun ε : ℝ => (S-ε)*(1-t)^a) (𝓝[>] 0) (𝓝 ((S-0)*(1-t)^a)))
  have hh : S*(1-t)^a ≤ Λ-q := le_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hS).filter_mono inf_le_left] with ε hε hεS
    exact hb ε hε hεS)
  linarith

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma lpNorm_congr_ae {f g : α → ℝ} (h : f =ᵐ[μ] g) (p : ℝ≥0∞) :
    lpNorm f p μ = lpNorm g p μ := by
  unfold lpNorm
  rw [eLpNorm_congr_ae h]
  by_cases hf : AEStronglyMeasurable f μ
  · rw [if_pos hf, if_pos (hf.congr h)]
  · rw [if_neg hf, if_neg (fun hg => hf (hg.congr h.symm))]

lemma criticalNorm_nonneg (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :
    0 ≤ criticalNorm I p u := lpNorm_nonneg

lemma criticalMass_nonneg (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u : H) :
    0 ≤ criticalMass I p u :=
  integral_nonneg fun point => Real.rpow_nonneg (abs_nonneg ((I u) point)) p

lemma criticalNorm_smul (I : H →L[ℝ] Lp ℝ 2 μ) (p c : ℝ) (u : H) :
    criticalNorm I p (c • u) = |c| *criticalNorm I p u := by
  dsimp [criticalNorm]
  rw [map_smul,lpNorm_congr_ae (Lp.coeFn_smul c (I u)) _,lpNorm_const_smul]
  rfl

lemma criticalNorm_sq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalNorm I p u ^ 2 = criticalMass I p u ^ (2/p) :=
  lpNorm_sq_eq_integral hp (Lp.aestronglyMeasurable _)

lemma criticalMass_eq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalMass I p u = criticalNorm I p u ^ p := by
  dsimp [criticalNorm,criticalMass]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ofReal_ne_top (Lp.aestronglyMeasurable _)]
  simp only [toReal_ofReal hp.le,Real.norm_eq_abs]
  exact (Real.rpow_inv_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) hp.ne').symm

lemma criticalMass_sub (I : H →L[ℝ] Lp ℝ 2 μ) (p : ℝ) (u v : H) :
    criticalMass I p (u-v) = ∫ x, |(I u) x-(I v) x|^p ∂μ := by
  dsimp [criticalMass]
  rw [map_sub]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (I u) (I v)] with x hx
  rw [hx]
  rfl

lemma criticalMass_integrable (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H)
    (h : MemLp (I u) (ENNReal.ofReal p) μ) : Integrable (fun x => |(I u) x|^p) μ := by
  simpa only [toReal_ofReal hp.le,Real.norm_eq_abs] using h.integrable_norm_rpow (by positivity) ofReal_ne_top

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_WeakSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma criticalMass_defect (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 1 ≤ p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    {u : ℕ → H} {v : H} (hu : ∀ j, criticalNorm I p (u j) = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (I (u j)) x) atTop (𝓝 ((I v) x))) :
    Tendsto (fun j => criticalMass I p (u j-v)) atTop (𝓝 (1-criticalMass I p v)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hf (j : ℕ) := criticalMass_integrable I hp0 (u j) (hm (u j))
  have hg := criticalMass_integrable I hp0 v (hm v)
  have hz (j : ℕ) : Integrable (fun x => |(I (u j)) x-(I v) x|^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,Pi.sub_apply] using
      ((hm (u j)).sub (hm v)).integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hb (j : ℕ) : ∫ x, |(I (u j)) x-(I v) x|^p ∂μ ≤ (1+criticalNorm I p v)^p := by
    rw [←criticalMass_sub I p (u j) v,criticalMass_eq I hp0]
    apply Real.rpow_le_rpow (criticalNorm_nonneg I p _) _ hp0.le
    dsimp [criticalNorm]
    rw [map_sub,lpNorm_congr_ae (Lp.coeFn_sub (I (u j)) (I v)) _]
    have hh := lpNorm_sub_le (hm (u j)) hpe (g := I v)
    simpa only [show lpNorm (I (u j)) (ENNReal.ofReal p) μ = 1 from hu j] using hh
  have hh := brezis_lieb_splitting hp0 (fun j => (I (u j) : α → ℝ)) (I v)
    hf hg hz hlim ((1+criticalNorm I p v)^p) hb
  have he (j : ℕ) : (∫ x, |(I (u j)) x|^p ∂μ) = 1 := by
    change criticalMass I p (u j) = 1
    rw [criticalMass_eq I hp0,hu j,Real.one_rpow]
  simp only [he,←criticalMass_sub] at hh
  have hd := ((tendsto_const_nhds (x := (1:ℝ))).sub hh).sub_const (criticalMass I p v)
  convert hd using 1
  · ext j
    dsimp [criticalMass]
    ring
  · simp

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_inner_weak_subsequence [CompleteSpace E] [SeparableSpace E]
    (u : ℕ → E) (M : ℝ) (hM : ∀ j, ‖u j‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ w : E, Tendsto (fun j => inner ℝ (u (s j)) w) atTop (𝓝 (inner ℝ v w)) := by
  let f : ℕ → WeakDual ℝ E := fun j => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u j))
  have hf : ∀ j, f j ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) M := by
    intro j
    simpa [f,mem_closedBall,dist_zero_right] using hM j
  obtain ⟨v,hv,s,hs,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hf
  let w := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual v)
  refine ⟨w,?_,s,hs,fun x => ?_⟩
  · have hw := (InnerProductSpace.toDual ℝ E).symm.norm_map (WeakDual.toStrongDual v)
    rw [hw]
    simpa only [mem_preimage,mem_closedBall,dist_zero_right] using hv
  · have hh := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hlim) x
    change Tendsto (fun j => inner ℝ (u (s j)) x) atTop (𝓝 ((WeakDual.toStrongDual v) x)) at hh
    simpa only [w,InnerProductSpace.toDual_symm_apply] using hh

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_CriticalEnergy
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [SeparableSpace H] in
lemma inner_tendsto_map [SeparableSpace H] (I : H →L[ℝ] E) {u : ℕ → H} {v : H}
    (h : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w))) (w : E) :
    Tendsto (fun j => inner ℝ (I (u j)) w) atTop (𝓝 (inner ℝ (I v) w)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using h (I.adjoint w)

lemma exists_weak_strong_subsequence (I : H →L[ℝ] E) (hI : IsCompactOperator I)
    (u : ℕ → H) (M : ℝ) (hM : ∀ j, ‖u j‖ ≤ M) :
    ∃ v : H, ‖v‖ ≤ M ∧ ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ w, Tendsto (fun j => inner ℝ (u (s j)) w) atTop (𝓝 (inner ℝ v w))) ∧
      Tendsto (fun j => I (u (s j))) atTop (𝓝 (I v)) := by
  obtain ⟨v,hv,s,hs,hw⟩ := exists_inner_weak_subsequence u M hM
  have hc := hI.isCompact_closure_image_closedBall M
  have hmem (j : ℕ) : I (u (s j)) ∈ closure (I '' closedBall (0 : H) M) :=
    subset_closure ⟨u (s j),by simpa using hM (s j),rfl⟩
  obtain ⟨z,hz,t,ht,hl⟩ := hc.isSeqCompact hmem
  have hweak (w : H) := (hw w).comp ht.tendsto_atTop
  have heq : z = I v := by
    apply ext_inner_right ℝ
    intro w
    have h1 : Tendsto (fun j => inner ℝ (I (u (s (t j)))) w) atTop (𝓝 (inner ℝ z w)) :=
      (show Continuous (fun x : E => inner ℝ x w) from continuous_id.inner continuous_const).continuousAt.tendsto.comp hl
    have h2 := inner_tendsto_map I (u := fun j => u (s (t j))) hweak w
    exact tendsto_nhds_unique h1 h2
  exact ⟨v,hv,s ∘ t,hs.comp ht,hweak,by simpa [heq,Function.comp_def] using hl⟩

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F] in
lemma energy_nonneg [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F]
    (I : H →L[ℝ] E) (G : H →L[ℝ] F) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (u : H) : 0 ≤ energy I G A B u := by
  exact add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F] in
lemma energy_smul [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F]
    (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B c : ℝ) (u : H) :
    energy I G A B (c • u) = c^2*energy I G A B u := by
  simp only [energy,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma energy_defect (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B : ℝ)
    {u : ℕ → H} {v : H} {Λ : ℝ}
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ)) :
    Tendsto (fun j => energy I G A B (u j-v)) atTop (𝓝 (Λ-energy I G A B v)) := by
  have hG := inner_tendsto_map G hweak (G v)
  have hI := inner_tendsto_map I hweak (I v)
  have hh := ((hQ.sub ((hG.const_mul (2*A)).add (hI.const_mul (2*B)))).add_const
    (energy I G A B v))
  simp only [real_inner_self_eq_norm_sq] at hh
  convert hh using 1
  · ext j
    simp only [energy,map_sub,norm_sub_sq_real]
    ring
  · congr 1
    dsimp [energy]
    ring

lemma energy_le_limit (I : H →L[ℝ] E) (G : H →L[ℝ] F) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {u : ℕ → H} {v : H} {Λ : ℝ}
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ)) :
    energy I G A B v ≤ Λ := by
  have hh := ge_of_tendsto' (energy_defect I G A B hweak hQ)
    (fun j => energy_nonneg I G hA hB (u j-v))
  linarith

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_NoLoss
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma critical_no_loss (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A B p S Λ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 2 < p)
    (hΛ : 0 ≤ Λ) (hΛS : Λ < S)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    (hmin : ∀ u, Λ*(criticalNorm I p u)^2 ≤ energy I G A B u)
    (hsob : ∀ ε : ℝ, 0 < ε → ε < S → ∃ C ≥ (0:ℝ), ∀ u,
      (S-ε)*(criticalNorm I p u)^2 ≤ A*‖G u‖^2+C*‖I u‖^2)
    {u : ℕ → H} {v : H}
    (hu : ∀ j, criticalNorm I p (u j) = 1)
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ))
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hstrong : Tendsto (fun j => I (u j)) atTop (𝓝 (I v)))
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j => (I (u j)) x) atTop (𝓝 ((I v) x))) :
    criticalNorm I p v = 1 ∧ energy I G A B v = Λ := by
  have hp0 : 0 < p := by linarith
  have ha : 0 < 2/p := div_pos (by norm_num) hp0
  have ha1 : 2/p ≤ 1 := (div_le_one hp0).mpr hp.le
  have hS : 0 < S := hΛ.trans_lt hΛS
  have hmass := criticalMass_defect I (by linarith : 1 ≤ p) hm hu hae
  have ht := criticalMass_nonneg I p v
  have ht1 : criticalMass I p v ≤ 1 := by
    have hh := ge_of_tendsto' hmass (fun j => criticalMass_nonneg I p (u j-v))
    linarith
  have hdef := energy_defect I G A B hweak hQ
  have hIz : Tendsto (fun j => ‖I (u j-v)‖^2) atTop (𝓝 0) := by
    have hh := ((hstrong.sub_const (I v)).norm).pow 2
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),map_sub] using hh
  have hib (ε : ℝ) (hε : 0 < ε) (hεS : ε < S) :
      (S-ε)*(1-criticalMass I p v)^(2/p) ≤ Λ-energy I G A B v := by
    obtain ⟨C,hC,hb⟩ := hsob ε hε hεS
    have hl := (hmass.rpow_const (Or.inr ha.le)).const_mul (S-ε)
    have hr := hdef.add (hIz.const_mul C)
    simp only [mul_zero,add_zero] at hr
    apply le_of_tendsto_of_tendsto' hl hr
    intro j
    have hh := hb (u j-v)
    rw [criticalNorm_sq I hp0] at hh
    exact hh.trans (by dsimp [energy]; nlinarith [mul_nonneg hB (sq_nonneg ‖I (u j-v)‖)])
  have hlow := hmin v
  rw [criticalNorm_sq I hp0] at hlow
  have hcc := concentration_inequality ha ht ht1 hS hlow hib
  have hmass1 := no_loss ha1 hΛ hΛS ht ht1 hcc
  have hn2 := criticalNorm_sq I hp0 v
  rw [hmass1,Real.one_rpow] at hn2
  have hn1 : criticalNorm I p v = 1 := by
    nlinarith [criticalNorm_nonneg I p v]
  refine ⟨hn1,le_antisymm (energy_le_limit I G hA hB hweak hQ) ?_⟩
  have hh := hmin v
  simpa only [hn1,one_pow,mul_one] using hh

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H : Type*} [AddCommGroup H] [Module ℝ H]

lemma normalized_infimum (N Q : H → ℝ)
    (hN : ∀ u, 0 ≤ N u) (hQ : ∀ u, 0 ≤ Q u)
    (hNs : ∀ c u, N (c • u) = |c| *N u)
    (hQs : ∀ c u, Q (c • u) = c^2*Q u)
    (v : H) (hv : 0 < N v) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ ≤ Q v/(N v)^2 ∧
      (∀ u, Λ*(N u)^2 ≤ Q u) ∧
      ∃ u : ℕ → H, (∀ j, N (u j) = 1) ∧
        (∀ j, Q (u j) ≤ Q (u 0)) ∧ Tendsto (fun j => Q (u j)) atTop (𝓝 Λ) := by
  classical
  let C : Set ℝ := {q | ∃ u, N u = 1 ∧ Q u = q}
  have hunit {u : H} (hu : 0 < N u) : N ((N u)⁻¹ • u) = 1 := by
    rw [hNs,abs_of_pos (inv_pos.mpr hu),inv_mul_cancel₀ hu.ne']
  have hC : C.Nonempty := ⟨Q ((N v)⁻¹ • v),_,hunit hv,rfl⟩
  have hCb : BddBelow C := ⟨0,by rintro q ⟨u,hu,rfl⟩; exact hQ u⟩
  let Λ := sInf C
  have hΛ : 0 ≤ Λ := le_csInf hC (by rintro q ⟨u,hu,rfl⟩; exact hQ u)
  have hmin (u : H) : Λ*(N u)^2 ≤ Q u := by
    by_cases hu : N u = 0
    · simp only [hu,zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact hQ u
    have hu' : 0 < N u := lt_of_le_of_ne (hN u) (Ne.symm hu)
    have hh : Λ ≤ Q ((N u)⁻¹ • u) := csInf_le hCb ⟨_,hunit hu',rfl⟩
    rw [hQs,inv_pow] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg (N u))
    calc
      Λ*(N u)^2 ≤ ((N u)^2)⁻¹*Q u*(N u)^2 := hh'
      _ = Q u := by rw [mul_assoc,mul_comm (Q u),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hu),one_mul]
  have hvb : Λ ≤ Q v/(N v)^2 := (le_div_iff₀ (sq_pos_of_pos hv)).mpr (hmin v)
  obtain ⟨a,haanti,halim,ha⟩ := exists_seq_tendsto_sInf hC hCb
  choose u huN huQ using ha
  refine ⟨Λ,hΛ,hvb,hmin,u,huN,fun j => ?_,?_⟩
  · simpa only [huQ] using haanti (show 0 ≤ j from Nat.zero_le j)
  · simpa only [huQ] using halim

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Distribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma negativeTail_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (negativeTail μ).measure = μ := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (-μ.real (Ioi b) - -μ.real (Ioi a)) = μ (Ioc a b)
  have hsplit : μ.real (Ioi a) = μ.real (Ioc a b) + μ.real (Ioi b) := by
    rw [←measureReal_union (by simp [Set.disjoint_left]) measurableSet_Ioi]
    congr 1
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · intro h
      by_cases hx : x ≤ b
      · exact Or.inl ⟨h,hx⟩
      · exact Or.inr (not_le.mp hx)
    · rintro (h|h)
      · exact h.1
      · exact hab.trans h
  rw [hsplit]
  convert ENNReal.ofReal_toReal (measure_ne_top μ (Ioc a b)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [measureReal_def]
  congr 1
  ring

lemma ae_hasDerivAt_tail (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ t : ℝ, HasDerivAt (fun s => μ.real (Ioi s))
      (-(μ.rnDeriv volume t).toReal) t := by
  have h := (negativeTail μ).ae_hasDerivAt
  rw [negativeTail_measure] at h
  filter_upwards [h] with t ht
  have hn := ht.neg
  change HasDerivAt (fun s => - -μ.real (Ioi s)) _ t at hn
  simpa only [neg_neg] using hn

lemma stieltjes_secant_lower (f : StieltjesFunction ℝ) {a b c : ℝ}
    (hab : a ≤ b)
    (hc : ∀ᵐ x ∂volume.restrict (Ioc a b), c ≤ deriv f x) :
    c * (b-a) ≤ f b-f a := by
  have hfin : f.measure (Ioc a b) ≠ ∞ := by
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  have hle : ∀ᵐ x ∂volume.restrict (Ioc a b),
      c ≤ (f.measure.rnDeriv volume x).toReal := by
    filter_upwards [hc, ae_restrict_of_ae f.ae_hasDerivAt] with x hx hd
    simpa only [hd.deriv] using hx
  calc
    c * (b-a) = ∫ x in Ioc a b, c := by
      simp [integral_const, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
        measureReal_def, mul_comm]
    _ ≤ ∫ x in Ioc a b, (f.measure.rnDeriv volume x).toReal :=
      integral_mono_ae (integrable_const c)
        (Measure.integrableOn_toReal_rnDeriv hfin) hle
    _ ≤ f.measure.real (Ioc a b) := Measure.setIntegral_toReal_rnDeriv_le hfin
    _ = f b - f a := by
      rw [measureReal_def, StieltjesFunction.measure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hab))]

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

variable (μ : Measure ℝ) {ω : ℝ} {n : ℕ}

lemma radius_nonneg [IsFiniteMeasure μ] (hω : 0 ≤ ω) (t : ℝ) :
    0 ≤ radiusDistribution μ ω n t :=
  Real.rpow_nonneg (div_nonneg measureReal_nonneg hω) _

lemma radius_pos [IsFiniteMeasure μ] (hω : 0 < ω) {t : ℝ} (ht : 0 < μ.real (Ioi t)) :
    0 < radiusDistribution μ ω n t := Real.rpow_pos_of_pos (div_pos ht hω) _

lemma radius_pow [IsFiniteMeasure μ] (hω : 0 < ω) (hn : 0 < n) (t : ℝ) :
    ω*(radiusDistribution μ ω n t)^n = μ.real (Ioi t) := by
  rw [radiusDistribution,one_div,Real.rpow_inv_natCast_pow
    (div_nonneg measureReal_nonneg hω.le) hn.ne']
  exact mul_div_cancel₀ _ hω.ne'

variable [IsFiniteMeasure μ]

lemma ae_radius_derivative (hω : 0 < ω) (hn : 0 < n) :
    ∀ᵐ t : ℝ, HasDerivAt (radiusDistribution μ ω n)
      (deriv (radiusDistribution μ ω n) t) t ∧
      (n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)*
        deriv (radiusDistribution μ ω n) t = -(μ.rnDeriv volume t).toReal := by
  filter_upwards [(radius_antitone μ (n := n) hω.le).neg.ae_differentiableAt,
    ae_hasDerivAt_tail μ] with t ht htail
  have ht : DifferentiableAt ℝ (radiusDistribution μ ω n) t := by simpa using ht.neg
  refine ⟨ht.hasDerivAt,?_⟩
  have hpow := (ht.hasDerivAt.pow n).const_mul ω
  have he : (fun s => μ.real (Ioi s)) =ᶠ[𝓝 t]
      (fun s => ω*(radiusDistribution μ ω n s)^n) :=
    Eventually.of_forall (fun s => (radius_pow μ hω hn s).symm)
  have hc := (hpow.congr_of_eventuallyEq he).unique htail
  nlinarith only [hc]

lemma radius_secant_from_coarea (hω : 0 < ω) (hn : 0 < n) {U K η : ℝ}
    (hK : 0 < K) {P : ℝ → ℝ}
    (hpos : ∀ t ∈ Ioo 0 U, 0 < μ.real (Ioi t))
    (hP : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal) :
    ∀ s t : ℝ, 0 < s → s < t → t < U →
      ((1-η)/K)*(t-s) ≤ radiusDistribution μ ω n s-radiusDistribution μ ω n t := by
  have hd : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)/K ≤ deriv (negativeRadius μ hω hn) t := by
    filter_upwards [hP,ae_restrict_of_ae (ae_radius_derivative μ hω hn),
      (ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂volume.restrict (Ioo 0 U), t ∈ Ioo 0 U)]
      with t hp hdt ht
    have hA : 0 < (n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1) := by
      exact mul_pos (mul_pos (by exact_mod_cast hn) hω)
        (pow_pos (radius_pos μ hω (hpos t ht)) _)
    have he : deriv (negativeRadius μ hω hn) t =
        -deriv (radiusDistribution μ ω n) t := by
      exact hdt.1.neg.deriv
    rw [he,div_le_iff₀ hK]
    have hle := hp.1.trans hp.2
    have hh := hdt.2
    nlinarith
  intro s t hs hst htU
  have hsub : Ioc s t ⊆ Ioo (0:ℝ) U := fun x hx => ⟨hs.trans hx.1,hx.2.trans_lt htU⟩
  have hdd : ∀ᵐ x ∂volume.restrict (Ioc s t),
      (1-η)/K ≤ deriv (negativeRadius μ hω hn) x :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hd
  have hslope := stieltjes_secant_lower (negativeRadius μ hω hn) hst.le hdd
  change ((1-η)/K)*(t-s) ≤ -radiusDistribution μ ω n t - -radiusDistribution μ ω n s at hslope
  linarith only [hslope]

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Cauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal

namespace CAT0Fillings.RadialSobolev

lemma integral_cs_square {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    (∫ x, a x*b x ∂μ)^2 ≤ (∫ x, (a x)^2 ∂μ)*(∫ x, (b x)^2 ∂μ) := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using ha) (by simpa using hb)
  have he (f : α → ℝ) : (fun x => ‖f x‖^(2:ℝ)) = (fun x => (f x)^2) := by
    funext x
    simp [Real.norm_eq_abs,sq_abs]
  rw [he a,he b,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hh
  have hi : |∫ x, a x*b x ∂μ| ≤ ∫ x, ‖a x‖*‖b x‖ ∂μ := by
    simpa only [Real.norm_eq_abs,abs_mul] using norm_integral_le_integral_norm (f := fun x => a x*b x) (μ := μ)
  have ha0 : 0 ≤ ∫ x, (a x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hb0 : 0 ≤ ∫ x, (b x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hbound := hi.trans hh
  have hs := sq_le_sq₀ (abs_nonneg (∫ x, a x*b x ∂μ))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hbound
  simpa only [sq_abs,mul_pow,Real.sq_sqrt ha0,Real.sq_sqrt hb0] using hs

end CAT0Fillings.RadialSobolev
end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CAT0Fillings.RadialSobolev

lemma continuous_memLp_Icc {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp h p (volume.restrict (Icc a b)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hh.continuousOn
  apply MemLp.of_bound hh.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

lemma continuous_mul_deriv_memLp_Icc {h f : ℝ → ℝ} {K : ℝ≥0}
    (hh : Continuous h) (hf : LipschitzWith K f) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => h x*deriv f x) p (volume.restrict (Icc a b)) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hh.continuousOn
  apply MemLp.of_bound (hh.aestronglyMeasurable.mul (measurable_deriv f).aestronglyMeasurable) (C*K)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul (hC x hx) (norm_deriv_le_of_lipschitz hf) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx))

lemma weighted_interval_cs {w z f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hab : a ≤ b) (hw : Continuous w) (hz : Continuous z) (hf : LipschitzWith K f)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) :
    (∫ x in a..b,w x*deriv f x*z x)^2 ≤
      (∫ x in a..b,w x*(deriv f x)^2)*(∫ x in a..b,w x*(z x)^2) := by
  have hs : Continuous (fun x => Real.sqrt (w x)) := hw.sqrt
  have hc := integral_cs_square
    (continuous_mul_deriv_memLp_Icc hs hf a b 2)
    (continuous_memLp_Icc (hs.mul hz) a b 2)
  dsimp only [Pi.mul_apply] at hc
  have ih : (∫ x in Icc a b, (Real.sqrt (w x)*deriv f x)*(Real.sqrt (w x)*z x)) =
      ∫ x in Icc a b,w x*deriv f x*z x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    have he := Real.sq_sqrt (hw0 x hx)
    calc
      _ = (Real.sqrt (w x))^2*deriv f x*z x := by ring
      _ = _ := by rw [he]
  have ie : (∫ x in Icc a b, (Real.sqrt (w x)*deriv f x)^2) =
      ∫ x in Icc a b,w x*(deriv f x)^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [mul_pow,Real.sq_sqrt (hw0 x hx)]
  have im : (∫ x in Icc a b, (Real.sqrt (w x)*z x)^2) =
      ∫ x in Icc a b,w x*(z x)^2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [mul_pow,Real.sq_sqrt (hw0 x hx)]
  rw [ih,ie,im] at hc
  simpa only [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab] using hc

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_RadialCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

lemma cumulativeOrderIso_apply {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (x : Icc a b) :
    (cumulativeOrderIso hab hF hm x : ℝ) = F x := rfl

lemma cumulativeInverse_mem {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (y : ℝ) :
    cumulativeInverse hab hF hm y ∈ Icc a b := Subtype.property _

lemma cumulativeInverse_continuous {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) :
    Continuous (cumulativeInverse hab hF hm) :=
  continuous_subtype_val.comp ((cumulativeOrderIso hab hF hm).symm.continuous.comp continuous_projIcc)

lemma cumulativeInverse_right {F : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Icc (F a) (F b)) : F (cumulativeInverse hab hF hm y) = y := by
  have hh := congrArg Subtype.val ((cumulativeOrderIso hab hF hm).apply_symm_apply
    (projIcc (F a) (F b) (hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y))
  rw [cumulativeOrderIso_apply] at hh
  simpa only [cumulativeInverse,projIcc_of_mem _ hy] using hh

lemma cumulativeInverse_left {F : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (hx : x ∈ Icc a b) :
    cumulativeInverse hab hF hm (F x) = x := by
  apply hm.injOn (cumulativeInverse_mem hab hF hm _) hx
  exact cumulativeInverse_right hab hF hm
    ⟨hm.monotoneOn ⟨le_rfl,hab⟩ hx hx.1,hm.monotoneOn hx ⟨hab,le_rfl⟩ hx.2⟩

lemma cumulativeInverse_interior {F : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Ioo (F a) (F b)) : cumulativeInverse hab hF hm y ∈ Ioo a b := by
  have hb := cumulativeInverse_mem hab hF hm y
  have he := cumulativeInverse_right hab hF hm ⟨hy.1.le,hy.2.le⟩
  refine ⟨lt_of_le_of_ne hb.1 ?_,lt_of_le_of_ne hb.2 ?_⟩
  · intro hh
    rw [←hh] at he
    exact hy.1.ne he
  · intro hh
    rw [hh] at he
    exact hy.2.ne' he

lemma cumulativeInverse_hasDerivAt {F : ℝ → ℝ} {a b y d : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Ioo (F a) (F b))
    (hd : HasDerivAt F d (cumulativeInverse hab hF hm y)) (hd0 : d ≠ 0) :
    HasDerivAt (cumulativeInverse hab hF hm) d⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse (cumulativeInverse_continuous hab hF hm).continuousAt hd hd0
  filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
  exact cumulativeInverse_right hab hF hm ⟨hz.1.le,hz.2.le⟩

lemma cumulativeTransport_hasDerivAt {F G : ℝ → ℝ} {a b r f' g' : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G (Icc a b)) (hm : StrictMonoOn G (Icc a b))
    (hy : F r ∈ Ioo (G a) (G b)) (hF : HasDerivAt F f' r)
    (hd : HasDerivAt G g' (cumulativeInverse hab hG hm (F r))) (hd0 : g' ≠ 0) :
    HasDerivAt (fun s => cumulativeInverse hab hG hm (F s)) (f'/g') r := by
  simpa only [Function.comp_def,div_eq_mul_inv,mul_comm] using
    (cumulativeInverse_hasDerivAt hab hG hm hy hd hd0).comp r hF

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

lemma radialCDF_zero (n : ℕ) (ω : ℝ) (f : ℝ → ℝ) (p : ℝ) :
    radialCDF n ω f p 0 = 0 := by simp [radialCDF]

lemma radialTransport_continuous {n : ℕ} {ω p D : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r) :
    Continuous (radialTransport (f := f) hD hn hω hg hp hgp) :=
  (cumulativeInverse_continuous _ _ _).comp (radialCDF_continuous hf hp)

lemma radialTransport_cdf {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Icc 0 R) :
    radialCDF n ω g p (radialTransport (f := f) hD hn hω hg hp hgp r) =
      radialCDF n ω f p r := by
  apply cumulativeInverse_right
  have hm := (radialCDF_strictMonoOn hn hω hf hp hfp).monotoneOn
  constructor
  · simpa only [radialCDF_zero] using hm (show 0 ∈ Icc 0 R from ⟨le_rfl,hr.1.trans hr.2⟩) hr hr.1
  · rw [←hmass]
    exact hm hr ⟨hr.1.trans hr.2,le_rfl⟩ hr.2

lemma radialTransport_interior {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Ioo 0 R) :
    radialTransport (f := f) hD hn hω hg hp hgp r ∈ Ioo 0 D := by
  apply cumulativeInverse_interior
  have hm := radialCDF_strictMonoOn hn hω hf hp hfp
  constructor
  · simpa only [radialCDF_zero] using hm
      (show 0 ∈ Icc 0 R from ⟨le_rfl,(hr.1.trans hr.2).le⟩) ⟨hr.1.le,hr.2.le⟩ hr.1
  · rw [←hmass]
    exact hm ⟨hr.1.le,hr.2.le⟩ ⟨(hr.1.trans hr.2).le,le_rfl⟩ hr.2

lemma radialTransport_hasDerivAt {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (radialTransport (f := f) hD hn hω hg hp hgp)
      (((n:ℝ)*ω*r^(n-1)*(f r)^p) /
        ((n:ℝ)*ω*(radialTransport (f := f) hD hn hω hg hp hgp r)^(n-1)*
          (g (radialTransport (f := f) hD hn hω hg hp hgp r))^p)) r := by
  have ht := radialTransport_interior hD hn hω hf hg hp hfp hgp hmass hr
  have hv : radialCDF n ω f p r ∈ Ioo (radialCDF n ω g p 0) (radialCDF n ω g p D) := by
    rw [←radialTransport_cdf hD hn hω hf hg hp hfp hgp hmass ⟨hr.1.le,hr.2.le⟩]
    have hm := radialCDF_strictMonoOn hn hω hg hp hgp
    exact ⟨hm ⟨le_rfl,hD⟩ ⟨ht.1.le,ht.2.le⟩ ht.1,
      hm ⟨ht.1.le,ht.2.le⟩ ⟨hD,le_rfl⟩ ht.2⟩
  apply cumulativeTransport_hasDerivAt hD (radialCDF_continuous hg hp).continuousOn
    (radialCDF_strictMonoOn hn hω hg hp hgp) hv
    (radialCDF_hasDerivAt hf hp) (radialCDF_hasDerivAt hg hp)
  exact ne_of_gt (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
    (Real.rpow_pos_of_pos (hgp _ ht) _))

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_AbsoluteContinuity
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.RadialSobolev

section
variable {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
  (hR : 0 < R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
  (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
  (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
  (hmass : radialCDF n ω f p R = radialCDF n ω g p D)

lemma radialTransport_zero : radialTransport (f := f) hD.le hn hω hg hp hgp 0 = 0 := by
  change cumulativeInverse _ _ _ (radialCDF n ω f p 0) = 0
  simpa only [radialCDF_zero] using
    cumulativeInverse_left hD.le (radialCDF_continuous hg hp).continuousOn
      (radialCDF_strictMonoOn hn hω hg hp hgp) ⟨le_rfl,hD.le⟩

include hmass in
lemma radialTransport_top : radialTransport (f := f) hD.le hn hω hg hp hgp R = D := by
  change cumulativeInverse _ _ _ (radialCDF n ω f p R) = D
  rw [hmass]
  exact cumulativeInverse_left _ _ _ ⟨hD.le,le_rfl⟩

include hf hfp hmass

lemma radialTransport_deriv_pos {r : ℝ} (hr : r ∈ Ioo 0 R) :
    0 < deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  exact div_pos
    (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos hr.1 _))
      (Real.rpow_pos_of_pos (hfp r hr) _))
    (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
      (Real.rpow_pos_of_pos (hgp _ ht) _))

lemma radialTransport_jacobian {r : ℝ} (hr : r ∈ Ioo 0 R) :
    deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r *
      (radialTransport (f := f) hD.le hn hω hg hp hgp r/r)^(n-1) =
      (f r)^p/(g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^p := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hg0 := (Real.rpow_pos_of_pos (hgp _ ht) p).ne'
  rw [div_pow]
  field_simp [hn0,hω.ne',hr.1.ne',ht.1.ne']

lemma radialTransport_weighted_jacobian {r : ℝ} (hr : r ∈ Ioo 0 R) :
    deriv (radialTransport (f := f) hD.le hn hω hg hp hgp) r *
      ((n:ℝ)*ω*(radialTransport (f := f) hD.le hn hω hg hp hgp r)^(n-1)*
        (g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^p) =
      (n:ℝ)*ω*r^(n-1)*(f r)^p := by
  rw [(radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).deriv]
  have ht := radialTransport_interior hD.le hn hω hf hg hp hfp hgp hmass hr
  apply div_mul_cancel₀
  exact ne_of_gt (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
    (Real.rpow_pos_of_pos (hgp _ ht) _))

end
end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma ac_congr {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (he : EqOn f g (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := hf ε hε
  refine ⟨δ,hδ,fun E hE hlen => ?_⟩
  have hs : (∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he (hE.1 i hi).1,he (hE.1 i hi).2]
  rw [hs]
  exact hh E hE hlen

lemma ac_of_nonnegative_derivative {t t' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn t (Icc a b))
    (hd : ∀ r ∈ Ioo a b, HasDerivAt t (t' r) r)
    (hp : ∀ r ∈ Ioo a b, 0 ≤ t' r) : AbsolutelyContinuousOnInterval t a b := by
  have hi : IntervalIntegrable t' volume a b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · simpa only [uIcc_of_le hab] using hc
    · simpa only [min_eq_left hab,max_eq_right hab] using hd
    · simpa only [min_eq_left hab,max_eq_right hab] using hp
  have ha := hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hk : AbsolutelyContinuousOnInterval (fun _ : ℝ => t a) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  apply ac_congr (ha.add hk)
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1,uIcc_of_le hab]
    exact Icc_subset_Icc_right hx.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (Icc_subset_Icc_right hx.2))
    (fun r hr => hd r ⟨hr.1,hr.2.trans_le hx.2⟩) (hi.mono_set hsub)
  change (∫ r in a..x,t' r)+t a=t x
  rw [he,sub_add_cancel]

lemma lipschitz_power_ac {f : ℝ → ℝ} {K : ℝ≥0} {a b q : ℝ}
    (hf : LipschitzWith K f) (hq : 1 ≤ q) :
    AbsolutelyContinuousOnInterval (fun r => (f r)^q) a b := by
  obtain ⟨C,hC⟩ := isCompact_uIcc.bddBelow_image (hf.continuous.continuousOn (s := uIcc a b))
  obtain ⟨B,hB⟩ := isCompact_uIcc.bddAbove_image (hf.continuous.continuousOn (s := uIcc a b))
  have hp : ContDiffOn ℝ 1 (fun x : ℝ => x^q) (Icc C B) :=
    (Real.contDiff_rpow_const_of_le (by exact_mod_cast hq)).contDiffOn
  obtain ⟨L,hL⟩ := hp.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have hrange : MapsTo f (uIcc a b) (Icc C B) := by
    intro x hx
    exact ⟨hC ⟨x,hx,rfl⟩,hB ⟨x,hx,rfl⟩⟩
  exact (hL.comp hf.lipschitzOnWith hrange).absolutelyContinuousOnInterval

lemma radial_agm {n : ℕ} (hn : 0 < n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (n:ℝ)*(a*b^(n-1))^((n:ℝ)⁻¹) ≤ a+((n:ℝ)-1)*b := by
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ (n:ℝ)⁻¹ by positivity)
    (show 0 ≤ ((n:ℝ)-1)/(n:ℝ) by positivity) ha hb
    (show (n:ℝ)⁻¹+((n:ℝ)-1)/(n:ℝ)=1 by field_simp; ring)
  rw [Real.mul_rpow ha (pow_nonneg hb _),←Real.rpow_natCast b (n-1),
    ←Real.rpow_mul hb] at *
  have he : ((n-1:ℕ):ℝ)*(n:ℝ)⁻¹ = ((n:ℝ)-1)/(n:ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one,div_eq_mul_inv]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left h hnR.le
  have heq : (n:ℝ)*((n:ℝ)⁻¹*a+((n:ℝ)-1)/(n:ℝ)*b) = a+((n:ℝ)-1)*b := by
    field_simp
  rw [heq] at hm
  exact hm

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_RadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma weightedTransport_hasDerivAt {n : ℕ} {t : ℝ → ℝ} {r d : ℝ}
    (ht : HasDerivAt t d r) :
    HasDerivAt (fun s => s^(n-1)*t s)
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*d) r := by
  simpa [Nat.sub_sub] using ((hasDerivAt_id r).fun_pow (n-1)).fun_mul ht

lemma radial_integration_by_parts {n : ℕ} {f t : ℝ → ℝ} {K : ℝ≥0} {R q : ℝ}
    (hn : 2 ≤ n) (hR : 0 ≤ R) (hf : LipschitzWith K f) (hq : 1 ≤ q) (hfR : f R = 0)
    (ht : AbsolutelyContinuousOnInterval t 0 R)
    (hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r) :
    (∫ r in (0:ℝ)..R, (f r)^q*
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r)) =
      -q*∫ r in (0:ℝ)..R, r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
  have hu : AbsolutelyContinuousOnInterval (fun r => (f r)^q) 0 R := lipschitz_power_ac hf hq
  have hv : AbsolutelyContinuousOnInterval (fun r => r^(n-1)*t r) 0 R :=
    (contDiff_id.pow (n-1)).contDiffOn.absolutelyContinuousOnInterval.fun_mul ht
  have hparts := hu.integral_mul_deriv_eq_deriv_mul hv
  have hn0 : n-1 ≠ 0 := by omega
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hboundary : (f R)^q*(R^(n-1)*t R)-(f 0)^q*((0:ℝ)^(n-1)*t 0)=0 := by
    simp [hfR,Real.zero_rpow hq0,zero_pow hn0]
  rw [hboundary,zero_sub] at hparts
  have hleft : (∫ r in (0:ℝ)..R, (f r)^q*deriv (fun s => s^(n-1)*t s) r) =
      ∫ r in (0:ℝ)..R,(f r)^q*(((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hR
    intro r hr
    dsimp only
    exact congrArg (fun z => (f r)^q*z)
      (weightedTransport_hasDerivAt (n := n) (hdt r hr).hasDerivAt).deriv
  rw [hleft] at hparts
  have hright : (∫ r in (0:ℝ)..R, deriv (fun s => (f s)^q) r*(r^(n-1)*t r)) =
      q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with r hr hmem
    rw [(hr.hasDerivAt.rpow_const (Or.inr hq)).deriv]
    ring
  rw [hright] at hparts
  simpa only [neg_mul] using hparts

lemma radialTransport_ac {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
    (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) :
    AbsolutelyContinuousOnInterval (radialTransport (f := f) hD.le hn hω hg hp hgp) 0 R := by
  apply ac_of_nonnegative_derivative hR (radialTransport_continuous hD.le hn hω hf hg hp hgp).continuousOn
  · intro r hr
    exact (radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).differentiableAt.hasDerivAt
  · intro r hr
    exact (radialTransport_deriv_pos hD hn hω hf hg hp hfp hgp hmass hr).le

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

section
variable {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
  (hR : 0 ≤ R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
  (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
  (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
  (hmass : radialCDF n ω f p R = radialCDF n ω g p D)

include hR hf hfp hmass

lemma radialTransport_integral_moment (H : ℝ → ℝ) :
    (∫ s in (0:ℝ)..D, (n:ℝ)*ω*s^(n-1)*(g s)^p*H s) =
    ∫ r in (0:ℝ)..R, (n:ℝ)*ω*r^(n-1)*(f r)^p*
      H (radialTransport (f := f) hD.le hn hω hg hp hgp r) := by
  let t := radialTransport (f := f) hD.le hn hω hg hp hgp
  have he : (∫ r in (0:ℝ)..R,
      ((n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p*H (t r))*deriv t r) =
      ∫ s in t 0..t R, (n:ℝ)*ω*s^(n-1)*(g s)^p*H s := by
    apply intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := t) (f' := deriv t)
      (g := fun s => (n:ℝ)*ω*s^(n-1)*(g s)^p*H s)
    · exact (radialTransport_continuous hD.le hn hω hf hg hp hgp).continuousOn
    · simp only [min_eq_left hR,max_eq_right hR]
      intro r hr
      exact (radialTransport_hasDerivAt hD.le hn hω hf hg hp hfp hgp hmass hr).differentiableAt.hasDerivAt
    · simp only [min_eq_left hR,max_eq_right hR]
      exact fun r hr => (radialTransport_deriv_pos hD hn hω hf hg hp hfp hgp hmass hr).le
  change (∫ s in (0:ℝ)..D, _) = ∫ r in (0:ℝ)..R, _
  have ht0 : t 0 = 0 := radialTransport_zero hD hn hω hg hp hgp
  have htR : t R = D := radialTransport_top hD hn hω hg hp hgp hmass
  rw [ht0,htR] at he
  rw [←he]
  apply intervalIntegral.integral_congr_Ioo_of_le hR
  intro r hr
  dsimp only
  calc
    (n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p*H (t r)*deriv t r =
        (deriv t r*((n:ℝ)*ω*(t r)^(n-1)*(g (t r))^p))*H (t r) := by ring
    _ = (n:ℝ)*ω*r^(n-1)*(f r)^p*H (t r) := by
      rw [radialTransport_weighted_jacobian hD hn hω hf hg hp hfp hgp hmass hr]

end

lemma transport_power_identity {a b p q m : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : q+p*m=p) : a^q*(a^p/b^p)^m = a^p*b^(q-p) := by
  rw [Real.div_rpow (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _),
    ←Real.rpow_mul ha.le,←Real.rpow_mul hb.le,←mul_div_assoc,←Real.rpow_add ha]
  rw [hm]
  have he : q-p = -(p*m) := by linarith
  rw [he,Real.rpow_neg hb.le,div_eq_mul_inv]

lemma transport_pointwise_agm {n : ℕ} {a b u v p q : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hq : q+p/(n:ℝ)=p) (hjac : u*v^(n-1)=a^p/b^p) :
    (n:ℝ)*a^p*b^(q-p) ≤ a^q*(u+(n-1:ℕ)*v) := by
  have h := mul_le_mul_of_nonneg_left (radial_agm hn hu hv) (Real.rpow_nonneg ha.le q)
  rw [hjac] at h
  have hid := transport_power_identity ha hb (m := 1/(n:ℝ)) (by simpa only [mul_one_div] using hq)
  simp only [one_div] at hid
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  nlinarith [hid]

end CAT0Fillings.RadialSobolev

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Integrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

section
variable {n : ℕ} {ω p R D : ℝ} {f g : ℝ → ℝ}
  (hR : 0 ≤ R) (hD : 0 < D) (hn : 0 < n) (hω : 0 < ω)
  (hf : Continuous f) (hg : Continuous g) (hp : 0 < p)
  (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
  (hmass : radialCDF n ω f p R = radialCDF n ω g p D)
include hR hf hfp hmass

lemma radialTransport_integral_moment_unscaled (H : ℝ → ℝ) :
    (∫ s in (0:ℝ)..D, s^(n-1)*(g s)^p*H s) =
    ∫ r in (0:ℝ)..R, r^(n-1)*(f r)^p*
      H (radialTransport (f := f) hD.le hn hω hg hp hgp r) := by
  apply mul_left_cancel₀ (ne_of_gt (mul_pos (Nat.cast_pos.mpr hn) hω))
  simpa only [←intervalIntegral.integral_const_mul,mul_assoc] using
    radialTransport_integral_moment hR hD hn hω hf hg hp hfp hgp hmass H

lemma radialTransport_integral_power (q : ℝ) :
    (∫ s in (0:ℝ)..D, s^(n-1)*(g s)^q) =
    ∫ r in (0:ℝ)..R, r^(n-1)*(f r)^p*
      (g (radialTransport (f := f) hD.le hn hω hg hp hgp r))^(q-p) := by
  rw [←radialTransport_integral_moment_unscaled hR hD hn hω hf hg hp hfp hgp hmass (fun s => (g s)^(q-p))]
  apply intervalIntegral.integral_congr_Ioo_of_le hD.le
  intro s hs
  dsimp only
  rw [mul_assoc,←Real.rpow_add (hgp s hs)]
  congr 2
  ring

end

lemma radial_divergence_algebra {n : ℕ} {r t d : ℝ} (hn : 2 ≤ n) (hr : r ≠ 0) :
    r^(n-1)*(d+(n-1:ℕ)*t/r) = (n-1:ℕ)*r^(n-2)*t+r^(n-1)*d := by
  have he : n-1 = n-2+1 := by omega
  rw [he,pow_succ]
  field_simp
  ring

lemma weighted_transport_derivative_integrable {n : ℕ} {f t : ℝ → ℝ} {R q : ℝ}
    (hR : 0 ≤ R) (hf : Continuous f) (hq : 0 ≤ q)
    (ht : AbsolutelyContinuousOnInterval t 0 R)
    (hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r) :
    IntervalIntegrable (fun r => (f r)^q*
      (((n-1:ℕ):ℝ)*r^(n-2)*t r+r^(n-1)*deriv t r)) volume 0 R := by
  have hv : AbsolutelyContinuousOnInterval (fun r => r^(n-1)*t r) 0 R :=
    (contDiff_id.pow (n-1)).contDiffOn.absolutelyContinuousOnInterval.fun_mul ht
  have hh := hv.intervalIntegrable_deriv.continuousOn_mul
    (hf.rpow_const (fun _ => Or.inr hq)).continuousOn
  apply hh.congr_uIoo
  simp only [uIoo_of_le hR]
  intro r hr
  dsimp only
  rw [(weightedTransport_hasDerivAt (n := n) (hdt r hr).hasDerivAt).deriv]

lemma finite_transport_ibp {n : ℕ} {ω p q R D : ℝ} {f g : ℝ → ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 2 ≤ n) (hω : 0 < ω)
    (hf : LipschitzWith K f) (hg : Continuous g) (hp : 0 < p) (hq : 1 ≤ q)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r, 0 < g r) (hfR : f R = 0)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D)
    (hexp : q+p/(n:ℝ)=p) :
    (n:ℝ)*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q) ≤
      -q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*
        radialTransport (f := f) hD.le (by omega : 0 < n) hω hg hp (fun r _ => hgp r) r := by
  have hn0 : 0 < n := by omega
  let t := radialTransport (f := f) hD.le hn0 hω hg hp (fun r _ => hgp r)
  have ht : Continuous t := radialTransport_continuous _ _ _ hf.continuous hg hp _
  have hta : AbsolutelyContinuousOnInterval t 0 R :=
    radialTransport_ac hR hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass
  have hdt : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ t r := fun r hr =>
    (radialTransport_hasDerivAt hD.le hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr).differentiableAt
  have hA := weighted_transport_derivative_integrable (n := n) hR hf.continuous (by linarith : 0 ≤ q) hta hdt
  have hJ : Continuous (fun r => r^(n-1)*(f r)^p*(g (t r))^(q-p)) :=
    ((continuous_id.pow _).mul (hf.continuous.rpow_const (fun _ => Or.inr hp.le))).mul
      ((hg.comp ht).rpow_const (fun r => Or.inl (hgp (t r)).ne'))
  rw [radialTransport_integral_power hR hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass q,
    ←intervalIntegral.integral_const_mul]
  calc
    (∫ r in (0:ℝ)..R,(n:ℝ)*(r^(n-1)*(f r)^p*(g (t r))^(q-p))) ≤
        ∫ r in (0:ℝ)..R,(f r)^q*((n-1:ℕ)*r^(n-2)*t r+r^(n-1)*deriv t r) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hR
        (hJ.intervalIntegrable _ _ |>.const_mul _) hA
      intro r hr
      have hpos := radialTransport_deriv_pos hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr
      have htp := radialTransport_interior hD.le hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr
      have hagm := transport_pointwise_agm hn0 (hfp r hr) (hgp (t r)) hpos.le
        (div_nonneg htp.1.le hr.1.le) hexp
        (radialTransport_jacobian hD hn0 hω hf.continuous hg hp hfp (fun r _ => hgp r) hmass hr)
      have hh := mul_le_mul_of_nonneg_left hagm (pow_nonneg hr.1.le (n-1))
      have he := radial_divergence_algebra (t := t r) (d := deriv t r) hn hr.1.ne'
      change (n:ℝ)*(r^(n-1)*(f r)^p*(g (t r))^(q-p)) ≤ _
      calc
        _ = r^(n-1)*((n:ℝ)*(f r)^p*(g (t r))^(q-p)) := by ring
        _ ≤ r^(n-1)*((f r)^q*(deriv t r+(n-1:ℕ)*(t r/r))) := hh
        _ = (f r)^q*(r^(n-1)*(deriv t r+(n-1:ℕ)*t r/r)) := by ring
        _ = _ := by rw [he]
    _ = -q*∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r :=
      radial_integration_by_parts hn hR hf hq hfR hta hdt

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma finite_transport_estimate {n : ℕ} {ω p q R D : ℝ} {f g : ℝ → ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hD : 0 < D) (hn : 2 ≤ n) (hω : 0 < ω)
    (hf : LipschitzWith K f) (hg : Continuous g) (hp : 0 < p) (hq : 1 ≤ q)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r, 0 < g r) (hfR : f R = 0)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D)
    (hexp : q+p/(n:ℝ)=p) (hexp2 : 2*(q-1)=p) :
    (n:ℝ)^2*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q)^2 ≤
      q^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*
        (∫ s in (0:ℝ)..D,s^(n-1)*(g s)^p*s^2) := by
  have hn0 : 0 < n := by omega
  let t := radialTransport (f := f) hD.le hn0 hω hg hp (fun r _ => hgp r)
  have ht : Continuous t := radialTransport_continuous _ _ _ hf.continuous hg hp _
  have hz : Continuous (fun r => (f r)^(q-1)*t r) :=
    (hf.continuous.rpow_const (fun _ => Or.inr (sub_nonneg.mpr hq))).mul ht
  have hcs := weighted_interval_cs hR (continuous_id.pow (n-1)) hz hf
    (fun r hr => pow_nonneg hr.1 (n-1))
  have hI : (∫ r in (0:ℝ)..R,r^(n-1)*deriv f r*((f r)^(q-1)*t r)) =
      ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r := by
    apply intervalIntegral.integral_congr
    intro r hr
    ring
  have hM : (∫ r in (0:ℝ)..R,r^(n-1)*((f r)^(q-1)*t r)^2) =
      ∫ s in (0:ℝ)..D,s^(n-1)*(g s)^p*s^2 := by
    rw [radialTransport_integral_moment_unscaled hR hD hn0 hω hf.continuous hg hp hfp
      (fun r _ => hgp r) hmass (fun s => s^2)]
    apply intervalIntegral.integral_congr_Ioo_of_le hR
    intro r hr
    dsimp only
    rw [mul_pow,←Real.rpow_mul_natCast (hfp r hr).le]
    have he : (q-1)*(2:ℝ)=p := by linarith
    rw [Nat.cast_ofNat,he]
    ring
  dsimp only [Pi.pow_apply, id_eq] at hcs
  rw [hI,hM] at hcs
  have hibp := finite_transport_ibp hR hD hn hω hf hg hp hq hfp hgp hfR hmass hexp
  have hJ0 : 0 ≤ (n:ℝ)*(∫ s in (0:ℝ)..D,s^(n-1)*(g s)^q) := by
    apply mul_nonneg (Nat.cast_nonneg n)
    apply intervalIntegral.integral_nonneg hD.le
    intro s hs
    exact mul_nonneg (pow_nonneg hs.1 _) (Real.rpow_nonneg (hgp s).le _)
  have hsq := (sq_le_sq₀ hJ0 (hJ0.trans hibp)).mpr hibp
  have hsq' := mul_le_mul_of_nonneg_left hcs (sq_nonneg q)
  calc
    _ ≤ (-q*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r))^2 := by
      simpa only [mul_pow] using hsq
    _ = q^2*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(q-1)*deriv f r*t r)^2 := by ring
    _ ≤ _ := by simpa only [mul_assoc] using hsq'

end CAT0Fillings.RadialSobolev
end

section

open Real Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma radial_integral_smul (n : ℕ) (p A D : ℝ) (g : ℝ → ℝ)
    (hA : 0 ≤ A) (hg : ∀ r, 0 ≤ g r) :
    (∫ r in (0:ℝ)..D,r^(n-1)*(A*g r)^p) =
      A^p*∫ r in (0:ℝ)..D,r^(n-1)*(g r)^p := by
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [Real.mul_rpow hA (hg r)]
  ring

lemma radial_second_moment_smul (n : ℕ) (p A D : ℝ) (g : ℝ → ℝ)
    (hA : 0 ≤ A) (hg : ∀ r, 0 ≤ g r) :
    (∫ r in (0:ℝ)..D,r^(n-1)*(A*g r)^p*r^2) =
      A^p*∫ r in (0:ℝ)..D,r^(n-1)*(g r)^p*r^2 := by
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [Real.mul_rpow hA (hg r)]
  ring

lemma radial_integral_pos {n : ℕ} {p R : ℝ} {f : ℝ → ℝ}
    (hn : 0 < n) (hp : 0 < p) (hR : 0 < R) (hf : Continuous f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) :
    0 < ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^p := by
  have h := radialCDF_strictMonoOn (ω := 1) hn zero_lt_one hf hp hfp
    (show (0:ℝ) ∈ Icc 0 R from ⟨le_rfl,hR.le⟩) (show R ∈ Icc 0 R from ⟨hR.le,le_rfl⟩) hR
  rw [radialCDF_zero,radialCDF, mul_one] at h
  exact (mul_pos_iff.mp h).resolve_right (by rintro ⟨hneg,_⟩; exact (not_lt_of_ge (Nat.cast_nonneg _)) hneg) |>.2

lemma normalization_power {p F I : ℝ} (hp : 0 < p) (hF : 0 < F) (hI : 0 < I) :
    ((F/I)^(1/p))^p = F/I := by
  rw [←Real.rpow_mul (div_nonneg hF.le hI.le),one_div_mul_cancel hp.ne',Real.rpow_one]

lemma normalize_transport_estimate {n : ℕ} {R D : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hD : 0 < D) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
    let I := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)
    let J := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevQ n)
    let M := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)*r^2
    (n:ℝ)^2*J^2*(F/I)^(2/sobolevP n) ≤
      (sobolevQ n)^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*M := by
  dsimp only
  let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
  let I := ∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)
  let A := (F/I)^(1/sobolevP n)
  have hs := sobolev_exponents hn
  have hF : 0 < F := radial_integral_pos (by omega) hs.1 hR hf.continuous hfp
  have hI : 0 < I := radial_integral_pos (by omega) hs.1 hD (bubble_continuous n) (fun r _ => bubble_pos n r)
  have hA : 0 < A := Real.rpow_pos_of_pos (div_pos hF hI) _
  have hAp : A^(sobolevP n) = F/I := normalization_power hs.1 hF hI
  have hm : radialCDF n 1 f (sobolevP n) R =
      radialCDF n 1 (fun r => A*bubble n r) (sobolevP n) D := by
    rw [radialCDF,radialCDF,radial_integral_smul n _ A D _ hA.le (fun r => (bubble_pos n r).le),hAp]
    change (n:ℝ)*1*F = (n:ℝ)*1*(F/I*I)
    rw [div_mul_cancel₀ _ hI.ne']
  have ht := finite_transport_estimate hR.le hD (by omega) zero_lt_one hf
    ((bubble_continuous n).const_mul A) hs.1 hs.2.1 hfp
    (fun r => mul_pos hA (bubble_pos n r)) hfR hm hs.2.2.1 hs.2.2.2.1
  rw [radial_integral_smul _ _ _ _ _ hA.le (fun r => (bubble_pos n r).le),
    radial_second_moment_smul _ _ _ _ _ hA.le (fun r => (bubble_pos n r).le),mul_pow] at ht
  have he : (A^(sobolevQ n))^2 = A^(sobolevP n)*A^2 := by
    rw [←Real.rpow_mul_natCast hA.le, ←Real.rpow_natCast, ←Real.rpow_add hA]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith [hs.2.2.2.2]
  have heA : A^2 = (F/I)^(2/sobolevP n) := by
    rw [←Real.rpow_mul_natCast (div_nonneg hF.le hI.le)]
    change (F/I)^((1/sobolevP n)*(2:ℝ)) = _
    congr 1
    ring
  rw [he] at ht
  have hout := (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hA (sobolevP n))).mp
    (show A^(sobolevP n)*((n:ℝ)^2*
      (∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevQ n))^2*A^2) ≤
      A^(sobolevP n)*((sobolevQ n)^2*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)*
        (∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)*r^2)) by convert ht using 1 <;> first | rfl | ring)
  rwa [heA] at hout

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Sharp
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma bubble_intervals_tendsto {n : ℕ} (hn : 2 < n) :
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevP n)) atTop (𝓝 (bubbleMass n)) ∧
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevQ n)) atTop (𝓝 (sobolevQ n*bubbleMass n)) ∧
    Tendsto (fun D : ℝ => ∫ r in (0:ℝ)..D, r^(n-1)*(bubble n r)^(sobolevP n)*r^2) atTop
      (𝓝 ((n:ℝ)/(n-2)*bubbleMass n)) := by
  have hi := bubble_moments_integrable hn
  have he := bubble_moments hn
  constructor
  · simpa only [id_eq,he.1] using intervalIntegral_tendsto_integral_Ioi 0 hi.1 tendsto_id
  constructor
  · simpa only [id_eq,he.2.1] using intervalIntegral_tendsto_integral_Ioi 0 hi.2.1 tendsto_id
  · simpa only [id_eq,he.2.2] using intervalIntegral_tendsto_integral_Ioi 0 hi.2.2 tendsto_id

lemma sobolev_power_complement {n : ℕ} (hn : 2 < n) : 1-2/sobolevP n = 2/(n:ℝ) := by
  have h : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (n:ℝ)-2 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  dsimp [sobolevP]
  field_simp
  ring

lemma bubble_normalization_energy {n : ℕ} {F : ℝ} (hn : 2 < n) (hF : 0 < F) :
    bubbleMass n*(F/bubbleMass n)^(2/sobolevP n) =
      (bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) := by
  have hI := bubble_mass_pos hn
  rw [Real.div_rpow hF.le hI.le]
  calc
    _ = ((bubbleMass n)^(1:ℝ)/(bubbleMass n)^(2/sobolevP n))*F^(2/sobolevP n) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_sub hI,sobolev_power_complement hn]

theorem radial_sharp {n : ℕ} {R : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    (n:ℝ)*(n-2)*(bubbleMass n)^(2/(n:ℝ))*
      (∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n))^(2/sobolevP n) ≤
      ∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2 := by
  let F := ∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)
  let E := ∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2
  have hs := sobolev_exponents hn
  have hF : 0 < F := radial_integral_pos (by omega) hs.1 hR hf.continuous hfp
  have hI := bubble_mass_pos hn
  have hi := bubble_intervals_tendsto hn
  have hdiv : Tendsto (fun D : ℝ => F/(∫ r in (0:ℝ)..D,r^(n-1)*(bubble n r)^(sobolevP n)))
      atTop (𝓝 (F/bubbleMass n)) := tendsto_const_nhds.div hi.1 hI.ne'
  have hp : ContinuousAt (fun x : ℝ => x^(2/sobolevP n)) (F/bubbleMass n) :=
    (Real.continuousAt_rpow_const _ _ (Or.inl (div_pos hF hI).ne'))
  have hl := ((hi.2.1.pow 2).const_mul ((n:ℝ)^2)).mul (hp.tendsto.comp hdiv)
  have hr := hi.2.2.const_mul ((sobolevQ n)^2*E)
  have ht := le_of_tendsto_of_tendsto hl hr (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
    exact normalize_transport_estimate hn hR hD hf hfp hfR)
  have hnR : (2:ℝ) < n := by exact_mod_cast hn
  have hq : 0 < sobolevQ n := lt_of_lt_of_le zero_lt_one hs.2.1
  have he : (n:ℝ)*(n-2)*bubbleMass n*(F/bubbleMass n)^(2/sobolevP n) ≤ E := by
    have hfactor : 0 < (sobolevQ n)^2*(n:ℝ)/(n-2)*bubbleMass n := by positivity
    apply (mul_le_mul_iff_right₀ hfactor).mp
    convert ht using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [F,E] <;> field_simp [ne_of_gt (sub_pos.mpr hnR)])
  rw [mul_assoc ((n:ℝ)*(n-2)),bubble_normalization_energy hn hF] at he
  simpa only [mul_assoc] using he

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma omega_pos {n : ℕ} (hn : 0 < n) : 0 < omega n := by
  rw [omega_gamma hn]
  have h : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

lemma sphere_rpow_bubble {n : ℕ} (hn : 2 < n) :
    (sphereArea n)^(2/(n:ℝ)) =
      4*((n:ℝ)*omega n*bubbleMass n)^(2/(n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hω := omega_pos (show 0 < n by omega)
  rw [←bubble_mass_sphere hn, Real.mul_rpow (by positivity)
    (mul_nonneg (mul_nonneg hn0.le hω.le) (bubble_mass_pos hn).le)]
  have he : ((2:ℝ)^n)^(2/(n:ℝ)) = 4 := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hx : (n:ℝ)*(2/(n:ℝ)) = 2 := by field_simp
    rw [hx,Real.rpow_two]
    norm_num
  rw [he]

lemma polar_sharp_coefficient {n : ℕ} {F E : ℝ} (hn : 2 < n) (hF : 0 ≤ F)
    (hE : (n:ℝ)*(n-2)*(bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) ≤ E) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ))*((n:ℝ)*omega n*F)^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*E) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (0:ℝ) < (n:ℝ)-2 := sub_pos.mpr (by exact_mod_cast hn)
  have hω := omega_pos (show 0 < n by omega)
  have hc : 0 < (n:ℝ)*omega n := mul_pos hn0 hω
  have he : 2/(n:ℝ)+2/sobolevP n = 1 := by linarith [sobolev_power_complement hn]
  have hp : ((n:ℝ)*omega n)^(2/(n:ℝ))*((n:ℝ)*omega n)^(2/sobolevP n) = (n:ℝ)*omega n := by
    rw [←Real.rpow_add hc,he,Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 4*((n:ℝ)*omega n)/(n-2) by positivity)
  rw [sphere_rpow_bubble hn,Real.mul_rpow hc.le (bubble_mass_pos hn).le,
    Real.mul_rpow hc.le hF]
  have hh' : 4*(n:ℝ)*((n:ℝ)*omega n)*(bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*E) := by
    convert hh using 1 <;> first | rfl | field_simp [hn2.ne']
  calc
    _ = 4*(n:ℝ)*
        (((n:ℝ)*omega n)^(2/(n:ℝ))*((n:ℝ)*omega n)^(2/sobolevP n))*
        (bubbleMass n)^(2/(n:ℝ))*F^(2/sobolevP n) := by ring
    _ ≤ _ := by rw [hp]; exact hh'

theorem radial_sharp_polar {n : ℕ} {R : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hn : 2 < n) (hR : 0 < R) (hf : LipschitzWith K f)
    (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hfR : f R = 0) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ))*
      ((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^(sobolevP n)))^(2/sobolevP n) ≤
      4/(n-2)*((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(deriv f r)^2)) := by
  exact polar_sharp_coefficient hn
    (radial_integral_pos (by omega) (sobolev_exponents hn).1 hR hf.continuous hfp).le
    (radial_sharp hn hR hf hfp hfR)

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CAT0Fillings
open RadialSobolev

lemma fillingCoefficient_pos {m : ℕ} (hm : 0 < m) : 0 < fillingCoefficient m := by
  unfold fillingCoefficient sphereArea
  have hω := omega_pos (Nat.succ_pos m)
  positivity

lemma ball_filling_identity {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) :
    fillingCoefficient m * (((m+1:ℝ)*omega (m+1)*r^m)^(fillingPower m)) =
      omega (m+1)*r^(m+1) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hω := omega_pos (Nat.succ_pos m)
  have hM : 0 < (m+1:ℝ)*omega (m+1) := by positivity
  have hp : (m+1:ℝ)/(m:ℝ) = 1+1/(m:ℝ) := by field_simp
  have hpow : ((r^m)^((m+1:ℝ)/(m:ℝ))) = r^(m+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    have he : (m:ℝ)*((m+1:ℝ)/(m:ℝ)) = (m+1:ℝ) := by field_simp
    rw [he]
    norm_cast
  rw [fillingCoefficient,fillingPower,Real.mul_rpow hM.le (pow_nonneg hr _),hpow]
  rw [hp,Real.rpow_add hM,Real.rpow_one]
  unfold sphereArea
  field_simp [hM.ne',Real.rpow_ne_zero hM.le hM.ne']

lemma perimeter_of_small_isoperimetry {m : ℕ} (hm : 0 < m) {r P η : ℝ}
    (hr : 0 ≤ r) (hP : 0 ≤ P) (hη : 0 < η) (hη1 : η < 1)
    (hiso : (1-η)*(omega (m+1)*r^(m+1)) ≤
      fillingCoefficient m * P^(fillingPower m)) :
    (1-η)*((m+1:ℝ)*omega (m+1)*r^m) ≤ P := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hp : 1 < fillingPower m := by unfold fillingPower; apply (lt_div_iff₀ hmR).mpr; linarith
  have hc := fillingCoefficient_pos hm
  let B := (m+1:ℝ)*omega (m+1)*r^m
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) (omega_pos (Nat.succ_pos m)).le) (pow_nonneg hr _)
  by_contra hn
  have hlt : P < (1-η)*B := not_le.mp hn
  have hpow := Real.rpow_lt_rpow hP hlt (lt_trans zero_lt_one hp)
  have hmul := mul_lt_mul_of_pos_left hpow hc
  rw [Real.mul_rpow (sub_pos.mpr hη1).le hB] at hmul
  have hsmall : (1-η)^(fillingPower m) ≤ 1-η := Real.rpow_le_self_of_le_one
    (sub_pos.mpr hη1).le (by linarith) hp.le
  have hid := ball_filling_identity hm hr
  change fillingCoefficient m * B^(fillingPower m) = _ at hid
  have hnonneg : 0 ≤ fillingCoefficient m * B^(fillingPower m) := mul_nonneg hc.le (Real.rpow_nonneg hB _)
  have hbd := mul_le_mul_of_nonneg_right hsmall hnonneg
  rw [hid] at hbd
  nlinarith

end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma radialInverse_bdd (R : ℝ → ℝ) (U ρ : ℝ) :
    BddAbove {t | 0 ≤ t ∧ t < U ∧ ρ < R t} := ⟨U,fun _ ht => ht.2.1.le⟩

lemma radialInverse_nonneg (R : ℝ → ℝ) (U ρ : ℝ) : 0 ≤ radialInverse R U ρ :=
  Real.sSup_nonneg (fun _ ht => ht.1)

lemma radialInverse_le (R : ℝ → ℝ) {U : ℝ} (hU : 0 ≤ U) (ρ : ℝ) :
    radialInverse R U ρ ≤ U := by
  apply Real.sSup_le
  · exact fun _ ht => ht.2.1.le
  · exact hU

lemma radialInverse_antitone (R : ℝ → ℝ) (U : ℝ) : Antitone (radialInverse R U) := by
  intro a b hab
  apply Real.sSup_le
  · intro t ht
    apply le_csSup (radialInverse_bdd R U a)
    exact ⟨ht.1,ht.2.1,hab.trans_lt ht.2.2⟩
  · exact radialInverse_nonneg R U a

lemma mem_of_lt_radialInverse {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 ≤ t) (h : t < radialInverse R U ρ) :
    t < U ∧ ρ < R t := by
  have hne : {s | 0 ≤ s ∧ s < U ∧ ρ < R s}.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [radialInverse,he,Real.sSup_empty] at h
    linarith
  obtain ⟨s,hs,hts⟩ := (lt_csSup_iff (radialInverse_bdd R U ρ) hne).mp h
  have htU := hts.trans hs.2.1
  exact ⟨htU,hs.2.2.trans_le (hR ⟨ht,htU.le⟩ ⟨hs.1,hs.2.1.le⟩ hts.le)⟩

lemma radius_le_of_inverse_lt {R : ℝ → ℝ} {U ρ t : ℝ}
    (ht : 0 ≤ t) (htU : t < U) (h : radialInverse R U ρ < t) : R t ≤ ρ := by
  by_contra hn
  have hx : t ≤ radialInverse R U ρ := le_csSup (radialInverse_bdd R U ρ)
    ⟨ht,htU,not_le.mp hn⟩
  linarith

lemma radialInverse_lipschitz {R : ℝ → ℝ} {U c : ℝ}
    (_ : 0 ≤ U) (hc : 0 < c) (hR : AntitoneOn R (Icc 0 U))
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t) :
    LipschitzWith (Real.toNNReal c⁻¹) (radialInverse R U) := by
  have hdiff {a b : ℝ} (hab : a ≤ b) :
      c*(radialInverse R U a-radialInverse R U b) ≤ b-a := by
    by_contra hn
    have hn' : b-a < c*(radialInverse R U a-radialInverse R U b) := not_le.mp hn
    have hgap : radialInverse R U b < radialInverse R U a := by
      by_contra hg
      have := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr (not_lt.mp hg))
      linarith
    let ε := ((radialInverse R U a-radialInverse R U b)-(b-a)/c)/4
    have hε : 0 < ε := by
      dsimp only [ε]
      apply div_pos _ (by norm_num)
      exact sub_pos.mpr ((div_lt_iff₀ hc).mpr (by nlinarith))
    have hεgap : 2*ε < radialInverse R U a-radialInverse R U b := by
      have hba : 0 ≤ (b-a)/c := div_nonneg (sub_nonneg.mpr hab) hc.le
      dsimp only [ε]
      linarith
    let s := radialInverse R U b+ε
    let t := radialInverse R U a-ε
    have hs0 : 0 < s := by
      have := radialInverse_nonneg R U b
      dsimp only [s]; linarith
    have hst : s < t := by dsimp only [s,t]; linarith
    have hta : t < radialInverse R U a := by dsimp only [t]; linarith
    have htU := (mem_of_lt_radialInverse hR (hs0.trans hst).le hta).1
    have hRt := (mem_of_lt_radialInverse hR (hs0.trans hst).le hta).2
    have hRs := radius_le_of_inverse_lt hs0.le (hst.trans htU)
      (show radialInverse R U b < s by dsimp only [s]; linarith)
    have hbound := hD s t hs0 hst htU
    have heq : c*((radialInverse R U a-radialInverse R U b)-4*ε) = b-a := by
      dsimp only [ε]
      field_simp
      ring
    dsimp only [s,t] at hbound
    nlinarith [mul_pos hc hε]
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (radialInverse_antitone R U hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    have := hdiff hab
    have hi : c⁻¹*c = 1 := inv_mul_cancel₀ hc.ne'
    have hm := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc.le)
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (radialInverse_antitone R U hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    have := hdiff hab
    have hi : c⁻¹*c = 1 := inv_mul_cancel₀ hc.ne'
    have hm := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hc.le)
    nlinarith

lemma radialInverse_superlevel {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 ≤ t) (htU : t < U)
    (hcont : ContinuousWithinAt R (Ici t) t) :
    t < radialInverse R U ρ ↔ ρ < R t := by
  constructor
  · exact fun h => (mem_of_lt_radialInverse hR ht h).2
  · intro hρ
    have hright : ContinuousWithinAt R (Ioi t) t :=
      hcont.mono (Ioi_subset_Ici_self)
    have hr : ∀ᶠ s in 𝓝[>] t, ρ < R s :=
      hright (isOpen_Ioi.mem_nhds hρ)
    have hu : ∀ᶠ s in 𝓝[>] t, s < U :=
      (eventually_lt_nhds htU).filter_mono nhdsWithin_le_nhds
    have hall : ∀ᶠ s in 𝓝[>] t, t < s ∧ ρ < R s ∧ s < U := by
      filter_upwards [self_mem_nhdsWithin, hr, hu] with s hs hr hu
      exact ⟨hs,hr,hu⟩
    obtain ⟨s,hs,hsr,hsU⟩ := hall.exists
    exact hs.trans_le (le_csSup (radialInverse_bdd R U ρ) ⟨ht.trans hs.le,hsU,hsr⟩)

lemma radialInverse_zero_outside {R : ℝ → ℝ} {U ρ : ℝ}
    (hU : 0 ≤ U) (hR : AntitoneOn R (Icc 0 U)) (hρ : R 0 ≤ ρ) :
    radialInverse R U ρ = 0 := by
  have he : {t | 0 ≤ t ∧ t < U ∧ ρ < R t} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hh := hR ⟨le_rfl,hU⟩ ⟨ht.1,ht.2.1.le⟩ ht.1
    exact hρ.not_gt (ht.2.2.trans_le hh)
  simp only [radialInverse,he,Real.sSup_empty]

lemma radialInverse_at_zero {R : ℝ → ℝ} {U : ℝ} (hU : 0 < U)
    (hpos : ∀ t ∈ Ico 0 U, 0 < R t) : radialInverse R U 0 = U := by
  apply le_antisymm (radialInverse_le R hU.le 0)
  apply le_of_forall_lt_imp_le_of_dense
  intro a ha
  by_cases ha0 : a < 0
  · exact ha0.le.trans (radialInverse_nonneg R U 0)
  · apply le_csSup (radialInverse_bdd R U 0)
    exact ⟨not_lt.mp ha0,ha,hpos a ⟨not_lt.mp ha0,ha⟩⟩

lemma radialInverse_radius_identity {R : ℝ → ℝ} {U c t : ℝ}
    (hc : 0 < c) (hR : AntitoneOn R (Icc 0 U)) (ht : 0 < t) (htU : t < U)
    (hD : ∀ s v : ℝ, 0 < s → s < v → v < U → c*(v-s) ≤ R s-R v) :
    radialInverse R U (R t) = t := by
  apply le_antisymm
  · apply Real.sSup_le
    · intro s hs
      by_contra hn
      have hh := hR ⟨ht.le,htU.le⟩ ⟨hs.1,hs.2.1.le⟩ (not_le.mp hn).le
      exact (hs.2.2.trans_le hh).false
    · exact ht.le
  · apply le_of_forall_lt_imp_le_of_dense
    intro a hat
    by_cases ha0 : a ≤ 0
    · exact ha0.trans (radialInverse_nonneg R U (R t))
    · have ha : 0 < a := lt_of_not_ge ha0
      have hr : R t < R a := by
        have hh := hD a t ha hat htU
        have hp := mul_pos hc (sub_pos.mpr hat)
        linarith
      exact le_csSup (radialInverse_bdd R U (R t)) ⟨ha.le,hat.trans htU,hr⟩

lemma radialInverse_fiber {R : ℝ → ℝ} {U ρ t : ℝ}
    (hR : AntitoneOn R (Icc 0 U)) (ht : 0 < t) (htU : t < U)
    (hcont : ContinuousAt R t) (heq : radialInverse R U ρ = t) : ρ = R t := by
  apply le_antisymm
  · have hc : Tendsto R (𝓝[<] t) (𝓝 (R t)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hc
    have hz : ∀ᶠ s in 𝓝[<] t, 0 < s :=
      (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hz] with s hs hs0
    exact (mem_of_lt_radialInverse hR hs0.le (by rwa [heq])).2.le
  · by_contra hn
    have h := (radialInverse_superlevel hR ht.le htU hcont.continuousWithinAt).mpr
      (not_le.mp hn)
    rw [heq] at h
    exact lt_irrefl t h

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Substitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma lipschitz_real_image_null {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s : Set ℝ} (hs : volume s = 0) : volume (f '' s) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num) s
  rw [MeasureTheory.hausdorffMeasure_real,hs,mul_zero] at h
  exact le_antisymm h zero_le

lemma lipschitz_real_image_ae_subset {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s t : Set ℝ} (hts : t ⊆ s) (hst : s =ᵐ[volume] t) :
    f '' s =ᵐ[volume] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : f '' s \ f '' t ⊆ f '' (s \ t) := by
      rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,fun h => hy ⟨x,h,rfl⟩⟩,rfl⟩
    exact measure_mono_null hsub (lipschitz_real_image_null hf (ae_eq_set.mp hst).1)
  · rw [sdiff_eq_empty.mpr (image_mono hts),measure_empty]

lemma lintegral_image_antitone_lipschitz {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {s : Set ℝ} (hs : MeasurableSet s)
    (hanti : AntitoneOn h s) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in h '' s, g t = ∫⁻ r in s, ENNReal.ofReal (-deriv h r)*g (h r) := by
  let D : Set ℝ := {r | r ∈ s ∧ DifferentiableAt ℝ h r}
  have hD : D =ᵐ[volume] s := by
    filter_upwards [hh.ae_differentiableAt (μ := volume)] with r hr
    change (r ∈ s ∧ DifferentiableAt ℝ h r) = (r ∈ s)
    exact propext ⟨And.left,fun hm => ⟨hm,hr⟩⟩
  obtain ⟨d,hds,hdm,hde⟩ :=
    (hs.nullMeasurableSet.congr hD.symm).exists_measurable_subset_ae_eq
  have hsub : d ⊆ s := fun r hr => (hds hr).1
  have hder : ∀ r ∈ d, HasDerivWithinAt h (deriv h r) d r :=
    fun r hr => (hds hr).2.hasDerivAt.hasDerivWithinAt
  have heq : d =ᵐ[volume] s := hde.trans hD
  calc
    _ = ∫⁻ t in h '' d, g t :=
      setLIntegral_congr (lipschitz_real_image_ae_subset hh hsub heq.symm)
    _ = ∫⁻ r in d, ENNReal.ofReal (-deriv h r)*g (h r) :=
      lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hdm hder (hanti.mono hsub) g
    _ = _ := setLIntegral_congr heq

lemma lintegral_antitone_interval {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {a b : ℝ} (hab : a ≤ b)
    (hanti : AntitoneOn h (Icc a b)) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Icc (h b) (h a), g t =
      ∫⁻ r in Icc a b, ENNReal.ofReal (-deriv h r)*g (h r) := by
  rw [←hh.continuous.continuousOn.image_Icc_of_antitoneOn hab hanti]
  exact lintegral_image_antitone_lipschitz hh measurableSet_Icc hanti g

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma ae_inverse_derivative {R : ℝ → ℝ} {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c) (hR : Antitone R)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      HasDerivAt R (deriv R t) t ∧
      HasDerivAt (radialInverse R U) (deriv R t)⁻¹ (R t) ∧ deriv R t ≠ 0 := by
  let h := radialInverse R U
  have hh := radialInverse_lipschitz hU hc (hR.antitoneOn _) hD
  let N : Set ℝ := {r | ¬ DifferentiableAt ℝ h r}
  have hN : volume N = 0 := by
    exact (ae_iff.mp (hh.ae_differentiableAt (μ := volume)))
  have hI : volume (h '' N) = 0 := lipschitz_real_image_null hh hN
  have ha : ∀ᵐ t ∂volume, t ∉ h '' N := by
    simpa only [ae_iff,not_not,mem_ofPred_eq, ofPred_mem_eq] using hI
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae hR.neg.ae_differentiableAt,
    (ae_restrict_mem measurableSet_Ioo : ∀ᵐ t ∂volume.restrict (Ioo 0 U), t ∈ Ioo 0 U)]
      with t ht hRt htI
  have hRt : DifferentiableAt ℝ R t := by simpa using hRt.neg
  have he : h (R t) = t := radialInverse_radius_identity hc (hR.antitoneOn _) htI.1 htI.2 hD
  have hht : DifferentiableAt ℝ h (R t) := by
    by_contra hn
    exact ht ⟨R t,hn,he⟩
  have hid : (fun s : ℝ => s) =ᶠ[𝓝 t] (fun s => h (R s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
    exact (radialInverse_radius_identity hc (hR.antitoneOn _) hs.1 hs.2 hD).symm
  have hcomp := hht.hasDerivAt.comp t hRt.hasDerivAt
  have hone : deriv h (R t)*deriv R t = 1 :=
    (hcomp.congr_of_eventuallyEq hid).unique (hasDerivAt_id t)
  have hn : deriv R t ≠ 0 := by intro hn; simp [hn] at hone
  have hform : deriv h (R t) = (deriv R t)⁻¹ := by
    apply (mul_left_inj' hn).mp
    rw [hone,inv_mul_cancel₀ hn]
  exact ⟨hRt.hasDerivAt,by rw [←hform]; exact hht.hasDerivAt,hn⟩

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma map_antitone_derivative_measure {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {a b : ℝ} (hab : a ≤ b)
    (ha : AntitoneOn h (Icc a b)) :
    ((volume.restrict (Icc a b)).withDensity (fun r => ENNReal.ofReal (-deriv h r))).map h =
      volume.restrict (Icc (h b) (h a)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hh.continuous.measurable]
  have hd : Measurable (fun r : ℝ => ENNReal.ofReal (-deriv h r)) :=
    (measurable_deriv h).neg.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul (volume.restrict (Icc a b)) hd
    (show Measurable (fun r => g (h r)) from hg.comp hh.continuous.measurable)]
  exact (lintegral_antitone_interval hh hab ha g).symm

lemma inverse_energy_identity {R : ℝ → ℝ} {U c : ℝ}
    (hU : 0 < U) (hc : 0 < c) (hR : Antitone R)
    (hpos : ∀ t ∈ Ico 0 U, 0 < R t)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ r in Icc 0 (R 0), w r * (ENNReal.ofReal (-deriv (radialInverse R U) r))^2 =
      ∫⁻ t in Icc 0 U, w (R t) / ENNReal.ofReal (-deriv R t) := by
  let h := radialInverse R U
  let v := fun r => ENNReal.ofReal (-deriv h r)
  let ν := (volume.restrict (Icc 0 (R 0))).withDensity v
  have hh : LipschitzWith (c⁻¹).toNNReal h :=
    radialInverse_lipschitz hU.le hc (hR.antitoneOn _) hD
  have hvm : Measurable v := (measurable_deriv h).neg.ennreal_ofReal
  have hB : 0 ≤ R 0 := (hpos 0 ⟨le_rfl,hU⟩).le
  have h0 : h 0 = U := radialInverse_at_zero hU hpos
  have hB0 : h (R 0) = 0 := radialInverse_zero_outside hU.le (hR.antitoneOn _) le_rfl
  have hmap : ν.map h = volume.restrict (Icc 0 U) := by
    have he := map_antitone_derivative_measure hh hB
      ((radialInverse_antitone R U).antitoneOn _)
    rwa [h0,hB0] at he
  have hgood : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      t ∈ Ioo 0 U ∧ HasDerivAt R (deriv R t) t ∧
      HasDerivAt h (deriv R t)⁻¹ (R t) ∧ deriv R t ≠ 0 := by
    have he : volume.restrict (Icc 0 U) = volume.restrict (Ioo 0 U) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    rw [he]
    filter_upwards [ae_inverse_derivative hU.le hc hR hD,
      ae_restrict_mem measurableSet_Ioo] with t ht hm
    exact ⟨hm,ht⟩
  have hpull : ∀ᵐ r ∂ν,
      h r ∈ Ioo 0 U ∧ HasDerivAt R (deriv R (h r)) (h r) ∧
      HasDerivAt h (deriv R (h r))⁻¹ (R (h r)) ∧ deriv R (h r) ≠ 0 := by
    have hg' := hgood
    rw [←hmap] at hg'
    exact ae_of_ae_map hh.continuous.measurable.aemeasurable hg'
  let g := fun t => w (R t) / ENNReal.ofReal (-deriv R t)
  have hgm : Measurable g := (hw.comp hR.measurable).div (measurable_deriv R).neg.ennreal_ofReal
  have heq : (fun r => w r*v r) =ᵐ[ν] (fun r => g (h r)) := by
    filter_upwards [hpull] with r hr
    have hfiber : r = R (h r) := radialInverse_fiber (hR.antitoneOn _)
      hr.1.1 hr.1.2 hr.2.1.continuousAt rfl
    have hd : deriv h r = (deriv R (h r))⁻¹ := by
      calc
        deriv h r = deriv h (R (h r)) := congrArg (deriv h) hfiber
        _ = _ := hr.2.2.1.deriv
    have hdneg : 0 < -deriv R (h r) :=
      neg_pos.mpr (lt_of_le_of_ne hR.deriv_nonpos hr.2.2.2)
    dsimp [g,v]
    rw [hd,←inv_neg,ENNReal.ofReal_inv_of_pos hdneg,div_eq_mul_inv]
    exact congrArg (fun z => w z * (ENNReal.ofReal (-deriv R (h r)))⁻¹) hfiber
  calc
    _ = ∫⁻ r, w r*v r ∂ν := by
      change _ = ∫⁻ r, w r*v r ∂(volume.restrict (Icc 0 (R 0))).withDensity v
      rw [lintegral_withDensity_eq_lintegral_mul _ hvm (show Measurable (fun r => w r*v r) from hw.mul hvm)]
      apply lintegral_congr
      intro r
      dsimp [v]
      ring
    _ = ∫⁻ r, g (h r) ∂ν := lintegral_congr_ae heq
    _ = ∫⁻ t, g t ∂ν.map h := (lintegral_map hgm hh.continuous.measurable).symm
    _ = _ := by rw [hmap]

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma coarea_ratio_bound {A d P l z β : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hβ : 0 < β)
    (hP : β*A ≤ P) (hQ : P^2 ≤ l*z) (hlam : A*d = l) :
    A/d ≤ (β⁻¹)^2*z := by
  have hAP : (β*A)^2 ≤ P^2 := sq_le_sq₀ (mul_pos hβ hA).le
    ((mul_pos hβ hA).le.trans hP) |>.mpr hP
  have h2 : β^2*A ≤ d*z := by
    apply (mul_le_mul_iff_left₀ hA).mp
    rw [←hlam] at hQ
    nlinarith only [hAP,hQ]
  have hratio : A/d ≤ z/(β^2) := (div_le_div_iff₀ hd (sq_pos_of_pos hβ)).mpr
    (by nlinarith only [h2])
  convert hratio using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem rearranged_profile_energy_bound (μ ζ : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ζ] {ω : ℝ} {n : ℕ} (hω : 0 < ω) (hn : 0 < n)
    {U K η : ℝ} (hU : 0 < U) (hK : 0 < K) (hη : η < 1)
    {P : ℝ → ℝ}
    (hpos : ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t))
    (hco : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal ∧
      P t^2 ≤ (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal) :
    let R := radiusDistribution μ ω n
    let h := radialInverse R U
    ∫⁻ r in Icc 0 (R 0), ENNReal.ofReal ((n:ℝ)*ω*r^(n-1)) *
      (ENNReal.ofReal (-deriv h r))^2 ≤
      ENNReal.ofReal (((1-η)⁻¹)^2)*ζ univ := by
  dsimp only
  let R := radiusDistribution μ ω n
  have hc : 0 < (1-η)/K := div_pos (sub_pos.mpr hη) hK
  have hD := radius_secant_from_coarea μ hω hn hK
    (fun t ht => hpos t ⟨ht.1.le,ht.2⟩) (hco.mono fun _ h => ⟨h.1,h.2.1⟩)
  have hRpos : ∀ t ∈ Ico 0 U, 0 < R t := fun t ht => radius_pos μ hω (hpos t ht)
  have he := inverse_energy_identity hU hc (radius_antitone μ hω.le)
    hRpos hD (fun r => ENNReal.ofReal ((n:ℝ)*ω*r^(n-1))) (by fun_prop)
  rw [he]
  have hpt : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      ENNReal.ofReal ((n:ℝ)*ω*R t^(n-1)) / ENNReal.ofReal (-deriv R t) ≤
        ENNReal.ofReal (((1-η)⁻¹)^2)*ζ.rnDeriv volume t := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hco,ae_restrict_of_ae (ae_radius_derivative μ hω hn),
      ae_inverse_derivative hU.le hc (radius_antitone μ hω.le) hD,
      ae_restrict_mem measurableSet_Ioo] with t hp hd hi ht
    have hA : 0 < (n:ℝ)*ω*R t^(n-1) :=
      mul_pos (mul_pos (by exact_mod_cast hn) hω) (pow_pos (hRpos t ⟨ht.1.le,ht.2⟩) _)
    have hdpos : 0 < -deriv R t := neg_pos.mpr
      (lt_of_le_of_ne (radius_antitone μ hω.le).deriv_nonpos hi.2.2)
    have hlam : ((n:ℝ)*ω*R t^(n-1))*(-deriv R t) = (μ.rnDeriv volume t).toReal := by
      have hc := hd.2
      change (n:ℝ)*ω*R t^(n-1)*deriv R t = _ at hc
      linarith
    have hr := coarea_ratio_bound hA hdpos (sub_pos.mpr hη) hp.1 hp.2.2 hlam
    calc
      _ = ENNReal.ofReal (((n:ℝ)*ω*R t^(n-1))/(-deriv R t)) :=
        (ENNReal.ofReal_div_of_pos hdpos).symm
      _ ≤ ENNReal.ofReal ((((1-η)⁻¹)^2)*(ζ.rnDeriv volume t).toReal) :=
        ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal (((1-η)⁻¹)^2)*ENNReal.ofReal (ζ.rnDeriv volume t).toReal :=
        ENNReal.ofReal_mul (sq_nonneg _)
      _ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le
  calc
    _ ≤ ∫⁻ t in Icc 0 U, ENNReal.ofReal (((1-η)⁻¹)^2)*ζ.rnDeriv volume t :=
      lintegral_mono_ae hpt
    _ = ENNReal.ofReal (((1-η)⁻¹)^2)*∫⁻ t in Icc 0 U, ζ.rnDeriv volume t := by
      rw [lintegral_const_mul _ (ζ.measurable_rnDeriv volume)]
    _ ≤ _ := by
      gcongr
      exact (Measure.setLIntegral_rnDeriv_le (μ := ζ) (ν := volume) (Icc 0 U)).trans (measure_mono (subset_univ _))

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Euclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement

lemma lintegral_fun_norm_addHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f ‖x‖ ∂μ =
      (Module.finrank ℝ E : ℝ≥0∞)*μ (ball 0 1) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Module.finrank ℝ E-1))*f r := by
  let H := homeomorphUnitSphereProd E
  have hφ : Measurable (fun p : sphere (0:E) 1 × Ioi (0:ℝ) => f (p.2:ℝ)) :=
    hf.comp (measurable_subtype_coe.comp measurable_snd)
  calc
    _ = ∫⁻ x : ({(0:E)}ᶜ : Set E), f ‖x.1‖ ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x : E => f ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ p : sphere (0:E) 1 × Ioi (0:ℝ), f (p.2:ℝ)
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
      rw [←μ.measurePreserving_homeomorphUnitSphereProd.map_eq,
        lintegral_map hφ H.continuous.measurable]
      simp only [H,homeomorphUnitSphereProd_apply_snd_coe]
    _ = μ.toSphere univ * ∫⁻ r : Ioi (0:ℝ), f r
        ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) := by
      rw [lintegral_prod _ hφ.aemeasurable]
      simp only [lintegral_const]
      rw [mul_comm]
    _ = _ := by
      rw [μ.toSphere_apply_univ,Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^(Module.finrank ℝ E-1))) by fun_prop)
          (show Measurable (fun r : Ioi (0:ℝ) => f r) from hf.comp measurable_subtype_coe)]
      congr 1
      exact lintegral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r^(Module.finrank ℝ E-1))*f r)

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (ν : Measure E) [ν.IsAddHaarMeasure]

lemma unitBall_real_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (ν : Measure E) [ν.IsAddHaarMeasure] : 0 < ν.real (ball (0:E) 1) := by
  exact ENNReal.toReal_pos_iff.mpr ⟨measure_ball_pos ν 0 (by norm_num), measure_ball_lt_top⟩

lemma rearrangement_lipschitz (μ : Measure ℝ) [IsFiniteMeasure μ] {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U →
      c*(t-s) ≤ radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) s -
        radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t) :
    LipschitzWith (Real.toNNReal c⁻¹) (euclideanRearrangement ν μ U) := by
  have hh := radialInverse_lipschitz hU hc
    ((radius_antitone μ (unitBall_real_pos ν).le).antitoneOn _) hD
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hh.dist_le_mul ‖x‖ ‖y‖).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using dist_norm_norm_le x y) (NNReal.coe_nonneg _))

lemma rearrangement_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    (ν : Measure E) [ν.IsAddHaarMeasure] (μ : Measure ℝ) (U : ℝ) (x : E) :
    0 ≤ euclideanRearrangement ν μ U x := radialInverse_nonneg _ _ _

lemma rearrangement_superlevel (μ : Measure ℝ) [IsFiniteMeasure μ] {U t : ℝ}
    (ht : 0 ≤ t) (htU : t < U) :
    {x : E | t < euclideanRearrangement ν μ U x} =
      ball 0 (radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t) := by
  have hn := Module.finrank_pos (R := ℝ) (M := E)
  ext x
  simpa only [mem_ofPred_eq,mem_ball,dist_zero_right,euclideanRearrangement] using
    radialInverse_superlevel ((radius_antitone μ (unitBall_real_pos ν).le).antitoneOn _) ht htU
      (radius_right_continuous μ (unitBall_real_pos ν) hn t)

lemma rearrangement_superlevel_mass (μ : Measure ℝ) [IsFiniteMeasure μ] {U : ℝ}
    (hU : 0 ≤ U) (hupper : μ (Ioi U) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ν {x | t < euclideanRearrangement ν μ U x} = μ (Ioi t) := by
  by_cases htU : t < U
  · rw [rearrangement_superlevel ν μ ht htU]
    have hω := unitBall_real_pos ν
    have hn := Module.finrank_pos (R := ℝ) (M := E)
    rw [ν.addHaar_ball _ (radius_nonneg μ hω.le t)]
    rw [←ofReal_measureReal (measure_ball_lt_top.ne),
      ←ENNReal.ofReal_mul (pow_nonneg (radius_nonneg μ hω.le t) _),mul_comm,
      radius_pow μ hω hn,ofReal_measureReal (measure_ne_top _ _)]
  · have he : {x | t < euclideanRearrangement ν μ U x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt.mp htU).not_gt (hx.trans_le (radialInverse_le _ hU _))
    rw [he,measure_empty]
    exact (measure_mono_null (Ioi_subset_Ioi (not_lt.mp htU)) hupper).symm

theorem rearrangement_moments (μ : Measure ℝ) [IsFiniteMeasure μ] {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c) (hupper : μ (Ioi U) = 0)
    (hnegative : ∀ᵐ t ∂μ, 0 ≤ t)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U →
      c*(t-s) ≤ radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) s -
        radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t)
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal ((euclideanRearrangement ν μ U x)^q) ∂ν =
      ∫⁻ t, ENNReal.ofReal (t^q) ∂μ := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (Eventually.of_forall (rearrangement_nonneg ν μ U))
    (rearrangement_lipschitz ν μ hU hc hD).continuous.measurable.aemeasurable hq,
    lintegral_rpow_eq_lintegral_meas_lt_mul μ hnegative measurable_id.aemeasurable hq]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [rearrangement_superlevel_mass ν μ hU hupper ht.le]
  rfl

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Sobolev
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement

lemma weighted_deriv_sq_integrable {f w : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzWith K f) (hw : Continuous w) (hw0 : ∀ r ∈ Icc a b, 0 ≤ w r) :
    IntegrableOn (fun r => w r*(deriv f r)^2) (Icc a b) := by
  have h := RadialSobolev.continuous_mul_deriv_memLp_Icc hw.sqrt hf a b 2
  have hi := h.integrable_mul h
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  dsimp only [Pi.mul_apply]
  calc
    _ = (Real.sqrt (w r))^2*(deriv f r)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (hw0 r hr)]

lemma inverse_profile_energy_real {R : ℝ → ℝ} {U C : ℝ} {n : ℕ} {K : ℝ≥0}
    (hR0 : 0 ≤ R 0) (hC : 0 ≤ C) (hf : LipschitzWith K (radialInverse R U)) :
    ENNReal.ofReal (C*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv (radialInverse R U) r)^2)) =
      ∫⁻ r in Icc 0 (R 0), ENNReal.ofReal (C*r^(n-1))*
        (ENNReal.ofReal (-deriv (radialInverse R U) r))^2 := by
  have hi := weighted_deriv_sq_integrable hf (show Continuous (fun r : ℝ => r^(n-1)) by fun_prop)
    (fun r (hr : r ∈ Icc 0 (R 0)) => pow_nonneg hr.1 _)
  rw [intervalIntegral.integral_of_le hR0,←integral_Icc_eq_integral_Ioc,←integral_const_mul]
  rw [ofReal_integral_eq_lintegral_ofReal (hi.const_mul C) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_nonneg hC (mul_nonneg (pow_nonneg hr.1 _) (sq_nonneg _)))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hd : 0 ≤ -deriv (radialInverse R U) r := neg_nonneg.mpr (radialInverse_antitone R U).deriv_nonpos
  rw [←ENNReal.ofReal_pow hd,←ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hr.1 _))]
  congr 1
  ring

lemma radial_moment_finite_interval {f : ℝ → ℝ} {R q : ℝ} {n : ℕ}
    (hR : 0 ≤ R) (hq : 0 < q) (hf : Continuous f) (hf0 : ∀ r, 0 ≤ f r)
    (hz : ∀ r, R ≤ r → f r = 0) :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(n-1))*ENNReal.ofReal ((f r)^q) =
      ENNReal.ofReal (∫ r in (0:ℝ)..R,r^(n-1)*(f r)^q) := by
  have hc : Continuous (fun r => r^(n-1)*(f r)^q) :=
    (continuous_id.pow _).mul (hf.rpow_const (fun _ => Or.inr hq.le))
  have he : ∫⁻ r in Ioi R, ENNReal.ofReal (r^(n-1))*ENNReal.ofReal ((f r)^q) = 0 := by
    apply (lintegral_congr_ae _).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp [hz r hr.le,Real.zero_rpow hq.ne']
  rw [←Ioc_union_Ioi_eq_Ioi hR,lintegral_union measurableSet_Ioi
    (disjoint_left.mpr (fun r hr ht => (not_le_of_gt ht) hr.2)),he,add_zero,
    restrict_Ioc_eq_restrict_Icc]
  rw [intervalIntegral.integral_of_le hR,←integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact mul_nonneg (pow_nonneg hr.1 _) (Real.rpow_nonneg (hf0 r) _))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact (ENNReal.ofReal_mul (pow_nonneg hr.1 _)).symm

lemma euclidean_radial_moment {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ} {R q : ℝ}
    (hR : 0 ≤ R) (hq : 0 < q) (hf : Continuous f) (hf0 : ∀ r, 0 ≤ f r)
    (hz : ∀ r, R ≤ r → f r = 0) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((f ‖x‖)^q) =
      ENNReal.ofReal ((n:ℝ)*omega n*(∫ r in (0:ℝ)..R,r^(n-1)*(f r)^q)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hp := lintegral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun r => ENNReal.ofReal ((f r)^q))
    ((hf.rpow_const (fun _ => Or.inr hq.le)).measurable.ennreal_ofReal)
  simp only [finrank_euclideanSpace_fin] at hp
  rw [hp,radial_moment_finite_interval hR hq hf hf0 hz]
  unfold omega
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  congr 2
  exact (ofReal_measureReal (measure_ball_lt_top.ne)).symm

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement
open RadialSobolev

theorem rearranged_sobolev (μ ζ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ζ]
    {n : ℕ} (hn : 2 < n) {U K η : ℝ} (hU : 0 < U) (hK : 0 < K) (hη : η < 1)
    (hpos : ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t))
    (hupper : μ (Ioi U) = 0) (hnegative : ∀ᵐ t ∂μ, 0 ≤ t) {P : ℝ → ℝ}
    (hco : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*omega n*(radiusDistribution μ (omega n) n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal ∧
      P t^2 ≤ (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal) :
    (n:ℝ)*(sphereArea n)^(2/(n:ℝ)) *
      ((∫⁻ t, ENNReal.ofReal (t^(sobolevP n)) ∂μ).toReal)^(2/sobolevP n) ≤
      4/(n-2)*((1-η)⁻¹)^2*ζ.real univ := by
  have hn0 : 0 < n := by omega
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hω := omega_pos hn0
  let R := radiusDistribution μ (omega n) n
  let f := radialInverse R U
  have hc : 0 < (1-η)/K := div_pos (sub_pos.mpr hη) hK
  have hD := radius_secant_from_coarea μ hω hn0 hK
    (fun t ht => hpos t ⟨ht.1.le,ht.2⟩) (hco.mono fun _ h => ⟨h.1,h.2.1⟩)
  have hR := (radius_antitone μ (n := n) hω.le).antitoneOn (Icc 0 U)
  have hf := radialInverse_lipschitz hU.le hc hR hD
  have hR0 : 0 < R 0 := radius_pos μ hω (hpos 0 ⟨le_rfl,hU⟩)
  have hfpos : ∀ r ∈ Ioo 0 (R 0), 0 < f r := by
    intro r hr
    exact (radialInverse_superlevel hR le_rfl hU
      (radius_right_continuous μ hω hn0 0)).mpr hr.2
  have hfzero : ∀ r, R 0 ≤ r → f r = 0 := fun r hr => radialInverse_zero_outside hU.le hR hr
  have hsharp := radial_sharp_polar hn hR0 hf hfpos (hfzero _ le_rfl)
  have hmoment := rearrangement_moments (volume : Measure (EuclideanSpace ℝ (Fin n))) μ hU.le hc
    hupper hnegative (by simpa only [finrank_euclideanSpace_fin, omega, measureReal_def] using hD)
    (sobolev_exponents hn).1
  simp only [euclideanRearrangement, finrank_euclideanSpace_fin] at hmoment
  change ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((f ‖x‖)^(sobolevP n)) = _ at hmoment
  rw [euclidean_radial_moment hn0 hR0.le (sobolev_exponents hn).1 hf.continuous
    (radialInverse_nonneg R U) hfzero] at hmoment
  have hF := (radial_integral_pos hn0 (sobolev_exponents hn).1 hR0 hf.continuous hfpos).le
  have hmomentR := congrArg ENNReal.toReal hmoment
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hω.le) hF)] at hmomentR
  rw [←hmomentR]
  have henergy := rearranged_profile_energy_bound μ ζ hω hn0 hU hK hη hpos hco
  dsimp only at henergy
  rw [←inverse_profile_energy_real (n := n) (C := (n:ℝ)*omega n) hR0.le
    (mul_nonneg (Nat.cast_nonneg n) hω.le) hf] at henergy
  have hEnonneg : 0 ≤ (n:ℝ)*omega n*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv f r)^2) := by
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hω.le)
    apply intervalIntegral.integral_nonneg hR0.le
    intro r hr
    exact mul_nonneg (pow_nonneg hr.1 _) (sq_nonneg _)
  have henergyR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ζ univ)) henergy
  rw [ENNReal.toReal_ofReal hEnonneg,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)] at henergyR
  calc
    _ ≤ 4/(n-2)*((n:ℝ)*omega n*(∫ r in (0:ℝ)..R 0,r^(n-1)*(deriv f r)^2)) := hsharp
    _ ≤ _ := by
      simp only [measureReal_def]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergyR (show 0 ≤ 4/((n:ℝ)-2) by
        have : (2:ℝ) < n := by exact_mod_cast hn
        positivity)

end CAT0Fillings.Rearrangement
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_SmallSupport
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

namespace CAT0Fillings.Rearrangement

lemma positive_tail_right (μ : Measure ℝ) [IsFiniteMeasure μ] {t : ℝ}
    (ht : 0 < μ.real (Ioi t)) : ∃ s : ℝ, t < s ∧ 0 < μ.real (Ioi s) := by
  have h := (negativeTail μ).right_continuous' t
  have hc : ContinuousWithinAt (fun s => μ.real (Ioi s)) (Ici t) t := by
    have h := h.neg
    change ContinuousWithinAt (fun s => - -μ.real (Ioi s)) (Ici t) t at h
    simpa only [neg_neg] using h
  have hp : ∀ᶠ s in 𝓝[>] t, 0 < μ.real (Ioi s) :=
    (hc.mono Ioi_subset_Ici_self) (isOpen_Ioi.mem_nhds ht)
  have he : ∀ᶠ s in 𝓝[>] t, t < s ∧ 0 < μ.real (Ioi s) := by
    filter_upwards [self_mem_nhdsWithin,hp] with s hs hp
    exact ⟨hs,hp⟩
  exact he.exists

theorem exists_essential_top (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ}
    (hB : μ (Ioi B) = 0) (hzero : 0 < μ.real (Ioi 0)) :
    ∃ U : ℝ, 0 < U ∧ μ (Ioi U) = 0 ∧ ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t) := by
  let S := {t : ℝ | 0 < μ.real (Ioi t)}
  have hS : S.Nonempty := ⟨0,hzero⟩
  have hbd : BddAbove S := by
    refine ⟨B,fun t ht => ?_⟩
    by_contra hn
    have he := measure_mono_null (Ioi_subset_Ioi (not_le.mp hn).le) hB
    have : μ.real (Ioi t) = 0 := by rw [measureReal_def,he,ENNReal.toReal_zero]
    exact ht.ne' this
  let U := sSup S
  have hU : 0 < U := by
    obtain ⟨t,ht,htp⟩ := positive_tail_right μ hzero
    exact ht.trans_le (le_csSup hbd htp)
  have hupper : μ (Ioi U) = 0 := by
    by_contra hm
    have hu : 0 < μ.real (Ioi U) := ENNReal.toReal_pos_iff.mpr
      ⟨pos_iff_ne_zero.mpr hm,measure_lt_top _ _⟩
    obtain ⟨t,ht,htp⟩ := positive_tail_right μ hu
    exact ht.not_ge (le_csSup hbd htp)
  refine ⟨U,hU,hupper,fun t ht => ?_⟩
  obtain ⟨s,hs,hst⟩ := exists_lt_of_lt_csSup hS ht.2
  exact hs.trans_le (measureReal_mono (Ioi_subset_Ioi hst.le))

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open BorelRestriction MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem small_support_sobolev {k : ℕ} (hk : 0 < k)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hX : IsCAT0 X) (q : ChartGeometry hT.1)
    {δ η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hiso : ∀ E : Set X, MeasurableSet E →
      IsIntegral (k+2) (restrictCurrent hT.1 E) → mass (restrictCurrent hT.1 E) ≤ δ →
      (1-η)*mass (restrictCurrent hT.1 E) ≤
        fillingCoefficient (k+1)*(mass (boundarySucc (restrictCurrent hT.1 E)))^(fillingPower (k+1)))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hu0 : ∀ x, 0 ≤ u x)
    (hsupp : (currentMassMeasure hT.1).real {x | 0 < u x} ≤ δ) :
    (k+2:ℝ)*(sphereArea (k+2))^(2/(k+2:ℝ)) *
      ((∫⁻ x, ENNReal.ofReal ((u x)^(sobolevP (k+2))) ∂currentMassMeasure hT.1).toReal)^(2/sobolevP (k+2)) ≤
      4/((k+2:ℝ)-2)*((1-η)⁻¹)^2*(q.energyMeasure u).real univ := by
  let μ := (currentMassMeasure hT.1).map u
  let ζ := (q.energyMeasure u).map u
  let := q.energyMeasure_finite hu
  have hμfin : IsFiniteMeasure μ := inferInstance
  have hζfin : IsFiniteMeasure ζ := inferInstance
  have hn : 2 < k+2 := by omega
  have hp := (sobolev_exponents hn).1
  have hneg : ∀ᵐ t ∂μ, 0 ≤ t := by
    exact (ae_map_iff hu.continuous.measurable.aemeasurable (by measurability)).mpr
      (Eventually.of_forall hu0)
  have htail (t : ℝ) : μ.real (Ioi t) = mass (restrictCurrent hT.1 {x | t < u x}) := by
    rw [restriction_mass hT.1 (measurableSet_lt measurable_const hu.continuous.measurable)]
    simp only [μ,measureReal_def,Measure.map_apply hu.continuous.measurable measurableSet_Ioi]
    rfl
  have hmoment : (∫⁻ t, ENNReal.ofReal (t^(sobolevP (k+2))) ∂μ) =
      ∫⁻ x, ENNReal.ofReal ((u x)^(sobolevP (k+2))) ∂currentMassMeasure hT.1 := by
    exact lintegral_map (by fun_prop) hu.continuous.measurable
  have hζ : ζ.real univ = (q.energyMeasure u).real univ := by
    simp only [ζ,measureReal_def,Measure.map_apply hu.continuous.measurable MeasurableSet.univ,preimage_univ]
  by_cases hzero : μ (Ioi 0) = 0
  · have hzv : ∀ᵐ t ∂μ, t = 0 := by
      have hh : ∀ᵐ t ∂μ, t ∉ Ioi (0:ℝ) := (ae_iff.mpr (by simpa only [not_not,ofPred_mem_eq] using hzero))
      filter_upwards [hneg,hh] with t ht hh
      exact le_antisymm (le_of_not_gt hh) ht
    have hmom : (∫⁻ t, ENNReal.ofReal (t^(sobolevP (k+2))) ∂μ) = 0 := by
      calc
        _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hzv.mono fun t ht => by
          rw [ht,Real.zero_rpow hp.ne',ENNReal.ofReal_zero])
        _ = 0 := lintegral_zero
    rw [←hmoment,hmom,ENNReal.toReal_zero,Real.zero_rpow (div_pos (by norm_num) hp).ne',mul_zero]
    have hm : 0 ≤ (q.energyMeasure u).real univ := measureReal_nonneg
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (sq_nonneg _)) measureReal_nonneg
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuous.continuousOn
  have hbd : μ (Ioi B) = 0 := by
    rw [Measure.map_apply hu.continuous.measurable measurableSet_Ioi]
    have he : u ⁻¹' Ioi B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hB x (mem_univ x))).not_gt hx
    rw [he,measure_empty]
  obtain ⟨U,hU,hupper,hpos⟩ := exists_essential_top μ hbd
    (ENNReal.toReal_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hzero,measure_lt_top _ _⟩)
  have hco := q.ae_intrinsic_coarea hT hz hX hu
  have hco' : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((k+2:ℝ)*omega (k+2)*(radiusDistribution μ (omega (k+2)) (k+2) t)^(k+2-1)) ≤
        mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ∧
      mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ≤
        ((K:ℝ)+1)*(μ.rnDeriv volume t).toReal ∧
      mass (boundarySucc (restrictCurrent hT.1 {x | t < u x}))^2 ≤
        (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal := by
    filter_upwards [hco.filter_mono ae_restrict_le,ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
    have hsmall : mass (restrictCurrent hT.1 {x | t < u x}) ≤ δ := by
      rw [restriction_mass hT.1 hE]
      exact (measureReal_mono (fun x hx => hti.1.trans hx)).trans hsupp
    have hi := hiso _ hE ht.1 hsmall
    have hr := radius_nonneg μ (n := k+2) (omega_pos (by omega : 0 < k+2)).le t
    have he := radius_pow μ (omega_pos (by omega : 0 < k+2)) (by omega : 0 < k+2) t
    have hib : (1-η)*(omega (k+2)*(radiusDistribution μ (omega (k+2)) (k+2) t)^(k+2)) ≤
        fillingCoefficient (k+1)*(mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})))^(fillingPower (k+1)) := by
      rw [he,htail]
      exact hi
    have hper := perimeter_of_small_isoperimetry (by omega : 0 < k+1) hr
      (mass_nonneg _) hη hη1 hib
    refine ⟨?_,?_,ht.2.1⟩
    · simpa only [Nat.add_assoc, show (1:ℕ)+1=2 from rfl, show k+2-1=k+1 by omega,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, show (1:ℝ)+1=2 by norm_num] using hper
    · exact ht.2.2.trans (mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg)
  have hs := rearranged_sobolev μ ζ hn hU (by positivity : 0 < (K:ℝ)+1) hη1 hpos hupper hneg
    (P := fun t => mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})))
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hco')
  rw [hmoment,hζ] at hs
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hs

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Truncation
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

lemma positiveTrunc_lipschitz (τ : ℝ) : LipschitzWith 1 (positiveTrunc τ) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  change LipschitzWith 1 (fun t : ℝ => max (|t|-τ) 0)
  have hh := (ha.sub (LipschitzWith.const τ)).max (LipschitzWith.const (0:ℝ))
  norm_num only [add_zero,max_eq_left zero_le_one] at hh
  exact hh

lemma positiveTrunc_sub_bounds {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    0 ≤ |t|-positiveTrunc τ t ∧ |t|-positiveTrunc τ t ≤ τ := by
  dsimp only [positiveTrunc]
  constructor
  · apply sub_nonneg.mpr
    exact max_le (by linarith) (abs_nonneg _)
  · linarith [le_max_left (|t|-τ) (0:ℝ)]

lemma ae_fderiv_trunc_cases {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {F : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ z ∂μ, fderiv ℝ (positiveTrunc τ ∘ F) z = 0 ∨
      fderiv ℝ (positiveTrunc τ ∘ F) z = fderiv ℝ F z ∨
      fderiv ℝ (positiveTrunc τ ∘ F) z = -fderiv ℝ F z := by
  have hcomp := (positiveTrunc_lipschitz τ).comp hF
  filter_upwards [LipschitzWith.ae_fderiv_zero_on_level μ hcomp 0] with z hz
  by_cases hzero : positiveTrunc τ (F z) = 0
  · exact Or.inl (hz hzero)
  have hzpos : 0 < |F z|-τ := by
    by_contra hn
    exact hzero (max_eq_right (le_of_not_gt hn))
  have hne : F z ≠ 0 := by
    intro h
    simp only [h,abs_zero,zero_sub] at hzpos
    linarith
  have hev : ∀ᶠ y in 𝓝 z, τ < |F y| := hF.continuous.abs.continuousAt
    (Ioi_mem_nhds (by linarith : τ < |F z|))
  by_cases hpos : 0 < F z
  · right; left
    have hp : ∀ᶠ y in 𝓝 z, 0 < F y := hF.continuous.continuousAt (Ioi_mem_nhds hpos)
    have he : positiveTrunc τ ∘ F =ᶠ[𝓝 z] fun y => F y-τ := by
      filter_upwards [hev,hp] with y hy hp
      simp only [Function.comp_apply,positiveTrunc,abs_of_pos hp]
      rw [abs_of_pos hp] at hy
      exact max_eq_left (by linarith)
    exact he.fderiv_eq.trans (fderiv_sub_const τ)
  · right; right
    have hn : F z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hp : ∀ᶠ y in 𝓝 z, F y < 0 := hF.continuous.continuousAt (Iio_mem_nhds hn)
    have he : positiveTrunc τ ∘ F =ᶠ[𝓝 z] fun y => -F y-τ := by
      filter_upwards [hev,hp] with y hy hp
      simp only [Function.comp_apply,positiveTrunc,abs_of_neg hp]
      rw [abs_of_neg hp] at hy
      exact max_eq_left (by linarith)
    rw [he.fderiv_eq,fderiv_sub_const,fderiv_fun_neg]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_normSq_trunc_le (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      q.normSq i (positiveTrunc τ ∘ u) z ≤ q.normSq i u z := by
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨F,hF,heF⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (positiveTrunc τ ∘ u)) (positiveTrunc τ ∘ F) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz,Function.comp_apply]
    rw [←heF hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  have hcase := ae_fderiv_trunc_cases volume hF hτ
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hF heF,
    ae_fderivWithin_eq_fderiv_extension volume C.borel ((positiveTrunc_lipschitz τ).comp hF) hecomp,
    hcase.filter_mono ae_restrict_le,q.ae_normSq_bounds i hu] with z hz hc hcase hb
  change fderivWithin ℝ (C.scalar u) C.domain z = _ at hz
  rcases hcase with hzero | heq | heq
  · have he : q.covector i (positiveTrunc τ ∘ u) z = 0 := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) = 0
      rw [hc,hzero]
      ext j
      rfl
    simpa only [normSq,he,zero_dotProduct] using hb.1
  · have he : q.covector i (positiveTrunc τ ∘ u) z = q.covector i u z := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) =
        differentialRow (fderivWithin ℝ (C.scalar u) C.domain z)
      rw [hc,hz,heq]
    simp only [normSq,he,le_refl]
  · have he : q.covector i (positiveTrunc τ ∘ u) z = -q.covector i u z := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) =
        -differentialRow (fderivWithin ℝ (C.scalar u) C.domain z)
      rw [hc,hz,heq]
      ext j
      rfl
    simp only [normSq,he,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg,le_refl]

lemma energyMeasure_trunc_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    q.energyMeasure (positiveTrunc τ ∘ u) ≤ q.energyMeasure u := by
  apply Measure.le_iff.mpr
  intro E hE
  simp only [energyMeasure,weightedMeasure,Measure.sum_apply _ hE]
  apply ENNReal.tsum_le_tsum
  intro i
  exact densityPush_mono_ae (q.chart i).measurable_paramExtended
    ((q.ae_normSq_trunc_le i hu hτ).mono fun z hz =>
      mul_le_mul_of_nonneg_left hz (q.density_nonneg i z)) E

lemma energy_trunc_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (q.energyMeasure (positiveTrunc τ ∘ u)).real univ ≤ (q.energyMeasure u).real univ := by
  let := q.energyMeasure_finite hu
  exact ENNReal.toReal_mono (measure_ne_top _ _) (q.energyMeasure_trunc_le hu hτ univ)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma continuous_memLp {u : X → ℝ} (hu : Continuous u) (p : ℝ≥0∞) : MemLp u p μ :=
  hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)

lemma lpNorm_sq_moment {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Continuous u) (hu0 : ∀ x, 0 ≤ u x)
    {p : ℝ} (hp : 0 < p) :
    lpNorm u (ENNReal.ofReal p) μ ^2 =
      ((∫⁻ x, ENNReal.ofReal ((u x)^p) ∂μ).toReal)^(2/p) := by
  rw [←toReal_eLpNorm hu.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  simp only [←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hu0 _),
    ←ENNReal.ofReal_rpow_of_nonneg (hu0 _) hp.le,←ENNReal.toReal_rpow]
  rw [←Real.rpow_natCast,←Real.rpow_mul ENNReal.toReal_nonneg]
  congr 1
  ring

lemma lpNorm_two_sq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Continuous u) :
    lpNorm u 2 μ ^2 = ∫ x, (u x)^2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg fun x => sq_nonneg (u x))]
  norm_num

lemma truncation_small_support {u : X → ℝ} (hu : Continuous u) {δ : ℝ} (hδ : 0 < δ)
    (hu2 : 0 < lpNorm u 2 μ) :
    μ.real {x | 0 < positiveTrunc (lpNorm u 2 μ / Real.sqrt δ) (u x)} ≤ δ := by
  let τ := lpNorm u 2 μ / Real.sqrt δ
  have hτ : 0 < τ := div_pos hu2 (Real.sqrt_pos.mpr hδ)
  have he : τ^2*δ = lpNorm u 2 μ ^2 := by
    dsimp [τ]
    rw [div_pow,Real.sq_sqrt hδ.le]
    exact div_mul_cancel₀ _ hδ.ne'
  have hi : Integrable (fun x => (u x)^2) μ := (continuous_memLp μ (hu.pow 2) 1).integrable (by norm_num)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x => sq_nonneg (u x)) hi (τ^2)
  have hsub : {x | 0 < positiveTrunc τ (u x)} ⊆ {x | τ^2 ≤ (u x)^2} := by
    intro x hx
    have ha : τ < |u x| := by
      simpa only [mem_ofPred_eq,positiveTrunc,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hx
    change τ^2 ≤ (u x)^2
    nlinarith [sq_abs (u x)]
  have hm := measureReal_mono (μ := μ) hsub
  rw [←lpNorm_two_sq μ hu] at hb
  have hh := (mul_le_mul_of_nonneg_left hm (sq_nonneg τ)).trans hb
  change μ.real {x | 0 < positiveTrunc τ (u x)} ≤ δ
  nlinarith [sq_pos_of_pos hτ]

lemma truncation_norm_bound {u : X → ℝ} (hu : Continuous u) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) {τ : ℝ} (hτ : 0 ≤ τ) :
    lpNorm u p μ ≤ lpNorm (positiveTrunc τ ∘ u) p μ +
      μ.real univ ^ p.toReal⁻¹ * τ := by
  let z := positiveTrunc τ ∘ u
  have hz : Continuous z := (positiveTrunc_lipschitz τ).continuous.comp hu
  have ht := lpNorm_le_lpNorm_add_lpNorm_sub' (continuous_memLp μ hz p) hp
    (f := fun x => |u x|)
  rw [lpNorm_fun_abs hu.aestronglyMeasurable] at ht
  apply ht.trans
  apply add_le_add_right
  have hb : lpNorm (fun x => |u x|-z x) p μ ≤ lpNorm (fun _ : X => τ) p μ := by
    apply lpNorm_mono_real (memLp_const τ)
    intro x
    change abs (|u x|-positiveTrunc τ (u x)) ≤ τ
    have h := positiveTrunc_sub_bounds hτ (u x)
    exact (abs_le.mpr ⟨by linarith [h.1],h.2⟩)
  rw [lpNorm_const' (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpfin,
    Real.norm_eq_abs,abs_of_nonneg hτ] at hb
  exact hb.trans_eq (mul_comm _ _)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_AlmostSharp
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open BorelRestriction MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem almost_sobolev_from_small {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} (q : ChartGeometry hT) {S B p : ℝ}
    (hS : 0 < S) (hB : 0 ≤ B) (hp : 1 < p)
    (hsmall : ∀ η ∈ Ioo (0:ℝ) 1, ∃ δ > 0,
      ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u → (∀ x, 0 ≤ u x) →
        (currentMassMeasure hT).real {x | 0 < u x} ≤ δ →
        S*(1-η)^2*lpNorm u (ENNReal.ofReal p) (currentMassMeasure hT)^2 ≤
          B*(q.energyMeasure u).real univ)
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < S) :
    ∃ C ≥ (0:ℝ), ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      (S-ε)*lpNorm u (ENNReal.ofReal p) (currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ + C*lpNorm u 2 (currentMassMeasure hT)^2 := by
  let μ := currentMassMeasure hT
  let t := ε/(4*S)
  have ht : 0 < t := div_pos hε (by positivity)
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < 4*S)).mpr (by linarith)
  have het : ε = 4*S*t := by dsimp [t]; field_simp
  obtain ⟨δ,hδ,hs⟩ := hsmall t ⟨ht,ht1⟩
  let A := S*(1-t)^2
  let d := μ.real univ ^ (ENNReal.ofReal p).toReal⁻¹ / Real.sqrt δ
  have hA : 0 < A := mul_pos hS (sq_pos_of_pos (sub_pos.mpr ht1))
  have hd : 0 ≤ d := by positivity
  have hcoeff : (S-ε)*(1+t) ≤ A := by
    dsimp only [A]
    rw [het]
    nlinarith [mul_nonneg hS.le (sq_nonneg t),mul_nonneg hS.le ht.le]
  refine ⟨A/t*d^2,by positivity,?_⟩
  intro u K hu
  have hu2n : 0 ≤ lpNorm u 2 μ := lpNorm_nonneg
  by_cases hu2 : lpNorm u 2 μ = 0
  · have haz := (lpNorm_eq_zero (continuous_memLp μ hu.continuous 2) (by norm_num)).mp hu2
    have hpz : lpNorm u (ENNReal.ofReal p) μ = 0 :=
      (lpNorm_eq_zero (continuous_memLp μ hu.continuous _) (by positivity)).mpr haz
    change (S-ε)*lpNorm u (ENNReal.ofReal p) μ^2 ≤ _
    rw [hpz]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact add_nonneg (mul_nonneg hB (measureReal_nonneg))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hu2p : 0 < lpNorm u 2 μ := lt_of_le_of_ne hu2n (Ne.symm hu2)
  let τ := lpNorm u 2 μ / Real.sqrt δ
  let z := positiveTrunc τ ∘ u
  have hτ : 0 ≤ τ := by positivity
  have hz := (positiveTrunc_lipschitz τ).comp hu
  have hsup := truncation_small_support μ hu.continuous hδ hu2p
  have hpos : ∀ x, 0 ≤ z x := fun x => le_max_right _ _
  have hzs := hs z (1*K) hz hpos hsup
  have henergy := q.energy_trunc_le hu hτ
  have hbound := hzs.trans (mul_le_mul_of_nonneg_left henergy hB)
  have hnorm := truncation_norm_bound μ hu.continuous
    (show 1 ≤ ENNReal.ofReal p by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le) ENNReal.ofReal_ne_top hτ
  have he : μ.real univ ^ (ENNReal.ofReal p).toReal⁻¹ * τ = d*lpNorm u 2 μ := by
    dsimp [τ,d]
    ring
  rw [he] at hnorm
  have hnormsq : lpNorm u (ENNReal.ofReal p) μ^2 ≤
      (lpNorm z (ENNReal.ofReal p) μ+d*lpNorm u 2 μ)^2 := by
    apply (sq_le_sq₀ lpNorm_nonneg (add_nonneg lpNorm_nonneg (mul_nonneg hd hu2n))).mpr hnorm
  have hyoung : (lpNorm z (ENNReal.ofReal p) μ+d*lpNorm u 2 μ)^2 ≤
      (1+t)*lpNorm z (ENNReal.ofReal p) μ^2+
        (1+t⁻¹)*(d*lpNorm u 2 μ)^2 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have hh := sq_nonneg (t*lpNorm z (ENNReal.ofReal p) μ-d*lpNorm u 2 μ)
    have hinv : t*t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    nlinarith
  have hbig := hnormsq.trans hyoung
  have hdiv : (S-ε) ≤ A/(1+t) := (le_div_iff₀ (by linarith)).mpr hcoeff
  have hmul := mul_le_mul_of_nonneg_left hbig (show 0 ≤ A/(1+t) from le_of_lt (div_pos hA (by linarith)))
  have hid : A/(1+t)*((1+t)*lpNorm z (ENNReal.ofReal p) μ^2+
      (1+t⁻¹)*(d*lpNorm u 2 μ)^2) =
      A*lpNorm z (ENNReal.ofReal p) μ^2+A/t*d^2*lpNorm u 2 μ^2 := by
    field_simp
    ring
  rw [hid] at hmul
  have hlo := mul_le_mul_of_nonneg_right hdiv (sq_nonneg (lpNorm u (ENNReal.ofReal p) μ))
  exact (hlo.trans hmul).trans (add_le_add hbound le_rfl)

theorem extremal_almost_sobolev {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1) {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))) :
    ∃ C ≥ (0:ℝ), ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      ((k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))-ε)*
        lpNorm u (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1)^2 ≤
      4/((k+2:ℝ)-2)*(q.energyMeasure u).real univ +
        C*lpNorm u 2 (currentMassMeasure hT.1)^2 := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hB : 0 ≤ 4/((k+2:ℝ)-2) := div_nonneg (by norm_num) (by linarith)
  have hS : 0 < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) := by
    have hω := omega_pos (by omega : 0 < k+2+1)
    unfold sphereArea
    positivity
  have hp : 1 < sobolevP (k+2) := by
    unfold sobolevP
    push_cast
    apply (lt_div_iff₀ (sub_pos.mpr hn)).mpr
    linarith
  apply almost_sobolev_from_small q hS hB hp ?_ hε hεS
  intro η hη
  have hpfill : 1 < fillingPower (k+1) := by
    unfold fillingPower
    push_cast
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨δ,hδ,hi⟩ := small_restriction_mass_bound hX
    (fillingCoefficient_pos (by omega : 0 < k+1)).le hpfill hd hr hfill hT hz hm hext hη.1 hη.2
  refine ⟨δ,hδ.1,?_⟩
  intro u K hu hu0 hsupp
  have hh := small_support_sobolev hk hT hz hX q hη.1 hη.2 hi hu hu0 hsupp
  rw [←lpNorm_sq_moment (currentMassMeasure hT.1) hu.continuous hu0
    (lt_trans zero_lt_one hp)] at hh
  have hb := mul_le_mul_of_nonneg_left hh (sq_nonneg (1-η))
  have he : (1-η)^2 * (4/((k+2:ℝ)-2)*((1-η)⁻¹)^2*(q.energyMeasure u).real univ) =
      4/((k+2:ℝ)-2)*(q.energyMeasure u).real univ := by
    field_simp [(sub_pos.mpr hη.2).ne']
  rw [he] at hb
  nlinarith

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Completion
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGraph_isClosed : IsClosed (q.closedGraph : Set q.GraphAmbient) :=
  q.lipschitzGraph.isClosed_topologicalClosure

instance instCompleteSpaceSubtypeGraphAmbientMemSubmoduleRealSobolev : CompleteSpace q.Sobolev := q.closedGraph_isClosed.completeSpace_coe

lemma graph_norm_sq (P : q.GraphAmbient) :
    ‖P‖^2 = ‖q.valueProjection P‖^2+‖q.gradientProjection P‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 P

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma sobolev_norm_sq (P : q.Sobolev) :
    ‖P‖^2 = ‖q.inclusion P‖^2 + ‖q.closedGradient P‖^2 := q.graph_norm_sq P

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Constant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradient_const (c : ℝ) : q.gradient (LipschitzWith.const c) = 0 := by
  apply Lp.ext
  filter_upwards [(q.memLp_gradientFunction (LipschitzWith.const c)).coeFn_toLp,
    q.ae_gradientFunction_bound (LipschitzWith.const c),Lp.coeFn_zero (E := Euc (k+1)) (p := 2) (μ := q.atlasMeasure)] with w hw hb hz
  rw [gradient,hw,hz]
  apply norm_eq_zero.mp
  exact le_antisymm hb (norm_nonneg _)

@[simp] lemma closedGradient_constant (c : ℝ) : q.closedGradient (q.constant c) = 0 :=
  q.gradient_const c

lemma criticalNorm_constant {p : ℝ} (hp : 0 < p) (c : ℝ) :
    AnalyticMinimizer.criticalNorm q.inclusion p (q.constant c) =
      |c| *(mass T)^(1/p) := by
  dsimp only [AnalyticMinimizer.criticalNorm,constant]
  rw [q.inclusion_lipSobolev]
  have he : (value (hT := hT) (LipschitzWith.const c) : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun _ => c) := ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const c)).memLp 2).coeFn_toLp
  rw [AnalyticMinimizer.lpNorm_congr_ae he,
    lpNorm_const' (by positivity) ENNReal.ofReal_ne_top,MassMeasure.currentMassMeasure_total]
  rw [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs,one_div]

lemma norm_inclusion_constant_sq (c : ℝ) : ‖q.inclusion (q.constant c)‖^2 = c^2*mass T := by
  rw [constant,q.inclusion_lipSobolev,norm_value,lpNorm_const' (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,MassMeasure.currentMassMeasure_total,Real.norm_eq_abs]
  rw [mul_pow,sq_abs,←Real.rpow_mul_natCast (mass_nonneg T)]
  norm_num

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_Geometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [IsFiniteMeasure μ] in
theorem exists_critical_minimizer [IsFiniteMeasure μ] (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (hI : IsCompactOperator I) (hgraph : ∀ u, ‖u‖^2 = ‖I u‖^2+‖G u‖^2)
    {A B p S : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    (hsob : ∀ ε : ℝ, 0 < ε → ε < S → ∃ C ≥ (0:ℝ), ∀ u,
      (S-ε)*(criticalNorm I p u)^2 ≤ A*‖G u‖^2+C*‖I u‖^2)
    (w : H) (hw : 0 < criticalNorm I p w)
    (hwS : energy I G A B w/(criticalNorm I p w)^2 < S) :
    ∃ v : H, criticalNorm I p v = 1 ∧ energy I G A B v < S ∧
      ∀ u, energy I G A B v*(criticalNorm I p u)^2 ≤ energy I G A B u := by
  obtain ⟨Λ,hΛ,hΛw,hmin,u,hu,hub,hQ⟩ := normalized_infimum (criticalNorm I p) (energy I G A B)
    (criticalNorm_nonneg I p) (energy_nonneg I G hA.le hB.le)
    (criticalNorm_smul I p) (energy_smul I G A B) w hw
  have hΛS : Λ < S := hΛw.trans_lt hwS
  let c := min A B
  have hc : 0 < c := lt_min hA hB
  have hcoerce (u : H) : c*‖u‖^2 ≤ energy I G A B u := by
    rw [hgraph]
    dsimp [energy]
    have h1 := mul_le_mul_of_nonneg_right (min_le_left A B) (sq_nonneg ‖G u‖)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right A B) (sq_nonneg ‖I u‖)
    dsimp [c]
    nlinarith
  let M := Real.sqrt (energy I G A B (u 0)/c)
  have hM (j : ℕ) : ‖u j‖ ≤ M := by
    apply (Real.le_sqrt (norm_nonneg _) (div_nonneg (energy_nonneg I G hA.le hB.le _) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hcoerce (u j)).trans (hub j)
  obtain ⟨v,hv,s,hs,hweak,hstrong⟩ := exists_weak_strong_subsequence I hI u M hM
  obtain ⟨t,ht,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  have hQ' := hQ.comp (hs.comp ht).tendsto_atTop
  have hw' (z : H) := (hweak z).comp ht.tendsto_atTop
  have hs' := hstrong.comp ht.tendsto_atTop
  obtain ⟨hNv,hQv⟩ := critical_no_loss I G hA.le hB.le hp hΛ hΛS hm hmin hsob
    (u := fun j => u (s (t j))) (fun j => hu (s (t j))) hQ' hw' hs' hae
  exact ⟨v,hNv,hQv ▸ hΛS,fun u => hQv ▸ hmin u⟩

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma constant_subthreshold {n : ℕ} (hn : 2 < n) {m : ℝ}
    (hm : 0 < m) (hms : m < sphereArea n) :
    (n:ℝ)*m/(m^(1/sobolevP n))^2 < (n:ℝ)*sphereArea n^(2/(n:ℝ)) := by
  have hn2 : (2:ℝ) < n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have he : 1-((1/sobolevP n)*2) = 2/(n:ℝ) := by
    dsimp [sobolevP]
    field_simp
    ring
  have heq : (n:ℝ)*m/(m^(1/sobolevP n))^2 = (n:ℝ)*m^(2/(n:ℝ)) := by
    rw [←Real.rpow_mul_natCast hm.le]
    rw [mul_div_assoc]
    conv_lhs => arg 2; arg 1; rw [←Real.rpow_one m]
    rw [←Real.rpow_sub hm]
    norm_num only [Nat.cast_ofNat]
    rw [he]
  rw [heq]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hm.le hms (div_pos (by norm_num) hn0)) hn0

theorem extremal_critical_minimizer_oai {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      criticalNorm q.inclusion (sobolevP (k+2)) v = 1 ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v <
        (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) ∧
      ∀ u, energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
        (criticalNorm q.inclusion (sobolevP (k+2)) u)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) u := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hA : 0 < 4/((k+2:ℝ)-2) := div_pos (by norm_num) hk0
  have hB : 0 < (k+2:ℝ) := by positivity
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  obtain ⟨C,hC,hb⟩ := extremal_almost_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  have hcompact := q.inclusion_compact (Slicing.normalApprox_of_integral hT) hz hX hp
    (show 0 < S-S/2 by linarith) hA.le hC hb
  obtain ⟨D,hD,hclosed⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext
    (show 0 < S/2 by positivity) (show S/2 < S by linarith)
  refine exists_critical_minimizer q.inclusion q.closedGradient hcompact q.sobolev_norm_sq
    hA hB hp (fun u => (hclosed u).1) ?_ (q.constant 1) ?_ ?_
  · intro ε hε hεS
    obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev hk hX hT hz hm q hd hr hfill hext hε hεS
    exact ⟨C,hC,fun u => (hb u).2⟩
  · rw [q.criticalNorm_constant (by linarith : 0 < sobolevP (k+2))]
    simpa only [abs_one,one_mul] using Real.rpow_pos_of_pos hm (1/sobolevP (k+2))
  · rw [q.criticalNorm_constant (by linarith : 0 < sobolevP (k+2))]
    dsimp [energy]
    rw [q.closedGradient_constant,q.norm_inclusion_constant_sq]
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,
      one_pow,one_mul,abs_one]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using constant_subthreshold (by omega : 2 < k+2) hm hms

end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.extremal_critical_minimizer_oai.{u_1} := @OAI.CAT0Fillings.extremal_critical_minimizer_oai.{u_1}
