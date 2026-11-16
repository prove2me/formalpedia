-- Prove2me | solution 1 for NestedCRP.dirichlet_moment
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T22:42:06.484708+00:00
-- url     : https://prove2.me/submissions/4618a242-b6c8-4469-83c8-1d888d0ae037

import Mathlib
import Definitions.Def_NestedCRP_dirichletMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace GeneralDirichlet
noncomputable section
lemma gamma_integral (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (a-1) * Real.exp (-(r*t))) =
      ENNReal.ofReal (Real.Gamma a / r^a) := by
  have hI : ∫ t in Ioi (0:ℝ), t ^ (a-1) * Real.exp (-(r*t)) = Real.Gamma a / r^a := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr,Real.div_rpow zero_le_one hr.le,Real.one_rpow]
    ring
  rw [← hI,ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_integral_ne_zero (by rw [hI]; positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
lemma gamma_nat (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^m * Real.exp (-(r*t))) =
      ENNReal.ofReal (m.factorial / r^(m+1)) := by
  have h := gamma_integral ((m:ℝ)+1) r (by positivity) hr
  simp only [add_sub_cancel_right,Real.rpow_natCast,Real.Gamma_nat_eq_factorial] at h
  rw [show (m:ℝ)+1 = ((m+1:ℕ):ℝ) by norm_num,Real.rpow_natCast] at h
  exact h
lemma gamma_pos (a : ℝ) : ∀ᵐ x ∂gammaMeasure a 1, (0:ℝ) < x := by
  have hf : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  rw [gammaMeasure,ae_withDensity_iff hf]
  have hn : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hn] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h
lemma gamma_laplace (a : ℝ) (ha : 0 < a) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (z^n * Real.exp (-(t*z))) ∂gammaMeasure a 1 =
      ENNReal.ofReal (Real.Gamma (a+n) / Real.Gamma a / (1+t)^(a+n)) := by
  have hf : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  have hg : Measurable fun z : ℝ => ENNReal.ofReal (z^n * Real.exp (-(t*z))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul _ hf hg]
  have hn : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
  have he : (fun z => gammaPDF a 1 z * ENNReal.ofReal (z^n * Real.exp (-(t*z)))) =ᵐ[volume]
      (Ioi (0:ℝ)).indicator (fun z => ENNReal.ofReal ((Real.Gamma a)⁻¹) *
        ENNReal.ofReal (z^(a+n-1) * Real.exp (-((1+t)*z)))) := by
    filter_upwards [hn] with z hz
    rcases lt_or_gt_of_ne hz with hz | hz
    · rw [gammaPDF_of_neg hz,zero_mul,indicator_of_notMem (by simpa using hz.le)]
    · rw [gammaPDF_of_nonneg hz.le,indicator_of_mem (by simpa using hz),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [Real.one_rpow,one_mul]
      rw [show -((1+t)*z) = -z + -(t*z) by ring,Real.exp_add,
        show a+(n:ℝ)-1 = (a-1)+(n:ℝ) by ring,Real.rpow_add hz,Real.rpow_natCast]
      ring
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ioi,
    lintegral_const_mul _ (by fun_prop),gamma_integral (a+n) (1+t) (by positivity) (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end
end GeneralDirichlet

namespace GeneralDirichlet
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
lemma beta_integral (n : ℕ) (d : ℝ) (hn : 1 ≤ n) (hd : 0 < d) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) =
      ENNReal.ofReal ((n-1).factorial * Real.Gamma d / Real.Gamma ((n:ℝ)+d)) := by
  let N : ℝ := (n:ℝ)+d
  have hN : 0 < N := by dsimp [N]; positivity
  have hG : 0 < Real.Gamma N := Real.Gamma_pos_of_pos hN
  have step1 : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) =
      ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
        ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u))) := by
    intro t ht
    have ht' : 0 < 1+t := by linarith [mem_Ioi.mp ht]
    rw [lintegral_const_mul _ (by fun_prop),gamma_integral N (1+t) hN ht',
      ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (le_of_lt ht) _) hG.le)]
    congr 1
    dsimp [N] at *
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    exact (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.1^(n-1)/Real.Gamma N)).mul (ENNReal.measurable_ofReal.comp (by fun_prop :
      Measurable fun p : ℝ × ℝ => p.2^(N-1)*Real.exp (-((1+p.1)*p.2)))))]
  have step2 : ∀ u ∈ Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
      ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u)))) =
      ENNReal.ofReal ((n-1).factorial/Real.Gamma N) *
        ENNReal.ofReal (u^(d-1)*Real.exp (-(1*u))) := by
    intro u hu
    have hu' : 0 < u := hu
    have e : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)/Real.Gamma N) *
        ENNReal.ofReal (u^(N-1)*Real.exp (-((1+t)*u))) =
        ENNReal.ofReal (u^(N-1)*Real.exp (-u)/Real.Gamma N) *
          ENNReal.ofReal (t^(n-1)*Real.exp (-(u*t))) := by
      intro t ht
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (le_of_lt ht) _) hG.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((1+t)*u) = -u + -(u*t) by ring,Real.exp_add]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi e,
      lintegral_const_mul _ (by fun_prop),gamma_nat (n-1) hu',
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.sub_add_cancel hn,one_mul,
      show N-1 = (d-1)+(n:ℝ) by dsimp [N]; ring,Real.rpow_add hu',Real.rpow_natCast]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step2,
    lintegral_const_mul _ (by fun_prop),gamma_integral d 1 hd one_pos,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Real.one_rpow,div_one]
  dsimp [N]
  ring
end GeneralDirichlet

namespace GeneralDirichlet
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
noncomputable section
lemma pi_pos {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i) :
    ∀ᵐ z ∂(Measure.pi fun i => gammaMeasure (α i) 1), ∀ i, (0:ℝ) < z i := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  exact eventually_all.2 fun i => Measure.tendsto_eval_ae_ae.eventually (gamma_pos (α i))
lemma product_laplace {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i)
    (a : ι → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (∏ i, (z i ^ a i * Real.exp (-(t*z i))))
      ∂(Measure.pi fun i => gammaMeasure (α i) 1) =
      ENNReal.ofReal (∏ i, (Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i))) := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  have h1 : ∀ i, ∫ x, x^a i * Real.exp (-(t*x)) ∂gammaMeasure (α i) 1 =
      Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i) := by
    intro i
    have hai := hα i
    rw [integral_eq_lintegral_of_nonneg_ae,gamma_laplace (α i) (hα i) (a i) ht,
      ENNReal.toReal_ofReal (by positivity)]
    · filter_upwards [gamma_pos (α i)] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le
    · exact (by fun_prop : Continuous fun x : ℝ => x^a i * Real.exp (-(t*x))).aestronglyMeasurable
  have hint : ∀ i, Integrable (fun x : ℝ => x^a i * Real.exp (-(t*x))) (gammaMeasure (α i) 1) :=
    fun i => Integrable.of_integral_ne_zero (by have hai := hα i; rw [h1]; positivity)
  have h2 := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun (i : ι) (x : ℝ) => x^a i * Real.exp (-(t*x)))
    (μ := fun i => gammaMeasure (α i) 1)
  simp only [h1] at h2
  rw [← h2,ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.fintype_prod (f := fun (i : ι) (x : ℝ) => x^a i * Real.exp (-(t*x))) hint
  · filter_upwards [pi_pos α hα] with z hz
    exact Finset.prod_nonneg fun i _ => mul_nonneg (pow_nonneg (hz i).le _) (Real.exp_pos _).le
lemma reduce {ι : Type*} [Fintype ι] (α : ι → ℝ) (a : ι → ℕ) :
    (∫ p, ∏ i, p i ^ a i ∂NestedCRP.dirichletMeasure α) =
      ∫ z, (∏ i, z i ^ a i)/(∑ i, z i)^(∑ i, a i) ∂(Measure.pi fun i => gammaMeasure (α i) 1) := by
  rw [NestedCRP.dirichletMeasure,integral_map (by fun_prop : Measurable fun x : ι → ℝ => fun i => x i/∑ j,x j).aemeasurable
    (by fun_prop : Continuous fun p : ι → ℝ => ∏ i,p i^a i).aestronglyMeasurable]
  simp only [div_pow,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
lemma moment {ι : Type*} [Fintype ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i) (a : ι → ℕ) :
    (∫ p, ∏ i,p i^a i ∂NestedCRP.dirichletMeasure α) =
      Real.Gamma (∑ i,α i)/(∏ i,Real.Gamma (α i)) *
        ((∏ i,Real.Gamma ((a i:ℝ)+α i))/Real.Gamma ((∑ i,(a i:ℝ))+∑ i,α i)) := by
  classical
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  set d := ∑ i,α i with hd
  have hdpos : 0 < d := Finset.sum_pos (fun i _ => hα i) Finset.univ_nonempty
  set n := ∑ i,a i with hn
  have hg : (∏ i,Real.Gamma (α i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (Real.Gamma_pos_of_pos (hα i)).ne'
  have hprod : 0 < ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i) := Finset.prod_pos fun i _ => by
    have hi := hα i
    positivity
  rw [reduce]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have ha : ∀ i,a i=0 := fun i => (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)
    simp only [ha,pow_zero,Finset.prod_const_one,Finset.sum_const_zero,div_one,Nat.cast_zero,zero_add]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    field_simp [(Real.Gamma_pos_of_pos hdpos).ne']
  · set π := Measure.pi fun i => gammaMeasure (α i) 1
    have hnf : (0:ℝ) < (n-1).factorial := by positivity
    have hrep : ∀ᵐ z ∂π, ENNReal.ofReal ((∏ i,z i^a i)/(∑ i,z i)^n) =
        ENNReal.ofReal (1/(n-1).factorial) * ∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1)) := by
      filter_upwards [pi_pos α hα] with z hz
      have hS : 0 < ∑ i,z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
      have hF : 0 ≤ ∏ i,z i^a i := Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _
      have e : ∀ t,(∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1) =
          (∏ i,z i^a i)*(t^(n-1)*Real.exp (-((∑ i,z i)*t))) := by
        intro t
        rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_mul]
        simp only [neg_mul,Finset.sum_neg_distrib,mul_comm t]
        ring
      simp_rw [e]
      have hm : Measurable fun t : ℝ => ENNReal.ofReal (t^(n-1)*Real.exp (-((∑ i,z i)*t))) := ENNReal.measurable_ofReal.comp (by fun_prop)
      simp_rw [ENNReal.ofReal_mul hF]
      rw [lintegral_const_mul _ hm,gamma_nat (n-1) hS,Nat.sub_add_cancel hpos,
        ← ENNReal.ofReal_mul hF,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hinner : ∀ t ∈ Ioi (0:ℝ), (∫⁻ z,ENNReal.ofReal
        ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1)) ∂π) =
        ENNReal.ofReal (∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)) *
          ENNReal.ofReal (t^(n-1)/(1+t)^((n:ℝ)+d)) := by
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      simp_rw [ENNReal.ofReal_mul' (pow_nonneg ht0 (n-1))]
      have hm : Measurable fun z : ι → ℝ => ENNReal.ofReal (∏ i,(z i^a i*Real.exp (-(t*z i)))) := ENNReal.measurable_ofReal.comp (by fun_prop)
      have hpL : 0 < ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)/(1+t)^(α i+a i) :=
        Finset.prod_pos fun i _ => by
          have hi := hα i
          positivity
      rw [lintegral_mul_const _ hm,product_laplace α hα a ht0,
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Finset.prod_div_distrib,← Real.rpow_sum_of_pos (by linarith : 0 < 1+t)]
      have he : ∑ i,(α i+(a i:ℝ)) = (n:ℝ)+d := by simp only [Finset.sum_add_distrib,← Nat.cast_sum,← hn,← hd];ring
      rw [he]
      ring
    have hmeas : Measurable (Function.uncurry fun (z : ι → ℝ) (t : ℝ) => ENNReal.ofReal
      ((∏ i,(z i^a i*Real.exp (-(t*z i))))*t^(n-1))) := ENNReal.measurable_ofReal.comp (by fun_prop)
    have hL : (∫⁻ z,ENNReal.ofReal ((∏ i,z i^a i)/(∑ i,z i)^n) ∂π) =
        ENNReal.ofReal ((n-1).factorial*Real.Gamma d/Real.Gamma ((n:ℝ)+d)/(n-1).factorial *
          ∏ i,Real.Gamma (α i+a i)/Real.Gamma (α i)) := by
      rw [lintegral_congr_ae hrep,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_lintegral_swap hmeas.aemeasurable,setLIntegral_congr_fun measurableSet_Ioi hinner,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,beta_integral n d hpos hdpos,
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [integral_eq_lintegral_of_nonneg_ae,hL,ENNReal.toReal_ofReal (by positivity)]
    · simp only [Finset.prod_div_distrib,add_comm (α _) _,Nat.cast_sum] at *
      dsimp [n,d]
      push_cast
      field_simp
    · filter_upwards [pi_pos α hα] with z hz
      exact div_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _)
        (pow_nonneg (Finset.sum_nonneg fun i _ => (hz i).le) _)
    · exact (by fun_prop : Measurable fun z : ι → ℝ => (∏ i,z i^a i)/(∑ i,z i)^n).aestronglyMeasurable
end
end GeneralDirichlet


open MeasureTheory ProbabilityTheory
 theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (α : ι → ℝ) (hα : ∀ i,0 < α i) (n : ι → ℕ) :
    ∫ U, ∏ i,U i^n i ∂NestedCRP.dirichletMeasure α =
      Real.Gamma (∑ i,α i)/(∏ i,Real.Gamma (α i)) *
        ((∏ i,Real.Gamma ((n i:ℝ)+α i))/Real.Gamma ((∑ i,(n i:ℝ))+∑ i,α i)) :=
  GeneralDirichlet.moment α hα n
namespace GeneralDirichlet
lemma zero_exponents_control {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i,0 < α i) :
    (∫ p, ∏ i,p i^(0:ℕ) ∂NestedCRP.dirichletMeasure α) = 1 := by
  letI : ∀ i, IsProbabilityMeasure (gammaMeasure (α i) 1) := fun i => isProbabilityMeasure_gammaMeasure (hα i) one_pos
  rw [reduce]
  simp [Measure.real]
lemma uniform_pair_control :
    (∫ p, p 0 * p 1 ∂NestedCRP.dirichletMeasure (fun _ : Fin 2 => (1:ℝ))) = (1/6:ℝ) := by
  have h := moment (fun _ : Fin 2 => (1:ℝ)) (by intro i; norm_num) (fun _ => 1)
  norm_num [Fin.prod_univ_two,Fin.sum_univ_two,Real.Gamma_nat_eq_factorial] at h
  exact h
lemma singleton_control (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ p, p 0^n ∂NestedCRP.dirichletMeasure (fun _ : Fin 1 => a)) = 1 := by
  have h := moment (fun _ : Fin 1 => a) (fun _ => ha) (fun _ => n)
  simpa [Real.Gamma_pos_of_pos ha |>.ne',Real.Gamma_pos_of_pos (show 0 < (n:ℝ)+a by positivity) |>.ne'] using h
end GeneralDirichlet
