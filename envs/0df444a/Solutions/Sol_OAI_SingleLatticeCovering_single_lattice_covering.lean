-- Prove2me | solution 1 for OAI.SingleLatticeCovering.single_lattice_covering
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T13:07:00.295338+00:00
-- url     : https://prove2.me/submissions/a87c7a72-b14f-49c5-9c1b-8e05a387beef

import Mathlib
import Definitions.Def_SingleLatticeCovering
import Definitions.Def_OAIB3Sl000
import Theorems.Thm_OAI_SingleLatticeCovering_Assembly_sections_and_circuits_cover
import Theorems.Thm_OAI_SingleLatticeCovering_GaussianProjection_actual_smoothed_lower

section
-- module Solutions.OAIB3_Slc.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Folded
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section





section



noncomputable section
open scoped BigOperators
open Real

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι]

lemma gamma1_pos (x : ℝ) : 0 < gamma1 x :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))

lemma density_pos {h : ℝ} (hh : 0 < h) (t : ℝ) : 0 < density h t :=
  add_pos (mul_pos hh (gamma1_pos _)) (mul_pos hh (gamma1_pos _))

lemma folded_pos {h : ℝ} (hh : 0 < h) (t : ι → ℝ) : 0 < folded h t :=
  Finset.prod_pos (fun _ _ => density_pos hh _)

lemma alpha_pos : 0 < alpha := by unfold alpha; positivity

lemma probability_sum {h : ℝ} (hh : 0 < h) (t : ℝ) :
    probability h t false + probability h t true = 1 := by
  simp only [probability, bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero,
    ← add_div]
  exact div_self (density_pos hh t).ne'

lemma probability_pos {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    0 < probability h t e :=
  div_pos (mul_pos hh (gamma1_pos _)) (density_pos hh _)

lemma probability_le_one {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    probability h t e ≤ 1 := by
  have hs := probability_sum hh t
  have hf := (probability_pos hh t false).le
  have ht := (probability_pos hh t true).le
  cases e <;> linarith

lemma wordMass_sum [DecidableEq ι] {h : ℝ} (hh : 0 < h) (t : ι → ℝ) :
    (∑ e : ι → Bool, wordMass h t e) = 1 := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  have hs (j : ι) : (∑ e : Bool, probability h (t j) e) = 1 := by
    rw [Fintype.sum_bool]
    linarith [probability_sum hh (t j)]
  simp only [hs, Finset.prod_const_one]

lemma folded_identity {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool) :
    atom h t e = folded h t * wordMass h t e := by
  have ha : atom h t e = ∏ j, h*gamma1 (h*(t j-bitValue (e j))) := by
    simp [atom, gamma, Finset.prod_mul_distrib]
  rw [ha, folded, wordMass, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [probability]
  field_simp [(density_pos hh (t j)).ne']

lemma gaussian_ratio (h t : ℝ) :
    gamma1 (h*t) = Real.exp (h^2*(1/2-t))*gamma1 (h*(t-1)) := by
  have he : -(h*t)^2/2 = h^2*(1/2-t) + -(h*(t-1))^2/2 := by ring
  simp only [gamma1, he, Real.exp_add]
  ring

lemma probability_true_logistic {h : ℝ} (hh : 0 < h) (t : ℝ) :
    probability h t true = (1+Real.exp (h^2*(1/2-t)))⁻¹ := by
  have hg := (gamma1_pos (h*(t-1))).ne'
  unfold probability density
  simp only [bitValue, ↓reduceIte]
  rw [gaussian_ratio h t]
  field_simp
  ring

lemma one_sub_logistic (s : ℝ) :
    1-(1+Real.exp s)⁻¹ = (1+Real.exp (-s))⁻¹ := by
  rw [Real.exp_neg]
  field_simp
  ring

lemma logistic_lower {s : ℝ} (hs : s ≤ 1) : alpha ≤ (1+Real.exp s)⁻¹ := by
  simpa only [alpha, one_div] using
    one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1+exp s)
      (add_le_add_right (Real.exp_le_exp.mpr hs) 1)

lemma probability_central {h t : ℝ} (hh : 0 < h)
    (ht : |t-1/2| ≤ (h^2)⁻¹) (e : Bool) :
    alpha ≤ probability h t e ∧ probability h t e ≤ 1-alpha := by
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  have hprod := mul_le_mul_of_nonneg_left ht hh2.le
  rw [mul_inv_cancel₀ hh2.ne'] at hprod
  have hab := abs_le.mp ht
  have h1 : h^2*(1/2-t) ≤ 1 := by
    calc _ ≤ h^2*|t-1/2| := mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (t-1/2)] : 1/2-t ≤ |t-1/2|) hh2.le
         _ ≤ 1 := hprod
  have h2 : -(h^2*(1/2-t)) ≤ 1 := by
    calc _ ≤ h^2*|t-1/2| := by nlinarith [le_abs_self (t-1/2)]
         _ ≤ 1 := hprod
  have hp := logistic_lower h1
  have hn := logistic_lower h2
  rw [← probability_true_logistic hh t] at hp
  rw [← one_sub_logistic, ← probability_true_logistic hh t] at hn
  have hs := probability_sum hh t
  cases e <;> constructor <;> linarith

lemma wordMass_le_exp_card {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool)
    (S : Finset ι) (hS : ∀ j ∈ S, |t j-1/2| ≤ (h^2)⁻¹) :
    wordMass h t e ≤ Real.exp (-alpha*(S.card : ℝ)) := by
  classical
  have he : 1-alpha ≤ Real.exp (-alpha) := by
    have h := Real.add_one_le_exp (-alpha)
    linarith
  calc
    _ ≤ ∏ j : ι, Real.exp (if j ∈ S then -alpha else 0) := by
      apply Finset.prod_le_prod (fun j _ => (probability_pos hh _ _).le)
      intro j _
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte]
        exact (probability_central hh (hS j hj) _).2.trans he
      · simp only [hj, ↓reduceIte, Real.exp_zero]
        exact probability_le_one hh _ _
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_ite_mem, mul_comm]



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set


lemma continuous_gamma1 : Continuous gamma1 := by
  unfold gamma1
  fun_prop

lemma continuous_density (h : ℝ) : Continuous (density h) := by
  unfold density
  exact (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul continuous_id))).add
    (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul (continuous_id.sub continuous_const))))

lemma gamma1_eq_gaussianPDF (x : ℝ) : gamma1 x = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, gamma1]
  ring

lemma gamma1_int : ∫ x : ℝ, gamma1 x = 1 := by
  simp_rw [gamma1_eq_gaussianPDF]
  exact integral_gaussianPDFReal_eq_one 0 (by norm_num)

lemma gamma1_integrable : Integrable gamma1 := by
  have he : gamma1 = gaussianPDFReal 0 1 := funext gamma1_eq_gaussianPDF
  rw [he]
  exact integrable_gaussianPDFReal _ _

lemma totalMass_eq_integral {h : ℝ} (hh : 0 < h) :
    totalMass h = ∫ x in -h..h, gamma1 x := by
  unfold totalMass density
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left gamma1 hh.ne']
    have hs : (∫ t in (0 : ℝ)..1, gamma1 (h*(t-1))) =
        h⁻¹ * ∫ x in -h..0, gamma1 x := by
      calc
        _ = ∫ t in (0 : ℝ)..1, (fun u => gamma1 (h*u)) (t-1) := rfl
        _ = ∫ t in (-1 : ℝ)..0, gamma1 (h*t) := by
          simpa using (intervalIntegral.integral_comp_sub_right
            (fun u => gamma1 (h*u)) (a := 0) (b := 1) 1)
        _ = _ := by rw [intervalIntegral.integral_comp_mul_left gamma1 hh.ne']; simp
    rw [hs]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul, ←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (continuous_gamma1.intervalIntegrable _ _) (continuous_gamma1.intervalIntegrable _ _)
  · exact (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_gamma1.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _

lemma totalMass_pos {h : ℝ} (hh : 0 < h) : 0 < totalMass h := by
  unfold totalMass
  apply intervalIntegral.integral_pos
  · norm_num
  · exact (continuous_density h).continuousOn
  · intro x hx
    exact (density_pos hh x).le
  · exact ⟨0, by norm_num, density_pos hh 0⟩

lemma totalMass_le_one {h : ℝ} (hh : 0 < h) : totalMass h ≤ 1 := by
  rw [totalMass_eq_integral hh, intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  rw [←gamma1_int]
  exact setIntegral_le_integral gamma1_integrable (Filter.Eventually.of_forall (fun x => (gamma1_pos x).le))

lemma gamma1_le_inv_sqrt (x : ℝ) : gamma1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  unfold gamma1
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))).mpr
  rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne']
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

lemma density_upper {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    density h t ≤ 2*h/Real.sqrt (2*Real.pi) := by
  have h0 := mul_le_mul_of_nonneg_left (gamma1_le_inv_sqrt (h*t)) hh
  have h1 := mul_le_mul_of_nonneg_left (gamma1_le_inv_sqrt (h*(t-1))) hh
  unfold density
  rw [div_eq_mul_inv]
  nlinarith

lemma density_lower {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 1) :
    h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) ≤ density h t := by
  have hbase {x : ℝ} (hx : |x| ≤ 1/2) :
      h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) ≤ h*gamma1 (h*x) := by
    have hx' := abs_le.mp hx
    have hs : (h*x)^2 ≤ h^2/4 := by
      have hsq : x^2 ≤ 1/4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg h)]
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show -(h^2)/8 ≤ -(h*x)^2/2 by nlinarith))
      (show 0 ≤ h/Real.sqrt (2*Real.pi) by positivity)
    simpa only [gamma1, div_mul_eq_mul_div, mul_div_assoc] using he
  by_cases ht2 : t ≤ 1/2
  · have hz := hbase (abs_le.mpr ⟨by linarith [ht.1],ht2⟩)
    exact hz.trans (le_add_of_nonneg_right (mul_nonneg hh.le (gamma1_pos _).le))
  · have hz := hbase (x := t-1) (abs_le.mpr ⟨by linarith,by linarith [ht.2]⟩)
    exact hz.trans (le_add_of_nonneg_left (mul_nonneg hh.le (gamma1_pos _).le))



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma gaussian_subgaussian : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by simp [mgf_fun_id_gaussianReal]

lemma totalMass_eq_probability {h : ℝ} (hh : 0 < h) :
    totalMass h = (gaussianReal 0 1).real (Ioc (-h) h) := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  rw [totalMass_eq_integral hh, intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => gamma1_eq_gaussianPDF x)


lemma totalMass_tail {h : ℝ} (hh : 0 < h) :
    1-totalMass h ≤ 2*Real.exp (-h^2/2) := by
  rw [totalMass_eq_probability hh]
  have hc : (gaussianReal 0 1).real ((Ioc (-h) h)ᶜ) =
      1-(gaussianReal 0 1).real (Ioc (-h) h) := by
    rw [measureReal_compl measurableSet_Ioc]
    simp
  rw [←hc]
  have hs : (Ioc (-h) h)ᶜ ⊆ {x : ℝ | h ≤ -x} ∪ {x : ℝ | h ≤ x} := by
    intro x hx
    simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr hx.le
  calc
    _ ≤ (gaussianReal 0 1).real ({x : ℝ | h ≤ -x} ∪ {x : ℝ | h ≤ x}) :=
      measureReal_mono hs
    _ ≤ (gaussianReal 0 1).real {x : ℝ | h ≤ -x} +
        (gaussianReal 0 1).real {x : ℝ | h ≤ x} := measureReal_union_le _ _
    _ ≤ _ := by
      have hl := gaussian_subgaussian.neg.measure_ge_le hh.le
      have hr := gaussian_subgaussian.measure_ge_le hh.le
      simp only [Pi.neg_apply, NNReal.coe_one, mul_one] at hl hr
      linarith

lemma gamma1_second_int : ∫ x : ℝ, gamma1 x * x^2 = 1 := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hv
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)] at hv
  simpa only [←gamma1_eq_gaussianPDF, smul_eq_mul] using hv

lemma gamma1_second_integrable : Integrable (fun x : ℝ => gamma1 x*x^2) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
    (s := 2) (by norm_num)).div_const (Real.sqrt (2*Real.pi))
  convert hi using 1
  ext x
  rw [Real.rpow_two]
  unfold gamma1
  rw [show -(x^2)/2 = -(1/2 : ℝ)*x^2 by ring]
  ring



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma integral_fold {φ : ℝ → ℝ} (hφ : Continuous φ) {h : ℝ} (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, h*φ (h*t)+h*φ (h*(t-1))) = ∫ x in -h..h, φ x := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left φ hh.ne']
    have hs : (∫ t in (0 : ℝ)..1, φ (h*(t-1))) = h⁻¹ * ∫ x in -h..0, φ x := by
      calc
        _ = ∫ t in (0 : ℝ)..1, (fun u => φ (h*u)) (t-1) := rfl
        _ = ∫ t in (-1 : ℝ)..0, φ (h*t) := by
          simpa using (intervalIntegral.integral_comp_sub_right
            (fun u => φ (h*u)) (a := 0) (b := 1) 1)
        _ = _ := by rw [intervalIntegral.integral_comp_mul_left φ hh.ne']; simp
    rw [hs]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul, ←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)
  · exact (continuous_const.mul (hφ.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (continuous_const.mul (hφ.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _

lemma continuous_foldMoment (h : ℝ) : Continuous (foldMoment h) := by
  unfold foldMoment
  exact (continuous_const.mul ((continuous_gamma1.comp (continuous_const.mul continuous_id)).mul
    ((continuous_const.mul continuous_id).pow 2))).add
    (continuous_const.mul ((continuous_gamma1.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).mul
      ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2)))

lemma foldMoment_integral_le {h : ℝ} (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, foldMoment h t) ≤ 1 := by
  unfold foldMoment
  rw [integral_fold (φ := fun x => gamma1 x*x^2)
    (continuous_gamma1.mul (continuous_id.pow 2)) hh,
    intervalIntegral.integral_of_le (by linarith : -h ≤ h), ←gamma1_second_int]
  exact setIntegral_le_integral gamma1_second_integrable
    (Filter.Eventually.of_forall (fun x => mul_nonneg (gamma1_pos x).le (sq_nonneg x)))

lemma log_component {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Real.log (h*gamma1 (h*x)) = Real.log h-Real.log (Real.sqrt (2*Real.pi))-(h*x)^2/2 := by
  rw [Real.log_mul hh.ne' (gamma1_pos _).ne', gamma1,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne',
    Real.log_exp]
  ring

lemma entropy_lower_pointwise {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t-foldMoment h t/2 ≤
      density h t*Real.log (density h t) := by
  have hp0 : 0 < h*gamma1 (h*t) := mul_pos hh (gamma1_pos _)
  have hp1 : 0 < h*gamma1 (h*(t-1)) := mul_pos hh (gamma1_pos _)
  have hl0 := Real.log_le_log hp0 (show h*gamma1 (h*t) ≤ density h t by
    unfold density; linarith)
  have hl1 := Real.log_le_log hp1 (show h*gamma1 (h*(t-1)) ≤ density h t by
    unfold density; linarith)
  rw [log_component hh] at hl0 hl1
  have h0 := mul_le_mul_of_nonneg_left hl0 hp0.le
  have h1 := mul_le_mul_of_nonneg_left hl1 hp1.le
  unfold density foldMoment at *
  nlinarith

lemma logMean_upper {h : ℝ} (hh : 0 < h) :
    logMean h ≤ Real.log (2*h/Real.sqrt (2*Real.pi)) := by
  have hc : Continuous (fun t => density h t*Real.log (density h t)) :=
    (continuous_density h).mul ((continuous_density h).log (fun t => (density_pos hh t).ne'))
  have hl : (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t)) ≤
      (∫ t in (0 : ℝ)..1, density h t*Real.log (2*h/Real.sqrt (2*Real.pi))) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
      (((continuous_density h).mul continuous_const).intervalIntegrable _ _)
    intro t ht
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (density_pos hh t)
      (density_upper hh.le t)) (density_pos hh t).le
  rw [intervalIntegral.integral_mul_const] at hl
  exact (div_le_iff₀ (totalMass_pos hh)).mpr (by simpa [mul_comm, totalMass] using hl)

lemma logMean_lower {h : ℝ} (hh : 0 < h) :
    Real.log h-Real.log (Real.sqrt (2*Real.pi))-1/(2*totalMass h) ≤ logMean h := by
  have hc : Continuous (fun t => density h t*Real.log (density h t)) :=
    (continuous_density h).mul ((continuous_density h).log (fun t => (density_pos hh t).ne'))
  have hl : (∫ t in (0 : ℝ)..1,
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t-foldMoment h t/2) ≤
      (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ (hc.intervalIntegrable _ _) ?_
    · exact ((continuous_const.mul (continuous_density h)).sub
        ((continuous_foldMoment h).div_const 2)).intervalIntegrable _ _
    · intro t ht
      exact entropy_lower_pointwise hh t
  have hi₁ : IntervalIntegrable (fun t =>
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t) volume 0 1 :=
    (continuous_const.mul (continuous_density h)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t => foldMoment h t/2) volume 0 1 :=
    ((continuous_foldMoment h).div_const 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hl
  have hm := foldMoment_integral_le hh
  apply (le_div_iff₀ (totalMass_pos hh)).mpr
  have he : (Real.log h-Real.log (Real.sqrt (2*Real.pi))-1/(2*totalMass h))*totalMass h =
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*totalMass h-1/2 := by
    field_simp [(totalMass_pos hh).ne']
  rw [he]
  dsimp [totalMass] at *
  linarith

lemma logMean_lower_of_half {h : ℝ} (hh : 0 < h) (ha : 1/2 ≤ totalMass h) :
    Real.log h-Real.log (Real.sqrt (2*Real.pi))-1 ≤ logMean h := by
  have hi : 1/(2*totalMass h) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith [logMean_lower hh]



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real


lemma measurable_weight (h : ℝ) :
    Measurable (fun t => ENNReal.ofReal (density h t/totalMass h)) :=
  ((continuous_density h).div_const _).measurable.ennreal_ofReal

lemma integral_law {h : ℝ} (hh : 0 < h) (g : ℝ → ℝ) :
    (∫ t, g t ∂law h) = (∫ t in (0 : ℝ)..1, density h t*g t)/totalMass h := by
  unfold law
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_weight h)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (density_pos hh _).le (totalMass_pos hh).le),
    smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div, integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma law_isProbability {h : ℝ} (hh : 0 < h) : IsProbabilityMeasure (law h) := by
  constructor
  unfold law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change ENNReal.ofReal (totalMass h/totalMass h) = 1
    rw [div_self (totalMass_pos hh).ne', ENNReal.ofReal_one]
  · exact ((continuous_density h).div_const _).integrableOn_Icc
  · exact Filter.Eventually.of_forall (fun t =>
      div_nonneg (density_pos hh t).le (totalMass_pos hh).le)

lemma law_ae_mem (h : ℝ) : ∀ᵐ t ∂law h, t ∈ Icc (0 : ℝ) 1 := by
  unfold law
  apply (ae_withDensity_iff (measurable_weight h)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact fun _ => ht

lemma continuous_log_density {h : ℝ} (hh : 0 < h) :
    Continuous (fun t => Real.log (density h t)) :=
  (continuous_density h).log (fun t => (density_pos hh t).ne')

lemma integral_log_density {h : ℝ} (hh : 0 < h) :
    (∫ t, Real.log (density h t) ∂law h) = logMean h := integral_law hh _

lemma log_density_bounds {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 1) :
    Real.log (density h t) ∈ Icc
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2) := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  constructor
  · have hl := Real.log_le_log (x := h/Real.sqrt (2*Real.pi)*Real.exp (-h^2/8))
      (by positivity) (density_lower hh ht)
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_div hh.ne' hs.ne', Real.log_exp] at hl
    linarith
  · have hu := Real.log_le_log (density_pos hh t) (density_upper hh.le t)
    rw [Real.log_div (mul_pos (by norm_num) hh).ne' hs.ne',
      Real.log_mul (by norm_num) hh.ne'] at hu
    linarith

lemma log_density_memLp {h : ℝ} (hh : 0 < h) :
    MemLp (fun t => Real.log (density h t)) 2 (law h) := by
  let := law_isProbability hh
  refine memLp_of_bounded
    (a := Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
    (b := Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2)
    ?_ (continuous_log_density hh).aestronglyMeasurable 2
  filter_upwards [law_ae_mem h] with t ht
  exact log_density_bounds hh ht

lemma log_density_variance {h : ℝ} (hh : 0 < h) :
    Var[fun t => Real.log (density h t); law h] ≤ ((Real.log 2+h^2/8)/2)^2 := by
  let := law_isProbability hh
  have hb : ∀ᵐ t ∂law h, Real.log (density h t) ∈ Icc
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2) := by
    filter_upwards [law_ae_mem h] with t ht
    exact log_density_bounds hh ht
  convert variance_le_sq_of_bounded hb (continuous_log_density hh).measurable.aemeasurable using 1 ; ring



end SingleLatticeCovering.Folded



noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SingleLatticeCovering.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma chebyshev_real [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω-∫ x, X x ∂μ|} ≤ Var[X; μ]/c^2 := by
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hc)
  rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg c))] at ht

variable {ι : Type*} [Fintype ι]

lemma sum_memLp [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    MemLp (fun ω : ι → Ω => ∑ i, X (ω i)) 2 (Measure.pi (fun _ : ι => μ)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    hX.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i))

lemma sum_mean [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) :
    (∫ ω : ι → Ω, ∑ i, X (ω i) ∂Measure.pi (fun _ : ι => μ)) =
      (Fintype.card ι : ℝ)*(∫ x, X x ∂μ) := by
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_comp_eval hX)]
  simp only [integral_comp_eval (μ := fun _ : ι => μ) hX.aestronglyMeasurable, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

lemma sum_variance [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[fun ω : ι → Ω => ∑ i, X (ω i); Measure.pi (fun _ : ι => μ)] =
      (Fintype.card ι : ℝ)*Var[X; μ] := by
  have he : (∑ i, fun ω : ι → Ω => X (ω i)) = (fun ω : ι → Ω => ∑ i, X (ω i)) := by
    ext ω; simp
  rw [←he]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    using (variance_sum_pi (μ := fun _ : ι => μ) (X := fun _ : ι => X) (fun _ => hX))

lemma sum_chebyshev [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {v c : ℝ} (hv : Var[X; μ] ≤ v) (hc : 0 < c) :
    (Measure.pi (fun _ : ι => μ)).real
      {ω | c ≤ |(∑ i, X (ω i))-(Fintype.card ι : ℝ)*(∫ x, X x ∂μ)|} ≤
        (Fintype.card ι : ℝ)*v/c^2 := by
  have ht := chebyshev_real (sum_memLp (ι := ι) hX) hc
  rw [sum_mean (hX.integrable (by norm_num)), sum_variance hX] at ht
  exact ht.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
    (sq_nonneg c))

lemma indicator_variance [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Var[s.indicator (fun _ => (1 : ℝ)); μ] ≤ μ.real s := by
  have hm : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hs
  have ht := variance_le_expectation_sq hm.aestronglyMeasurable
  have he : (fun x => (s.indicator (fun _ => (1 : ℝ)) x)^2) = s.indicator (fun _ => (1 : ℝ)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  change Var[s.indicator (fun _ => (1 : ℝ)); μ] ≤ ∫ x, (s.indicator (fun _ => (1 : ℝ)) x)^2 ∂μ at ht
  rw [he] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

lemma count_lower_tail [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (hp : 0 < (Fintype.card ι : ℝ)*μ.real s) :
    (Measure.pi (fun _ : ι => μ)).real
      {ω | (∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i)) <
        (Fintype.card ι : ℝ)*μ.real s/2} ≤ 4/((Fintype.card ι : ℝ)*μ.real s) := by
  have hm : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hs
  have ht := sum_chebyshev (ι := ι) hm (indicator_variance hs) (half_pos hp)
  simp only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] at ht
  have hsub : {ω : ι → Ω | (∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i)) <
      (Fintype.card ι : ℝ)*μ.real s/2} ⊆
      {ω | (Fintype.card ι : ℝ)*μ.real s/2 ≤
        |(∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i))-(Fintype.card ι : ℝ)*μ.real s|} := by
    intro ω hω
    have hz := le_abs_self (-((∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i))-
      (Fintype.card ι : ℝ)*μ.real s))
    rw [abs_neg] at hz
    dsimp at hω ⊢
    linarith
  have he : (Fintype.card ι : ℝ)*μ.real s/((Fintype.card ι : ℝ)*μ.real s/2)^2 =
      4/((Fintype.card ι : ℝ)*μ.real s) := by field_simp [hp.ne']; ring
  exact (measureReal_mono hsub).trans (ht.trans_eq he)



end SingleLatticeCovering.Concentration


end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Concentration
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma law_real_of_subset {h : ℝ} (hh : 0 < h) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Icc (0 : ℝ) 1) :
    (law h).real s = (∫ t in s, density h t)/totalMass h := by
  calc
    _ = ∫ _ in s, (1 : ℝ) ∂law h := by simp
    _ = ∫ t in s, density h t/totalMass h ∂volume.restrict (Icc (0 : ℝ) 1) := by
      unfold law
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_weight h)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ => (1 : ℝ)) hs]
      simp only [ENNReal.toReal_ofReal (div_nonneg (density_pos hh _).le (totalMass_pos hh).le),
        smul_eq_mul, mul_one]
    _ = _ := by rw [Measure.restrict_restrict hs, inter_eq_left.mpr hsub, integral_div]


lemma centralInterval_subset {h : ℝ} (hh : 1 ≤ h) : centralInterval h ⊆ Icc (0 : ℝ) 1 := by
  have hh2 : 1 ≤ h^2 := by nlinarith
  have hw : 1/(2*h^2) ≤ (1/2 : ℝ) := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)
  intro t ht
  rcases ht with ⟨hl,hu⟩
  constructor <;> linarith

lemma centralInterval_volume {h : ℝ} (hh : 0 < h) :
    volume.real (centralInterval h) = 1/h^2 := by
  unfold centralInterval
  rw [Real.volume_real_Icc]
  have hz : 0 ≤ (1/2+1/(2*h^2))-(1/2-1/(2*h^2)) := by
    have : 0 ≤ 1/(2*h^2) := by positivity
    linarith
  rw [max_eq_left hz]
  ring

lemma centralInterval_probability {h : ℝ} (hh : 1 ≤ h) :
    Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) ≤ (law h).real (centralInterval h) := by
  have hp : 0 < h := by linarith
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have hmin : h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) * volume.real (centralInterval h) ≤
      ∫ t in centralInterval h, density h t := by
    calc
      _ = ∫ _ in centralInterval h, h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) := by simp [mul_comm]
      _ ≤ _ := by
        apply setIntegral_mono_on (integrableOn_const (s := centralInterval h) (hs := isCompact_Icc.measure_ne_top))
          (continuous_density h).integrableOn_Icc measurableSet_Icc
        intro t ht
        exact density_lower hp (centralInterval_subset hh ht)
  rw [centralInterval_volume hp] at hmin
  have he : h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8)*(1/h^2) =
      Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) := by field_simp
  rw [he] at hmin
  rw [law_real_of_subset (s := centralInterval h) hp measurableSet_Icc (centralInterval_subset hh)]
  exact hmin.trans ((le_div_iff₀ (totalMass_pos hp)).mpr
    (mul_le_of_le_one_right (le_trans (by positivity) hmin) (totalMass_le_one hp)))

variable {ι : Type*} [Fintype ι]

lemma log_folded {h : ℝ} (hh : 0 < h) (t : ι → ℝ) :
    Real.log (folded h t) = ∑ i, Real.log (density h (t i)) := by
  exact Real.log_prod (fun i _ => (density_pos hh (t i)).ne')

lemma folded_chebyshev {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | c ≤ |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h|} ≤
      (Fintype.card ι : ℝ)*((Real.log 2+h^2/8)/2)^2/c^2 := by
  let := law_isProbability hh
  have ht := Concentration.sum_chebyshev (ι := ι) (log_density_memLp hh)
    (log_density_variance hh) hc
  simp only [integral_log_density hh] at ht
  simpa only [cubeLaw, log_folded hh] using ht

lemma central_count_tail {h : ℝ} (hh : 1 ≤ h) (hi : 0 < Fintype.card ι)
    {r : ℝ} (hr : 2*r ≤ (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) :
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r} ≤
      4/((Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) := by
  have hp : 0 < h := by linarith
  let := law_isProbability hp
  have hl := mul_le_mul_of_nonneg_left (centralInterval_probability hh) (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  rw [←mul_div_assoc] at hl
  have hx : 0 < (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi)) := by positivity
  have ht := Concentration.count_lower_tail (ι := ι) (μ := law h) (s := centralInterval h) measurableSet_Icc (lt_of_lt_of_le hx hl)
  apply (measureReal_mono (show {t : ι → ℝ | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r} ⊆ _ from ?_)).trans
    (ht.trans (div_le_div_of_nonneg_left (by norm_num) hx hl))
  intro t ht
  dsimp at ht ⊢
  linarith




end SingleLatticeCovering.Folded
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace SingleLatticeCovering
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, SigmaFinite (μ i)]

lemma pi_withDensity_ofReal {f : ∀ i, Ω i → ℝ}
    (hf : ∀ i, Integrable (f i) (μ i)) (hpos : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [←ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i => (hf i).restrict))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hpos i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hpos i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (Filter.Eventually.of_forall (hpos i))


end SingleLatticeCovering

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real
variable {ι : Type*} [Fintype ι]

lemma continuous_folded (h : ℝ) : Continuous (folded h : (ι → ℝ) → ℝ) := by
  unfold folded
  exact continuous_finsetProd _ (fun i _ => (continuous_density h).comp (continuous_apply i))

lemma cubeLaw_density {h : ℝ} (hh : 0 < h) :
    (cubeLaw h : Measure (ι → ℝ)) =
      (volume.restrict cube).withDensity
        (fun t => ENNReal.ofReal (folded h t/(totalMass h)^Fintype.card ι)) := by
  have hf : Integrable (fun x => density h x/totalMass h) (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((continuous_density h).div_const _).integrableOn_Icc
  have ht := pi_withDensity_ofReal (μ := fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))
    (f := fun _ : ι => fun x => density h x/totalMass h) (fun _ => hf)
    (fun _ x => div_nonneg (density_pos hh x).le (totalMass_pos hh).le)
  simpa only [cubeLaw, law, ←Measure.restrict_pi_pi, volume_pi, cube,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, folded] using ht

lemma cube_integral {h : ℝ} (_ : 0 < h) :
    (∫ t in (cube : Set (ι → ℝ)), folded h t) = (totalMass h)^Fintype.card ι := by
  rw [cube, volume_pi, Measure.restrict_pi_pi]
  unfold folded
  rw [integral_fintype_prod_eq_pow, integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

lemma cubeLaw_real {h : ℝ} (hh : 0 < h) {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    (cubeLaw h).real s = (∫ t in s ∩ cube, folded h t)/(totalMass h)^Fintype.card ι := by
  calc
    _ = ∫ _ in s, (1 : ℝ) ∂cubeLaw h := by simp
    _ = ∫ t in s, folded h t/(totalMass h)^Fintype.card ι ∂volume.restrict cube := by
      rw [cubeLaw_density hh, setIntegral_withDensity_eq_setIntegral_toReal_smul
        (((continuous_folded h).div_const _).measurable.ennreal_ofReal)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun _ => (1 : ℝ)) hs]
      simp only [ENNReal.toReal_ofReal (div_nonneg (folded_pos hh _).le (pow_nonneg (totalMass_pos hh).le _)),
        smul_eq_mul, mul_one]
    _ = _ := by rw [Measure.restrict_restrict hs, integral_div]

lemma cubeLaw_isProbability {h : ℝ} (hh : 0 < h) : IsProbabilityMeasure (cubeLaw h : Measure (ι → ℝ)) := by
  let := law_isProbability hh
  change IsProbabilityMeasure (Measure.pi (fun _ : ι => law h))
  infer_instance


lemma continuous_good_mass {h c r : ℝ} (hh : 1 ≤ h) (hi : 0 < Fintype.card ι) (hc : 0 < c)
    (hr : 2*r ≤ (Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) :
    1 - (Fintype.card ι : ℝ)*((Real.log 2+h^2/8)/2)^2/c^2 -
      4/((Fintype.card ι : ℝ)*Real.exp (-(h^2)/8)/(h*Real.sqrt (2*Real.pi))) ≤
    (cubeLaw h : Measure (ι → ℝ)).real
      {t | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
        r ≤ ∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)} := by
  have hp : 0 < h := by linarith
  let := cubeLaw_isProbability (ι := ι) hp
  let A : Set (ι → ℝ) := {t | c ≤ |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h|}
  let B : Set (ι → ℝ) := {t | (∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)) < r}
  have hA : MeasurableSet A := by
    apply measurableSet_le measurable_const
    exact (((continuous_folded h).log (fun t => (folded_pos hp t).ne')).sub continuous_const).abs.measurable
  have hB : MeasurableSet B := by
    apply measurableSet_lt _ measurable_const
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator (show MeasurableSet (centralInterval h) from measurableSet_Icc)).comp (measurable_pi_apply i))
  have he : {t : ι → ℝ | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
        r ≤ ∑ i, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t i)} = (A ∪ B)ᶜ := by
    ext t
    simp only [A, B, mem_ofPred_eq, mem_compl_iff, mem_union, not_or, not_le, not_lt]
  rw [he, measureReal_compl (hA.union hB)]
  have hu := measureReal_union_le (μ := cubeLaw h) A B
  have ha := folded_chebyshev (ι := ι) hp hc
  have hb := central_count_tail (ι := ι) hh hi hr
  change (cubeLaw h).real A ≤ _ at ha
  change (cubeLaw h).real B ≤ _ at hb
  have hu1 : (cubeLaw h : Measure (ι → ℝ)).real Set.univ = 1 := by simp
  rw [hu1]
  linarith



end SingleLatticeCovering.Folded



noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma residue_integerLift {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [NeZero p] (z : ι → ZMod p) :
    residue p (integerLift p z) = z := by
  ext j
  simp only [residue, integerLift, Int.cast_natCast, ZMod.natCast_zmod_val]

lemma cellPoint_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [NeZero p] (C : Submodule (ZMod p) (ι → ZMod p))
    (t : ι → ℝ) (z : ι → ZMod p)
    (hz : residue p (floorVector p t) - z ∈ C) : cellPoint p t z ∈ codeLattice p C := by
  refine ⟨floorVector p t - integerLift p z, ?_, rfl⟩
  convert hz using 1
  ext j
  simp [residue, integerLift]

lemma cell_residual {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (t : ι → ℝ) (z : ι → ZMod p) (j : ι) :
    (t-cellPoint p t z) j = ((z j).val + Int.fract ((p : ℝ)*t j))/(p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hf := Int.floor_add_fract ((p : ℝ)*t j)
  simp only [Pi.sub_apply, cellPoint, generator, floorVector, integerLift, Int.cast_sub,
    Int.cast_natCast]
  apply (eq_div_iff hp0).mpr
  field_simp
  nlinarith [Int.floor_add_fract (t j*(p : ℝ))]

lemma cell_residual_mem_grid (p : ℕ) (hp : 0 < p) (t : ι → ℝ) (z : ι → ZMod p) :
    t-cellPoint p t z ∈ gridCell p z := by
  intro j
  rw [cell_residual p hp t z j]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  change 0 ≤ ((z j).val+Int.fract ((p : ℝ)*t j))/(p : ℝ)-(z j).val/(p : ℝ) ∧
    ((z j).val+Int.fract ((p : ℝ)*t j))/(p : ℝ)-(z j).val/(p : ℝ) < (p : ℝ)⁻¹
  rw [add_div, add_sub_cancel_left]
  constructor
  · exact div_nonneg (Int.fract_nonneg _) hp0.le
  · simpa only [one_div] using (div_lt_div_of_pos_right (Int.fract_lt_one _) hp0)

lemma gridCell_subset_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (τ : ι → ℝ)
    (hτ : τ ∈ gridCell p z) (j : ι) : τ j ∈ Set.Ico 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hj := hτ j
  change 0 ≤ τ j - (z j).val/(p : ℝ) ∧ τ j - (z j).val/(p : ℝ) < (p : ℝ)⁻¹ at hj
  have hv : ((z j).val : ℝ)+1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (ZMod.val_lt _)
  have h0 : 0 ≤ ((z j).val : ℝ)/(p : ℝ) := div_nonneg (Nat.cast_nonneg _) hp0.le
  have hl : ((z j).val : ℝ)/(p : ℝ) + (p : ℝ)⁻¹ ≤ 1 := by
    rw [← one_div, ← add_div, div_le_one hp0]
    exact hv
  exact ⟨by linarith, by linarith⟩

lemma integer_code_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (C : Submodule (ZMod p) (ι → ZMod p))
    (k : ι → ℤ) : (fun j => (k j : ℝ)) ∈ codeLattice p C := by
  refine ⟨fun j => (p : ℤ)*k j, ?_, ?_⟩
  · have he : residue p (fun j => (p : ℤ)*k j) = 0 := by ext; simp [residue]
    rw [he]; exact C.zero_mem
  · ext j
    simp [generator, show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne']

lemma cell_bits (p : ℕ) (hp : 0 < p) (C : Submodule (ZMod p) (ι → ZMod p))
    (t : ι → ℝ) (z : ι → ZMod p)
    (hz : residue p (floorVector p t) - z ∈ C) (e : ι → Bool) :
    cellPoint p t z + (fun j => if e j then (1 : ℝ) else 0) ∈ codeLattice p C ∧
      ∀ j, (t j - cellPoint p t z j - (if e j then (1 : ℝ) else 0)) ∈ Set.Icc (-1) 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  refine ⟨(codeLattice p C).add_mem (cellPoint_mem p C t z hz) ?_, ?_⟩
  · convert integer_code_mem p hp C (fun j => if e j then (1 : ℤ) else 0) using 1
    ext j
    cases e j <;> simp
  · intro j
    have hj := gridCell_subset_cube p hp z _ (cell_residual_mem_grid p hp t z) j
    simp only [Pi.sub_apply, Set.mem_Ico] at hj
    cases e j <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, Set.mem_Icc] <;>
      constructor <;> linarith


end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridCell_eq_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (z : ι → ZMod p) :
    gridCell p z = Set.univ.pi (fun j => Ico (anchor p z j) (anchor p z j+(p : ℝ)⁻¹)) := by
  ext t
  simp only [gridCell, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ico]
  constructor <;> intro ht j <;> have hj := ht j <;> constructor <;> linarith

lemma gridCell_measurable (p : ℕ) (z : ι → ZMod p) : MeasurableSet (gridCell p z) := by
  rw [gridCell_eq_pi]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

lemma floorVector_gridCell {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p) {z : ι → ZMod p} {t : ι → ℝ}
    (ht : t ∈ gridCell p z) : floorVector p t = integerLift p z := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  ext j
  apply Int.floor_eq_iff.mpr
  have hj := ht j
  change 0 ≤ t j-(z j).val/(p : ℝ) ∧ t j-(z j).val/(p : ℝ) < (p : ℝ)⁻¹ at hj
  have h1 := mul_le_mul_of_nonneg_left hj.1 hp0.le
  have h2 := mul_lt_mul_of_pos_left hj.2 hp0
  simp only [mul_sub, mul_div_cancel₀ _ hp0.ne', mul_inv_cancel₀ hp0.ne', mul_zero] at h1 h2
  change ((z j).val : ℝ) ≤ (p : ℝ)*t j ∧ (p : ℝ)*t j < (z j).val+1
  constructor <;> linarith

lemma gridCell_disjoint {p : ℕ} (hp : 0 < p) {z w : ι → ZMod p} (hzw : z ≠ w) :
    Disjoint (gridCell p z) (gridCell p w) := by
  let : NeZero p := ⟨hp.ne'⟩
  apply Set.disjoint_left.mpr
  intro t hz hw
  have he := (floorVector_gridCell hp hz).symm.trans (floorVector_gridCell hp hw)
  have he' := congr_arg (residue p) he
  simp only [residue_integerLift] at he'
  exact hzw he'

lemma anchor_floorVector {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p) {t : ι → ℝ}
    (ht : ∀ j, t j ∈ Ico 0 1) (j : ι) :
    anchor p (residue p (floorVector p t)) j = (⌊(p : ℝ)*t j⌋ : ℝ)/(p : ℝ) := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h0 : 0 ≤ ⌊(p : ℝ)*t j⌋ := Int.floor_nonneg.mpr (mul_nonneg hp0.le (ht j).1)
  have h1 : ⌊(p : ℝ)*t j⌋ < (p : ℤ) := Int.floor_lt.mpr (by simpa only [Int.cast_natCast, mul_one] using (mul_lt_mul_of_pos_left (ht j).2 hp0))
  have he := ZMod.val_intCast (n := p) (a := ⌊(p : ℝ)*t j⌋)
  rw [Int.emod_eq_of_lt h0 h1] at he
  unfold anchor residue floorVector
  congr 1
  exact_mod_cast he

lemma cube_mem_gridCell {p : ℕ} (hp : 0 < p) {t : ι → ℝ} (ht : ∀ j, t j ∈ Ico 0 1) :
    t ∈ gridCell p (residue p (floorVector p t)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  intro j
  rw [anchor_floorVector hp ht]
  have h0 := Int.floor_le ((p : ℝ)*t j)
  have h1 := Int.lt_floor_add_one ((p : ℝ)*t j)
  constructor
  · rw [sub_nonneg, div_le_iff₀ hp0]
    nlinarith
  · rw [sub_lt_iff_lt_add, ← one_div, ← add_div, lt_div_iff₀ hp0]
    nlinarith

lemma gridCell_iUnion {p : ℕ} (hp : 0 < p) :
    (⋃ z : ι → ZMod p, gridCell p z) = Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_univ_pi]
  constructor
  · rintro ⟨z, ht⟩ j
    exact gridCell_subset_cube p hp z t ht j
  · intro ht
    exact ⟨_, cube_mem_gridCell hp ht⟩

lemma gridCell_volume (p : ℕ) (z : ι → ZMod p) :
    volume (gridCell p z) = (ENNReal.ofReal ((p : ℝ)⁻¹))^Fintype.card ι := by
  rw [gridCell_eq_pi, volume_pi_pi]
  simp only [Real.volume_Ico, add_sub_cancel_left, Finset.prod_const, Finset.card_univ]

lemma gridCell_volume_real (p : ℕ) (z : ι → ZMod p) :
    volume.real (gridCell p z) = ((p : ℝ)⁻¹)^Fintype.card ι := by
  rw [Measure.real, gridCell_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal]
  positivity

lemma integral_gridCells {p : ℕ} [NeZero p] (hp : 0 < p) {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) :
    (∫ t in Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1), f t) =
      ∑ z : ι → ZMod p, ∫ t in gridCell p z, f t := by
  let : NeZero p := ⟨hp.ne'⟩
  have hi : IsCompact (Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hf' z : IntegrableOn f (gridCell p z) :=
    (hf.continuousOn.integrableOn_compact hi).mono_set (by
      intro t ht
      exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt))
  have he : Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) =ᵐ[volume]
      Set.univ.pi (fun _ : ι => Icc (0 : ℝ) 1) := by
    rw [volume_pi]
    exact Measure.pi_Ico_ae_eq_pi_Icc
  rw [←setIntegral_congr_set he, ←gridCell_iUnion hp]
  exact integral_iUnion_fintype (gridCell_measurable p)
    (fun _ _ hz => gridCell_disjoint hp hz) hf'


end SingleLatticeCovering.ConstructionA


end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Rounding
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι]

lemma square_difference_le {x y δ : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hd : |x-y| ≤ δ) : y^2-x^2 ≤ 2*δ := by
  have hsum : |y+x| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hdiff : |y-x| ≤ δ := by simpa only [abs_sub_comm] using hd
  calc
    _ = (y-x)*(y+x) := by ring
    _ ≤ |(y-x)*(y+x)| := le_abs_self _
    _ = |y-x| * |y+x| := abs_mul _ _
    _ ≤ δ*2 := mul_le_mul hdiff hsum (abs_nonneg _) (le_trans (abs_nonneg _) hdiff)
    _ = _ := by ring

lemma gamma1_rounding_upper (h : ℝ) {x y δ : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hd : |x-y| ≤ δ) : gamma1 (h*x) ≤ exp (h^2*δ)*gamma1 (h*y) := by
  have hs := mul_le_mul_of_nonneg_left (square_difference_le hx hy hd) (sq_nonneg h)
  have he : -(h*x)^2/2 ≤ h^2*δ + -(h*y)^2/2 := by nlinarith
  unfold gamma1
  rw [← mul_div_assoc, ← Real.exp_add]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) (Real.sqrt_nonneg _)

lemma abs_sub_bitValue {t : ℝ} (ht : t ∈ Set.Icc 0 1) (e : Bool) :
    |t-bitValue e| ≤ 1 := by
  apply abs_le.mpr
  cases e <;> simp only [bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero] <;>
    constructor <;> linarith [ht.1, ht.2]

lemma density_rounding_upper {h s t δ : ℝ} (hh : 0 < h)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) (hd : |t-s| ≤ δ) :
    density h t ≤ exp (h^2*δ)*density h s := by
  have h0 := gamma1_rounding_upper h (abs_sub_bitValue ht false)
    (abs_sub_bitValue hs false) (show |(t-bitValue false)-(s-bitValue false)| ≤ δ by simpa using hd)
  have h1 := gamma1_rounding_upper h (abs_sub_bitValue ht true)
    (abs_sub_bitValue hs true) (show |(t-bitValue true)-(s-bitValue true)| ≤ δ by
      simpa only [sub_sub_sub_cancel_right] using hd)
  simp only [bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero] at h0 h1
  have h0' := mul_le_mul_of_nonneg_left h0 hh.le
  have h1' := mul_le_mul_of_nonneg_left h1 hh.le
  unfold density
  nlinarith

lemma product_rounding {f g : ι → ℝ} (hf : ∀ j, 0 ≤ f j) (r : ℝ)
    (hfg : ∀ j, f j ≤ exp r*g j) :
    (∏ j, f j) ≤ exp ((Fintype.card ι : ℝ)*r)*(∏ j, g j) := by
  calc
    _ ≤ ∏ j, exp r*g j := Finset.prod_le_prod (fun j _ => hf j) (fun j _ => hfg j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp

lemma folded_rounding_upper {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    folded h t ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*folded h s := by
  simpa only [folded, mul_assoc] using product_rounding
    (fun j => (density_pos hh (t j)).le) (h^2*δ)
    (fun j => density_rounding_upper hh (hs j) (ht j) (hd j))

lemma atom_eq_product (h : ℝ) (t : ι → ℝ) (e : ι → Bool) :
    atom h t e = ∏ j, h*gamma1 (h*(t j-bitValue (e j))) := by
  simp [atom, gamma, Finset.prod_mul_distrib]

lemma atom_rounding_upper {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ) (e : ι → Bool)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    atom h t e ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*atom h s e := by
  rw [atom_eq_product, atom_eq_product]
  have hj (j : ι) : h*gamma1 (h*(t j-bitValue (e j))) ≤
      exp (h^2*δ)*(h*gamma1 (h*(s j-bitValue (e j)))) := by
    have hg := gamma1_rounding_upper h (abs_sub_bitValue (ht j) (e j))
      (abs_sub_bitValue (hs j) (e j))
      (show |(t j-bitValue (e j))-(s j-bitValue (e j))| ≤ δ by
        simpa only [sub_sub_sub_cancel_right] using hd j)
    nlinarith [mul_le_mul_of_nonneg_left hg hh.le]
  simpa only [mul_assoc] using product_rounding
    (fun j => mul_nonneg hh.le (gamma1_pos _).le) (h^2*δ) hj

lemma remove_exp_factor {a b η : ℝ} (h : b ≤ exp η*a) : exp (-η)*b ≤ a := by
  calc
    _ ≤ exp (-η)*(exp η*a) := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp



theorem rounding {h δ : ℝ} (hh : 0 < h) (s t : ι → ℝ) (e : ι → Bool)
    (hs : ∀ j, s j ∈ Set.Icc 0 1) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hd : ∀ j, |t j-s j| ≤ δ) :
    exp (-((Fintype.card ι : ℝ)*h^2*δ))*folded h s ≤ folded h t ∧
    folded h t ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*folded h s ∧
    exp (-((Fintype.card ι : ℝ)*h^2*δ))*(folded h s*wordMass h s e) ≤ atom h t e ∧
    atom h t e ≤ exp ((Fintype.card ι : ℝ)*h^2*δ)*(folded h s*wordMass h s e) := by
  have hd' (j : ι) : |s j-t j| ≤ δ := by simpa only [abs_sub_comm] using hd j
  refine ⟨remove_exp_factor (folded_rounding_upper hh t s ht hs hd'),
    folded_rounding_upper hh s t hs ht hd, ?_, ?_⟩
  · rw [← folded_identity hh]
    exact remove_exp_factor (atom_rounding_upper hh t s e ht hs hd')
  · rw [← folded_identity hh]
    exact atom_rounding_upper hh s t e hs ht hd


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma grid_anchor_mem_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (j : ι) :
    anchor p z j ∈ Set.Icc 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp0.le, ?_⟩
  apply (div_le_one hp0).mpr
  exact_mod_cast (ZMod.val_lt (z j)).le

lemma grid_distance {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {z : ι → ZMod p} {t : ι → ℝ} (ht : t ∈ gridCell p z) (j : ι) :
    |t j-anchor p z j| ≤ (p : ℝ)⁻¹ := by
  rw [abs_of_nonneg (ht j).1]
  exact (ht j).2.le

lemma grid_folded_integrable (h : ℝ) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    IntegrableOn (folded h) (gridCell p z) := by
  apply ((continuous_folded h).continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc) : IsCompact (cube : Set (ι → ℝ)))).mono_set
  intro t ht
  exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt)

lemma grid_integral_upper {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    (∫ t in gridCell p z, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι := by
  have hfin : volume (gridCell p z) ≠ ⊤ := by rw [gridCell_volume]; finiteness
  calc
    _ ≤ ∫ _ in gridCell p z, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z) := by
      apply setIntegral_mono_on (grid_folded_integrable h p hp z) (integrableOn_const hfin) (gridCell_measurable p z)
      intro t ht
      exact folded_rounding_upper hh _ _ (grid_anchor_mem_cube p hp z)
        (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_distance ht)
    _ = _ := by simp [gridCell_volume_real, mul_comm]

lemma grid_integral_lower {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) :
    Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι ≤
      (∫ t in gridCell p z, folded h t) := by
  have hfin : volume (gridCell p z) ≠ ⊤ := by rw [gridCell_volume]; finiteness
  calc
    _ = ∫ _ in gridCell p z, Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z) := by
      simp [gridCell_volume_real, mul_comm]
    _ ≤ _ := by
      apply setIntegral_mono_on (integrableOn_const hfin) (grid_folded_integrable h p hp z) (gridCell_measurable p z)
      intro t ht
      apply remove_exp_factor
      exact folded_rounding_upper hh _ _
        (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_anchor_mem_cube p hp z)
        (fun j => by rw [abs_sub_comm]; exact grid_distance ht j)


lemma grid_integral_total {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p) :
    Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*gridMass (ι := ι) h p Finset.univ ≤ (totalMass h)^Fintype.card ι ∧
    (totalMass h)^Fintype.card ι ≤ Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass (ι := ι) h p Finset.univ := by
  have he : (totalMass h)^Fintype.card ι =
      ∑ z : ι → ZMod p, ∫ t in gridCell p z, folded h t :=
    (cube_integral (ι := ι) hh).symm.trans (integral_gridCells hp (continuous_folded h))
  simp only [he]
  constructor
  · calc
      _ = ∑ z : ι → ZMod p, Real.exp (-((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹))*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι := by
        simp only [gridMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun z _ => grid_integral_lower hh p hp z)
  · calc
      _ ≤ ∑ z : ι → ZMod p, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι :=
        Finset.sum_le_sum (fun z _ => grid_integral_upper hh p hp z)
      _ = _ := by
        simp only [gridMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma halfCube_ae_cube {ι : Type*} [Fintype ι] [DecidableEq ι] : Set.univ.pi (fun _ : ι => Ico (0 : ℝ) 1) =ᵐ[volume] (cube : Set (ι → ℝ)) := by
  rw [volume_pi]
  exact Measure.pi_Ico_ae_eq_pi_Icc

lemma grid_selected_integral {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) :
    (∫ t in ⋃ z ∈ E, gridCell p z, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass h p E := by
  rw [integral_biUnion_finset E (fun z _ => gridCell_measurable p z)
    (fun z _ w _ hzw => gridCell_disjoint hp hzw) (fun z _ => grid_folded_integrable h p hp z)]
  calc
    _ ≤ ∑ z ∈ E, Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*folded h (anchor p z)*((p : ℝ)⁻¹)^Fintype.card ι :=
      Finset.sum_le_sum (fun z _ => grid_integral_upper hh p hp z)
    _ = _ := by
      simp only [gridMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

lemma grid_integral_event {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) (G : Set (ι → ℝ))
    (hG : ∀ t ∈ G, (∀ j, t j ∈ Ico 0 1) → residue p (floorVector p t) ∈ E) :
    (∫ t in G ∩ cube, folded h t) ≤
      Real.exp ((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹)*gridMass h p E := by
  have hi : IntegrableOn (folded h) (⋃ z ∈ E, gridCell p z) := by
    apply ((continuous_folded h).continuousOn.integrableOn_compact
      (isCompact_univ_pi (fun _ => isCompact_Icc) : IsCompact (cube : Set (ι → ℝ)))).mono_set
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨z,ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨hz,ht⟩
    exact Set.mem_univ_pi.mpr (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt)
  apply (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun t => (folded_pos hh t).le)) ?_).trans
    (grid_selected_integral hh p hp E)
  filter_upwards [halfCube_ae_cube (ι := ι)] with t ht
  intro htg
  have hc : ∀ j, t j ∈ Ico 0 1 := Set.mem_univ_pi.mp (ht.mpr htg.2)
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hG t htg.1 hc, cube_mem_gridCell hp hc⟩⟩

lemma log_folded_grid_distance {h : ℝ} (hh : 0 < h) (p : ℕ) (hp : 0 < p)
    {z : ι → ZMod p} {t : ι → ℝ} (ht : t ∈ gridCell p z) :
    |Real.log (folded h t)-Real.log (folded h (anchor p z))| ≤
      (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ := by
  have hu := folded_rounding_upper hh (anchor p z) t (grid_anchor_mem_cube p hp z)
    (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_distance ht)
  have hl := folded_rounding_upper hh t (anchor p z)
    (fun j => (gridCell_subset_cube p hp z t ht j).imp_right le_of_lt) (grid_anchor_mem_cube p hp z)
    (fun j => by rw [abs_sub_comm]; exact grid_distance ht j)
  have hu' := Real.log_le_log (folded_pos hh t) hu
  have hl' := Real.log_le_log (folded_pos hh (anchor p z)) hl
  rw [Real.log_mul (Real.exp_ne_zero _) (folded_pos hh _).ne', Real.log_exp] at hu' hl'
  exact abs_le.mpr ⟨by linarith,by linarith⟩


lemma round_into_eligible {h c r : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p] (hp : 0 < p)
    (hη : (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ ≤ c)
    (hw : (p : ℝ)⁻¹ ≤ 1/(2*h^2)) {t : ι → ℝ} (ht : ∀ j, t j ∈ Ico 0 1)
    (hg : |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
      r ≤ ∑ j, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t j)) :
    residue p (floorVector p t) ∈ gridEligible h (logMean h) (2*c) r p := by
  classical
  let z := residue p (floorVector p t)
  have hc := cube_mem_gridCell hp ht
  change z ∈ _
  simp only [gridEligible, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · have hd := log_folded_grid_distance hh p hp hc
    have htr := abs_add_le (Real.log (folded h (anchor p z))-Real.log (folded h t))
      (Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h)
    rw [sub_add_sub_cancel, abs_sub_comm (Real.log (folded h (anchor p z))) (Real.log (folded h t))] at htr
    linarith
  · apply hg.2.trans
    have he : ((Finset.univ.filter fun j => |anchor p z j-1/2| ≤ (h^2)⁻¹).card : ℝ) =
        ∑ j, if |anchor p z j-1/2| ≤ (h^2)⁻¹ then (1 : ℝ) else 0 := by
      simp only [←Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [he]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : t j ∈ centralInterval h
    · have hti : |t j-1/2| ≤ 1/(2*h^2) := abs_le.mpr ⟨by linarith [hj.1],by linarith [hj.2]⟩
      have hd := grid_distance hc j
      have hz : |anchor p z j-1/2| ≤ (h^2)⁻¹ := by
        have ha := abs_add_le (anchor p z j-t j) (t j-1/2)
        rw [sub_add_sub_cancel, abs_sub_comm (anchor p z j) (t j)] at ha
        have he : 1/(2*h^2)+1/(2*h^2) = (h^2)⁻¹ := by field_simp; ring
        linarith
      simp only [Set.indicator_of_mem hj, ite_eq_left hz, le_refl]
    · simp only [Set.indicator_of_notMem hj]
      split_ifs <;> norm_num


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridMass_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (p : ℕ) [NeZero p]
    {E F : Finset (ι → ZMod p)} (hEF : E ⊆ F) : gridMass h p E ≤ gridMass h p F := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hEF (fun _ _ _ => (folded_pos hh _).le))
  positivity

lemma exp_small_upper {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1/2) : Real.exp η ≤ 1+2*η := by
  apply (Real.exp_bound_div_one_sub_of_interval hη (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-η)).mpr
  nlinarith

lemma grid_from_continuous {h A B : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℕ) [NeZero p] (hp : 0 < p)
    (E : Finset (ι → ZMod p)) (G : Set (ι → ℝ)) (hG : MeasurableSet G)
    (hRound : ∀ t ∈ G, (∀ j, t j ∈ Ico 0 1) → residue p (floorVector p t) ∈ E)
    (ha : 1-(totalMass h)^Fintype.card ι ≤ A)
    (hg : 1-B ≤ (cubeLaw h : Measure (ι → ℝ)).real G)
    (hη : (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ ≤ 1/2) :
    |gridMass (ι := ι) h p Finset.univ-1| ≤ A+2*((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹) ∧
    |gridMass h p E-1| ≤ A+B+2*((Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹) := by
  let η := (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹
  let a := (totalMass h)^Fintype.card ι
  let q := (cubeLaw h : Measure (ι → ℝ)).real G
  change _ ≤ A+2*η ∧ _ ≤ A+B+2*η
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/2 := hη
  have ha0 : 0 ≤ a := pow_nonneg (totalMass_pos hh).le _
  have ha1 : a ≤ 1 := by simpa using pow_le_pow_left₀ (totalMass_pos hh).le (totalMass_le_one hh) (Fintype.card ι)
  let := cubeLaw_isProbability (ι := ι) hh
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := measureReal_le_one
  have haq0 : 0 ≤ a*q := mul_nonneg ha0 hq0
  have haq1 : a*q ≤ 1 := (mul_le_mul_of_nonneg_right ha1 hq0).trans (by simpa using hq1)
  have haq : 1-A-B ≤ a*q := by
    have ht := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hq1)
    change 1-a ≤ A at ha
    change 1-B ≤ q at hg
    nlinarith
  have hexp : 1-η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
  have htot := grid_integral_total (ι := ι) hh p hp
  have htu : gridMass (ι := ι) h p Finset.univ ≤ 1+2*η := by
    calc
      _ = Real.exp η*(Real.exp (-η)*gridMass (ι := ι) h p Finset.univ) := by rw [←mul_assoc,←Real.exp_add]; simp
      _ ≤ Real.exp η*a := mul_le_mul_of_nonneg_left htot.1 (Real.exp_pos _).le
      _ ≤ Real.exp η := mul_le_of_le_one_right (Real.exp_pos _).le ha1
      _ ≤ _ := exp_small_upper hη0 hη1
  have htl : 1-A-η ≤ gridMass (ι := ι) h p Finset.univ := by
    have ht := remove_exp_factor htot.2
    have ht' := mul_le_mul_of_nonneg_right hexp ha0
    change 1-a ≤ A at ha
    have hn := mul_nonneg hη0 (sub_nonneg.mpr ha1)
    nlinarith
  have hge : a*q = ∫ t in G ∩ cube, folded h t := by
    dsimp [a,q]
    rw [cubeLaw_real hh hG]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ (totalMass_pos hh).ne')]
  have hgl : 1-A-B-η ≤ gridMass h p E := by
    have ht := remove_exp_factor (grid_integral_event hh p hp E G hRound)
    rw [←hge] at ht
    have ht' := mul_le_mul_of_nonneg_right hexp haq0
    have hn := mul_nonneg hη0 (sub_nonneg.mpr haq1)
    nlinarith
  have hgu := (gridMass_mono hh p (Finset.subset_univ E)).trans htu
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith


lemma continuousGood_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] {h c r : ℝ} (hh : 0 < h) :
    MeasurableSet (continuousGood (ι := ι) h c r) := by
  have hc : Measurable (fun t : ι → ℝ => ∑ j, (centralInterval h).indicator
      (fun _ => (1 : ℝ)) (t j)) := by
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_const.indicator (show MeasurableSet (centralInterval h) from measurableSet_Icc)).comp (measurable_pi_apply j))
  exact (measurableSet_lt (((continuous_folded h).log (fun t => (folded_pos hh t).ne')).sub continuous_const).abs.measurable
    measurable_const).inter (measurableSet_le measurable_const hc)


end SingleLatticeCovering.Folded





noncomputable section
open Real Filter Topology
namespace SingleLatticeCovering.Folded

lemma prime_in_log_interval {s r : ℝ} (hs : 0 ≤ s) (hr : Real.log 4 ≤ r) :
    ∃ p : ℕ, p.Prime ∧ s ≤ Real.log p ∧ Real.log p ≤ s+r := by
  have he : 1 ≤ Real.exp s := Real.one_le_exp_iff.mpr hs
  have hn : 0 < ⌈Real.exp s⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  obtain ⟨p,hp,hpl,hpu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈Real.exp s⌉₊ hn.ne'
  have hpl' : Real.exp s ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpl.le)
  have hpu' : (p : ℝ) ≤ 4*Real.exp s := by
    have h := Nat.ceil_lt_add_one (Real.exp_pos s).le
    have h' : (p : ℝ) ≤ 2*(⌈Real.exp s⌉₊ : ℝ) := by exact_mod_cast hpu
    linarith
  have h4 : (4 : ℝ) ≤ Real.exp r := (Real.log_le_iff_le_exp (by norm_num)).mp hr
  refine ⟨p,hp,(Real.le_log_iff_exp_le (by exact_mod_cast hp.pos)).mpr hpl',?_⟩
  apply (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mpr
  calc
    _ ≤ 4*Real.exp s := hpu'
    _ ≤ Real.exp r*Real.exp s := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add, add_comm]


theorem block_prime {b μ : ℝ} (_ : 0 < b)
    (hμ : 4*b^(56/100 : ℝ) ≤ b*μ) (hr : Real.log 4 ≤ b^(56/100 : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ b*μ-4*b^(56/100 : ℝ) ≤ Real.log p ∧
      Real.log p ≤ b*μ-3*b^(56/100 : ℝ) := by
  obtain ⟨p,hp,hl,hu⟩ := prime_in_log_interval (sub_nonneg.mpr hμ) hr
  refine ⟨p,hp,hl,?_⟩
  linarith [hu]



theorem eventually_block_prime {μ : ℝ → ℝ} (hμ : Tendsto μ atTop atTop) :
    ∀ᶠ b : ℝ in atTop, ∃ p : ℕ, p.Prime ∧
      b*μ b-4*b^(56/100 : ℝ) ≤ Real.log p ∧
      Real.log p ≤ b*μ b-3*b^(56/100 : ℝ) := by
  have hpow : ∀ᶠ b : ℝ in atTop, 4*b^(56/100 : ℝ) ≤ b := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 44/100)).const_mul (4 : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (4 : ℝ)*0 < 1)),
      eventually_gt_atTop (0 : ℝ)] with b hb hb0
    have hh : b^(-(44/100 : ℝ)) = b^(56/100 : ℝ)/b := by
      calc
        _ = b^((56/100 : ℝ)-1) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_sub hb0, Real.rpow_one]
    rw [hh] at hb
    have hbb : 4*b^(56/100 : ℝ)/b < 1 := by simpa only [mul_div_assoc] using hb
    exact (by nlinarith [(div_lt_iff₀ hb0).mp hbb])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hμ.eventually (eventually_ge_atTop (1 : ℝ)),
    hpow, (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 56/100)).eventually
      (eventually_ge_atTop (Real.log 4))] with b hb hμb hpb hr
  exact block_prime hb (hpb.trans (by nlinarith)) hr



end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_totalMass_half : ∀ᶠ h : ℝ in atTop, 1/2 ≤ totalMass h := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2*Real.log 4)] with h hh hl
  have hp : 0 < h := by linarith
  have he : Real.exp (-(h^2)/2) ≤ (1/4 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  linarith [totalMass_tail hp]

lemma logMean_tendsto : Tendsto logMean atTop atTop := by
  have hl : Tendsto (fun h : ℝ => Real.log h + (-Real.log (Real.sqrt (2*Real.pi))-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ Real.tendsto_log_atTop
  apply tendsto_atTop_mono' _ _ hl
  filter_upwards [eventually_totalMass_half, eventually_gt_atTop (0 : ℝ)] with h ha hh
  have hb := logMean_lower_of_half hh ha
  linarith



lemma heightR_tendsto : Tendsto heightR atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 9/4) Real.tendsto_log_atTop)

lemma height_tendsto : Tendsto height atTop atTop :=
  heightR_tendsto.comp tendsto_natCast_atTop_atTop

lemma heightR_sq {b : ℝ} (hb : 1 ≤ b) : heightR b^2 = (9/4 : ℝ)*Real.log b :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg hb))

lemma heightR_pos {b : ℝ} (hb : 1 < b) : 0 < heightR b :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.log_pos hb))

lemma heightR_exp {b : ℝ} (hb : 1 ≤ b) (c : ℝ) :
    Real.exp (-(heightR b^2)*c) = b^(-(9/4 : ℝ)*c) := by
  rw [heightR_sq hb, Real.rpow_def_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb)]
  congr 1
  ring

lemma totalMass_power_loss {h : ℝ} (hh : 0 < h) (b : ℕ) :
    0 ≤ 1-(totalMass h)^b ∧ 1-(totalMass h)^b ≤ 2*(b : ℝ)*Real.exp (-(h^2)/2) := by
  have ha := totalMass_pos hh
  have hu := totalMass_le_one hh
  have hp := pow_le_pow_left₀ ha.le hu b
  have hb := one_add_mul_le_pow (a := totalMass h-1) (by linarith : -2 ≤ totalMass h-1) b
  simp only [add_sub_cancel] at hb
  have ht := mul_le_mul_of_nonneg_left (totalMass_tail hh) (Nat.cast_nonneg b : (0 : ℝ) ≤ _)
  simp only [one_pow] at hp
  constructor <;> nlinarith

lemma height_totalMass_power_loss {b : ℕ} (hb : 2 ≤ b) :
    0 ≤ 1-(totalMass (height b))^b ∧
      1-(totalMass (height b))^b ≤ 2*(b : ℝ)^(-(1/8 : ℝ)) := by
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hh : 0 < height b := heightR_pos (by exact_mod_cast (show 1 < b by omega))
  have ht := totalMass_power_loss hh b
  have he : Real.exp (-(height b^2)/2) = (b : ℝ)^(-(9/8 : ℝ)) := by
    calc
      _ = Real.exp (-(heightR (b : ℝ)^2)*(1/2)) := by change Real.exp (-(heightR (b : ℝ)^2)/2) = _; congr 1; ring
      _ = (b : ℝ)^(-(9/4 : ℝ)*(1/2)) := heightR_exp hb1 (1/2)
      _ = _ := by norm_num
  rw [he] at ht
  have hm : (b : ℝ)*(b : ℝ)^(-(9/8 : ℝ)) = (b : ℝ)^(-(1/8 : ℝ)) := by
    calc
      _ = (b : ℝ)^(1 : ℝ)*(b : ℝ)^(-(9/8 : ℝ)) := by rw [Real.rpow_one]
      _ = (b : ℝ)^((1 : ℝ)-(9/8 : ℝ)) := by rw [sub_eq_add_neg, Real.rpow_add hb0]
      _ = _ := by norm_num
  exact ⟨ht.1, by simpa only [mul_assoc, hm] using ht.2⟩

lemma eventually_height_prime : ∀ᶠ b : ℕ in atTop, ∃ p : ℕ, p.Prime ∧
    (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p ∧
    Real.log p ≤ (b : ℝ)*logMean (height b)-3*(b : ℝ)^(56/100 : ℝ) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_block_prime (logMean_tendsto.comp heightR_tendsto))




end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_logpow_bound {s c : ℝ} (r : ℝ) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, (Real.log b)^r ≤ c*b^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r hs).bound hc,
    eventually_ge_atTop (1 : ℝ)] with b hb hb1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hb1) _),
    abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) hb1) _)] using hb

lemma eventually_height_bound {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, heightR b ≤ c*b^s := by
  filter_upwards [eventually_logpow_bound (1 : ℝ) hs (div_pos hc (by norm_num : (0 : ℝ) < 3/2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with b hb hl
  rw [Real.rpow_one] at hb
  have hsqrt : heightR b ≤ (3/2 : ℝ)*Real.log b := by
    unfold heightR
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (Real.log b-1)]
  nlinarith

lemma eventually_height_square_le : ∀ᶠ b : ℝ in atTop, heightR b^2 ≤ b := by
  filter_upwards [eventually_logpow_bound (1 : ℝ) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 4/9), eventually_ge_atTop (1 : ℝ)] with b hb hb1
  rw [Real.rpow_one, Real.rpow_one] at hb
  rw [heightR_sq hb1]
  linarith

lemma eventually_central_mean : ∀ᶠ b : ℝ in atTop,
    2*b^(70/100 : ℝ) ≤ b*Real.exp (-(heightR b^2)/8)/(heightR b*Real.sqrt (2*Real.pi)) := by
  have hc : 0 < 1/(2*Real.sqrt (2*Real.pi)) := by positivity
  filter_upwards [eventually_height_bound (by norm_num : (0 : ℝ) < 3/160) hc,
    eventually_gt_atTop (1 : ℝ)] with b hb hb1
  have hb0 : 0 < b := by linarith
  have hh := heightR_pos hb1
  have hexp : Real.exp (-(heightR b^2)/8) = b^(-(9/32 : ℝ)) := by
    calc
      _ = Real.exp (-(heightR b^2)*(1/8)) := by congr 1; ring
      _ = b^(-(9/4 : ℝ)*(1/8)) := heightR_exp hb1.le (1/8)
      _ = _ := by norm_num
  rw [hexp, le_div_iff₀ (by positivity)]
  have hh' : 2*(heightR b*Real.sqrt (2*Real.pi)) ≤ b^(3/160 : ℝ) := by
    have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
    have ht := (le_div_iff₀ (show (0 : ℝ) < 2*Real.sqrt (2*Real.pi) by positivity)).mp
      (show heightR b ≤ b^(3/160 : ℝ)/(2*Real.sqrt (2*Real.pi)) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg hb0.le (70/100 : ℝ))
  have he : b^(70/100 : ℝ)*b^(3/160 : ℝ) = b*b^(-(9/32 : ℝ)) := by
    calc
      _ = b^((70/100 : ℝ)+3/160) := (Real.rpow_add hb0 _ _).symm
      _ = b^((1 : ℝ)+(-(9/32 : ℝ))) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hb0, Real.rpow_one]
  rw [he] at hm
  nlinarith

lemma eventually_log_variance_tail : ∀ᶠ b : ℝ in atTop,
    b*((Real.log 2+heightR b^2/8)/2)^2/((1/2 : ℝ)*b^(56/100 : ℝ))^2 ≤ b^(-(1/20 : ℝ)) := by
  filter_upwards [eventually_logpow_bound (2 : ℝ) (by norm_num : (0 : ℝ) < 7/100)
    (by norm_num : (0 : ℝ) < 1/4), eventually_ge_atTop (2 : ℝ)] with b hb hb2
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hb2
  have hl0 := Real.log_nonneg hb1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.rpow_two] at hb
  have hsq : ((Real.log 2+heightR b^2/8)/2)^2 ≤ (Real.log b)^2 := by
    rw [heightR_sq hb1]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hr2 : (b^(56/100 : ℝ))^2 = b^(112/100 : ℝ) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hb0.le]
    norm_num
  have he : b^(-(1/20 : ℝ))*((1/2 : ℝ)*b^(56/100 : ℝ))^2 = (1/4 : ℝ)*b*b^(7/100 : ℝ) := by
    rw [mul_pow, hr2]
    have hpow : b^(-(1/20 : ℝ))*b^(112/100 : ℝ) = b*b^(7/100 : ℝ) := by
      calc
        _ = b^(-(1/20 : ℝ)+(112/100 : ℝ)) := (Real.rpow_add hb0 _ _).symm
        _ = b^((1 : ℝ)+(7/100 : ℝ)) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hb0, Real.rpow_one]
    nlinarith
  apply (div_le_iff₀ (by positivity)).mpr
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left (hsq.trans hb) hb0.le]



end SingleLatticeCovering.Folded



end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Sampling
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology

namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics

lemma eventually_rpow_ratio_bound {s t c : ℝ} (hst : s < t) (hc : 0 < c) :
    ∀ᶠ b : ℝ in atTop, b^s ≤ c*b^t := by
  have ht := tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  filter_upwards [ht.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with b hb hb0
  have he : b^(-(t-s)) = b^s/b^t := by
    rw [←Real.rpow_sub hb0]
    congr 1
    ring
  rw [he] at hb
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hb0 t)).mp hb |>.le

lemma eventually_prime_power (k : ℝ) (hk : 0 < k) :
    ∀ᶠ b : ℝ in atTop, ∀ p : ℝ, 0 < p →
      b*logMean (heightR b)-4*b^(56/100 : ℝ) ≤ Real.log p → b^k ≤ p := by
  filter_upwards [(logMean_tendsto.comp heightR_tendsto).eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_rpow_ratio_bound (by norm_num : (56/100 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/4),
    eventually_logpow_bound (1 : ℝ) (by norm_num : (0 : ℝ) < 1) (inv_pos.mpr hk),
    eventually_gt_atTop (1 : ℝ)] with b hμ hr hl hb1
  intro p hp hlp
  have hb0 : 0 < b := by linarith
  rw [Real.rpow_one] at hr
  rw [Real.rpow_one, Real.rpow_one] at hl
  have hbl : b ≤ Real.log p := by
    dsimp only [Function.comp_apply] at hμ
    nlinarith [mul_le_mul_of_nonneg_left hμ hb0.le]
  have hkl : Real.log b*k ≤ b := by
    calc
      _ ≤ (k⁻¹*b)*k := mul_le_mul_of_nonneg_right hl hk.le
      _ = b := by field_simp
  rw [Real.rpow_def_of_pos hb0]
  exact (Real.exp_le_exp.mpr (hkl.trans hbl)).trans_eq (Real.exp_log hp)

lemma grid_slack_of_fourth {b h p : ℝ} (hb : 2 ≤ b) (hh : 0 < h)
    (hsq : h^2 ≤ b) (hp : b^4 ≤ p) :
    b*h^2/p ≤ b^(-(2 : ℝ)) ∧ p⁻¹ ≤ 1/(2*h^2) := by
  have hb0 : 0 < b := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have he : b^(-(2 : ℝ)) = 1/b^2 := by rw [Real.rpow_neg hb0.le, Real.rpow_two, one_div]
  constructor
  · rw [he, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ b^3 by positivity)]
  · rw [inv_eq_one_div, div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [sq_nonneg (b-2),sq_nonneg (b^2-2)]

lemma eventually_rounding_slack : ∀ᶠ b : ℝ in atTop, ∀ p : ℝ, 0 < p →
    b*logMean (heightR b)-4*b^(56/100 : ℝ) ≤ Real.log p →
      b*heightR b^2/p ≤ b^(-(1/20 : ℝ)) ∧
      b*heightR b^2/p ≤ (1/2 : ℝ)*b^(56/100 : ℝ) ∧
      p⁻¹ ≤ 1/(2*heightR b^2) := by
  filter_upwards [eventually_prime_power (4 : ℝ) (by norm_num), eventually_height_square_le,
    eventually_rpow_ratio_bound (by norm_num : (-2 : ℝ) < 56/100) (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (2 : ℝ)] with b hp hs hr hb
  intro p hp0 hlp
  have hp4 : b^4 ≤ p := by
    have ht := hp p hp0 hlp
    change b^((4 : ℕ) : ℝ) ≤ p at ht
    rwa [Real.rpow_natCast] at ht
  have hg := grid_slack_of_fourth hb (heightR_pos (by linarith)) hs hp4
  exact ⟨hg.1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)), hg.1.trans hr,hg.2⟩


end SingleLatticeCovering.Folded


namespace SingleLatticeCovering.Folded
open Real Filter Topology MeasureTheory ConstructionA

lemma numerical_count_tail {b m : ℝ} (hb : 1 ≤ b)
    (hm : 2*b^(70/100 : ℝ) ≤ m) : 4/m ≤ 2*b^(-(1/20 : ℝ)) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hp : 0 < b^(70/100 : ℝ) := Real.rpow_pos_of_pos hb0 _
  have hm0 : 0 < m := by linarith
  calc
    4/m ≤ 4/(2*b^(70/100 : ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hm
    _ = 2*b^(-(70/100 : ℝ)) := by rw [Real.rpow_neg hb0.le]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb (by norm_num)) (by norm_num)




lemma eventually_grid_mass : ∀ᶠ b : ℕ in atTop, ∀ (p : ℕ) [NeZero p], 0 < p →
    (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
    |gridMass (ι := Fin b) (height b) p Finset.univ-1| ≤ 7*(b : ℝ)^(-(1/20 : ℝ)) ∧
    |gridMass (height b) p (gridEligible (ι := Fin b) (height b) (logMean (height b))
      ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p)-1| ≤ 7*(b : ℝ)^(-(1/20 : ℝ)) := by
  have hε : ∀ᶠ b : ℝ in atTop, b^(-(1/20 : ℝ)) ≤ 1/2 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [height_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually eventually_central_mean,
    tendsto_natCast_atTop_atTop.eventually eventually_log_variance_tail,
    tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
    tendsto_natCast_atTop_atTop.eventually hε, eventually_ge_atTop (2 : ℕ)]
    with b hh hm hv hs he hb
  intro p inst hp hlp
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hh0 : 0 < height b := by linarith
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp
  let e := (b : ℝ)^(-(1/20 : ℝ))
  let c := (1/2 : ℝ)*(b : ℝ)^(56/100 : ℝ)
  let r := (b : ℝ)^(70/100 : ℝ)
  let E := gridEligible (ι := Fin b) (height b) (logMean (height b)) (2*c) r p
  have he0 : 0 ≤ e := Real.rpow_nonneg hb0.le _
  have hc : 0 < c := mul_pos (by norm_num) (Real.rpow_pos_of_pos hb0 _)
  have hslack := hs (p : ℝ) hp0 hlp
  have hη : (b : ℝ)*height b^2*(p : ℝ)⁻¹ ≤ e := by simpa only [div_eq_mul_inv, height, heightR, e] using hslack.1
  have hηc : (b : ℝ)*height b^2*(p : ℝ)⁻¹ ≤ c := by simpa only [div_eq_mul_inv, height, heightR, c] using hslack.2.1
  have ha : 1-totalMass (height b)^b ≤ 2*e := by
    apply (height_totalMass_power_loss hb).2.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (by norm_num)
  have hg : 1-3*e ≤ (cubeLaw (height b) : Measure (Fin b → ℝ)).real
      (continuousGood (height b) c r) := by
    have ht := continuous_good_mass (ι := Fin b) hh (by simpa using (show 0 < b by omega)) hc
      (by simpa only [Fintype.card_fin, height, heightR, r] using hm)
    have hct := numerical_count_tail hb1 hm
    have ht' : 1-(b : ℝ)*((Real.log 2+height b^2/8)/2)^2/c^2 -
        4/((b : ℝ)*Real.exp (-(height b^2)/8)/(height b*Real.sqrt (2*Real.pi))) ≤
        (cubeLaw (height b) : Measure (Fin b → ℝ)).real (continuousGood (height b) c r) := by
      simpa only [continuousGood, Fintype.card_fin] using ht
    change (b : ℝ)*((Real.log 2+height b^2/8)/2)^2/c^2 ≤ e at hv
    change 4/((b : ℝ)*Real.exp (-(height b^2)/8)/(height b*Real.sqrt (2*Real.pi))) ≤ 2*e at hct
    linarith
  have hout := grid_from_continuous (ι := Fin b) hh0 (show 0 ≤ 2*e by positivity)
    (show 0 ≤ 3*e by positivity) p hp E (continuousGood (height b) c r)
    (continuousGood_measurable hh0)
    (fun t ht htc => round_into_eligible hh0 p hp
      (by simpa only [Fintype.card_fin] using hηc) hslack.2.2 htc ht)
    (by simpa only [Fintype.card_fin] using ha) hg
    (by simpa only [Fintype.card_fin] using hη.trans he)
  have htwo : 2*c = (b : ℝ)^(56/100 : ℝ) := by dsimp [c]; ring
  simp only [Fintype.card_fin, E, htwo] at hout
  exact ⟨hout.1.trans (by linarith), hout.2.trans (by linarith)⟩


end SingleLatticeCovering.Folded





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Sampler

universe u v

section FiniteAverages
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]

lemma expect_prod (f : α × β → ℝ) :
    (𝔼 z, f z) = 𝔼 a, 𝔼 b, f (a, b) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, Fintype.sum_prod_type, div_div]
  rw [mul_comm]


lemma expect_cons (k : ℕ) (f : (Fin (k + 1) → α) → ℝ) :
    (𝔼 w, f w) = 𝔼 a, 𝔼 w, f (Fin.cons a w) := by
  calc
    (𝔼 w, f w) = 𝔼 z : α × (Fin k → α), f (Fin.cons z.1 z.2) :=
      Fintype.expect_equiv (consEquiv k α) _ _ (fun w => by simp [consEquiv])
    _ = _ := expect_prod _

lemma expect_append (k j : ℕ) (f : (Fin (k+j) → α) → ℝ) :
    (𝔼 w, f w) = 𝔼 u : Fin k → α, 𝔼 v : Fin j → α, f (Fin.append u v) := by
  calc
    (𝔼 w, f w) = 𝔼 z : (Fin k → α) × (Fin j → α), f (Fin.append z.1 z.2) :=
      (Fintype.expect_equiv (Fin.appendEquiv k j) _ _ (fun _ => rfl)).symm
    _ = _ := expect_prod _


lemma expect_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    (𝔼 a, f a) ≤ 𝔼 a, g a := Finset.expect_le_expect (fun a _ => h a)

lemma expect_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ 𝔼 a, f a :=
  Finset.expect_nonneg (fun a _ => h a)

end FiniteAverages

section FiniteProbability
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]


lemma probability_nonneg (p : α → Prop) : 0 ≤ probability p := by
  classical
  exact expect_nonneg (fun _ => by split_ifs <;> norm_num)

lemma probability_le_one [Nonempty α] (p : α → Prop) : probability p ≤ 1 := by
  classical
  exact Finset.expect_le Finset.univ_nonempty (fun _ _ => by split_ifs <;> norm_num)

lemma probability_mono {p q : α → Prop} (h : ∀ x, p x → q x) :
    probability p ≤ probability q := by
  classical
  apply expect_mono
  intro x
  by_cases hp : p x
  · simp [hp, h x hp]
  · by_cases hq : q x <;> simp [hp, hq]

lemma probability_false : probability (fun _ : α => False) = 0 := by
  simp [probability]

lemma probability_compl [Nonempty α] (p : α → Prop) :
    probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  unfold probability
  rw [← Fintype.expect_const (ι := α) (1 : ℝ), ← Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro x _
  by_cases h : p x <;> simp [h]

lemma probability_prod (p : α × β → Prop) :
    probability p = 𝔼 a, probability (fun b => p (a,b)) := expect_prod _

lemma probability_cons (k : ℕ) (p : (Fin (k+1) → α) → Prop) :
    probability p = 𝔼 a, probability (fun w : Fin k → α => p (Fin.cons a w)) := by
  classical
  exact expect_cons k _

lemma probability_cons_tail (k : ℕ) (p : (Fin (k+1) → α) → Prop) :
    probability p = 𝔼 w : Fin k → α, probability (fun a => p (Fin.cons a w)) := by
  classical
  rw [probability_cons]
  unfold probability
  rw [Finset.expect_comm]

lemma probability_append (k j : ℕ) (p : (Fin (k+j) → α) → Prop) :
    probability p = probability (fun z : (Fin k → α) × (Fin j → α) => p (Fin.append z.1 z.2)) := by
  classical
  unfold probability
  exact (Fintype.expect_equiv (Fin.appendEquiv k j) _ _ (fun _ => rfl)).symm


lemma probability_gt_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    probability (fun x => t < f x) ≤ (𝔼 x, f x) / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold probability
  rw [Finset.expect_mul]
  apply expect_mono
  intro x
  by_cases h : t < f x
  · simpa [h] using h.le
  · simpa [h] using hf x

end FiniteProbability

section GroupAverages
variable {G : Type u} [AddCommGroup G] [Fintype G]

lemma expect_sub_right (f : G → ℝ) (a : G) :
    (𝔼 x, f (x - a)) = 𝔼 x, f x :=
  Fintype.expect_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

lemma expect_sub_left (f : G → ℝ) (a : G) :
    (𝔼 x, f (a - x)) = 𝔼 x, f x :=
  Fintype.expect_equiv (Equiv.subLeft a) _ _ (fun _ => rfl)

lemma expect_correlation (f g : G → ℝ) :
    (𝔼 w, 𝔼 x, f x * g (x - w)) = (𝔼 x, f x) * 𝔼 x, g x := by
  rw [Finset.expect_comm]
  simp_rw [← Finset.mul_expect, expect_sub_left, ← Finset.expect_mul]


lemma step_nonneg {G : Type u} [AddCommGroup G] [Fintype G] (w : G) {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ step w f x := by exact div_nonneg (add_nonneg (hf x) (hf _)) (by norm_num)

lemma step_mean (w : G) (f : G → ℝ) : (𝔼 x, step w f x) = 𝔼 x, f x := by
  simp only [step, ← Finset.expect_div, Finset.expect_add_distrib, expect_sub_right]
  ring



lemma step_second_moment (f : G → ℝ) :
    (𝔼 w, 𝔼 x, (step w f x) ^ 2) =
      ((𝔼 x, (f x) ^ 2) + (𝔼 x, f x) ^ 2) / 2 := by
  have h (w x : G) : (step w f x) ^ 2 =
      ((f x) ^ 2 + (f (x-w)) ^ 2 + 2 * (f x * f (x-w))) / 4 := by
    unfold step
    ring
  have hs (w : G) : (𝔼 x, (f (x-w))^2) = 𝔼 x, (f x)^2 :=
    expect_sub_right (fun x => (f x)^2) w
  simp_rw [h, ← Finset.expect_div, Finset.expect_add_distrib,
    ← Finset.mul_expect, hs, Fintype.expect_const]
  rw [expect_correlation]
  ring


lemma binaryAverage_mean {k : ℕ} (w : Fin k → G) (f : G → ℝ) :
    (𝔼 x, binaryAverage w f x) = 𝔼 x, f x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (𝔼 x, step (w 0) (binaryAverage (Fin.tail w) f) x) = _
    rw [step_mean, ih]

lemma binaryAverage_nonneg {k : ℕ} (w : Fin k → G) {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : G) : 0 ≤ binaryAverage w f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih => exact step_nonneg _ (fun x => ih (Fin.tail w) x) x

lemma binaryAverage_sub_const {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) (f : G → ℝ) (c : ℝ) (x : G) :
    binaryAverage w (fun y => f y - c) x = binaryAverage w f x - c := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change ((binaryAverage (Fin.tail w) (fun y => f y-c) x +
      binaryAverage (Fin.tail w) (fun y => f y-c) (x-w 0)) / 2) = _
    rw [ih, ih]
    change _ = (binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0)) / 2-c
    ring



lemma binaryAverage_centered_second_moment (k : ℕ) (f : G → ℝ)
    (hf : (𝔼 x, f x) = 0) :
    (𝔼 w : Fin k → G, 𝔼 x, (binaryAverage w f x)^2) =
      (𝔼 x, (f x)^2) / (2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [expect_cons, Finset.expect_comm]
    simp_rw [binaryAverage_cons, step_second_moment, binaryAverage_mean, hf,
      zero_pow (by decide : 2 ≠ 0), add_zero, ← Finset.expect_div]
    rw [ih, pow_succ]
    ring

lemma binaryAverage_variance (k : ℕ) (f : G → ℝ) :
    (𝔼 w : Fin k → G, 𝔼 x, (binaryAverage w f x - (𝔼 y, f y))^2) =
      (𝔼 x, (f x - (𝔼 y, f y))^2) / (2 : ℝ)^k := by
  simpa only [binaryAverage_sub_const] using
    binaryAverage_centered_second_moment k (fun x => f x - (𝔼 y, f y)) (by
      rw [Finset.expect_sub_distrib, Fintype.expect_const, sub_self])


lemma variance_eq (f : G → ℝ) :
    (𝔼 x, (f x - (𝔼 y, f y))^2) = (𝔼 x, (f x)^2) - (𝔼 x, f x)^2 := by
  have h (x : G) : (f x - (𝔼 y, f y))^2 =
      (f x)^2 - 2 * (𝔼 y, f y) * f x + (𝔼 y, f y)^2 := by ring
  simp_rw [h, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const]
  ring

lemma lower_tail_le_variance {G : Type u} [AddCommGroup G] [Fintype G] (f : G → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hμ : 0 < 𝔼 x, f x) :
    probability (fun x => f x < (1-δ) * (𝔼 y, f y)) ≤
      (𝔼 x, (f x - (𝔼 y, f y))^2) / (δ * (𝔼 x, f x))^2 := by
  have ht : 0 < δ * (𝔼 y, f y) := mul_pos hδ hμ
  apply (probability_mono (q := fun x => (δ*(𝔼 y, f y))^2 <
    (f x - (𝔼 y, f y))^2) ?_).trans
      (probability_gt_le (fun x => sq_nonneg _) (sq_pos_of_pos ht))
  intro x hx
  nlinarith


lemma expected_bad_fraction_le (k : ℕ) (f : G → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hμ : 0 < 𝔼 x, f x) :
    (𝔼 w : Fin k → G,
      probability (fun x => binaryAverage w f x < (1-δ) * (𝔼 y, f y))) ≤
      (𝔼 x, (f x - (𝔼 y, f y))^2) / ((2 : ℝ)^k * (δ * (𝔼 x, f x))^2) := by
  have h (w : Fin k → G) := lower_tail_le_variance (binaryAverage w f) hδ
    (by simpa only [binaryAverage_mean] using hμ)
  simp only [binaryAverage_mean] at h
  have he := expect_mono h
  rw [← Finset.expect_div, binaryAverage_variance, div_div] at he
  exact he


lemma subsetShift_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin (k+1) → G) (b : Bool) (e : Fin k → Bool) :
    subsetShift w (Fin.cons b e) = (if b then w 0 else 0) + subsetShift (Fin.tail w) e := by
  simp [subsetShift, Fin.sum_univ_succ, Fin.tail]

lemma subsetShift_append {G : Type u} [AddCommGroup G] [Fintype G] {k j : ℕ} (u : Fin k → G) (v : Fin j → G)
    (a : Fin k → Bool) (b : Fin j → Bool) :
    subsetShift (Fin.append u v) (Fin.append a b) = subsetShift u a + subsetShift v b := by
  simp [subsetShift, Fin.sum_univ_add]


lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b) = (f false + f true)/2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
  simp [add_comm]



lemma binaryAverage_eq_expect {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) :
    binaryAverage w f x = 𝔼 e : Fin k → Bool, f (x-subsetShift w e) := by
  induction k generalizing x with
  | zero => simp [subsetShift]
  | succ k ih =>
    rw [expect_cons, expect_bool]
    simp only [subsetShift_cons, Bool.false_eq_true, ↓reduceIte, zero_add,
      sub_add_eq_sub_sub]
    rw [← ih (Fin.tail w) x, ← ih (Fin.tail w) (x-w 0)]
    rfl

lemma binaryAverage_eq_sum {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) :
    binaryAverage w f x = (∑ e : Fin k → Bool, f (x-subsetShift w e)) / (2 : ℝ)^k := by
  rw [binaryAverage_eq_expect, Fintype.expect_eq_sum_div_card]
  simp



lemma binaryAverage_append {k j : ℕ} (u : Fin k → G) (v : Fin j → G) (f : G → ℝ) (x : G) :
    binaryAverage (Fin.append u v) f x = binaryAverage v (binaryAverage u f) x := by
  rw [binaryAverage_eq_expect, expect_append, Finset.expect_comm]
  simp_rw [subsetShift_append, binaryAverage_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  apply Finset.expect_congr rfl
  intro a _
  congr 1
  abel


lemma binaryAverage_mono {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) {f g : G → ℝ}
    (h : ∀ x, f x ≤ g x) (x : G) : binaryAverage w f x ≤ binaryAverage w g x := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih =>
    change (binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0))/2 ≤
      (binaryAverage (Fin.tail w) g x + binaryAverage (Fin.tail w) g (x-w 0))/2
    exact div_le_div_of_nonneg_right (add_le_add (ih _ x) (ih _ (x-w 0))) (by norm_num)

lemma binaryAverage_mul_const {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (w : Fin k → G) (f : G → ℝ) (c : ℝ) (x : G) :
    binaryAverage w (fun y => c * f y) x = c * binaryAverage w f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (binaryAverage (Fin.tail w) (fun y => c*f y) x +
      binaryAverage (Fin.tail w) (fun y => c*f y) (x-w 0))/2 = _
    rw [ih, ih]
    change _ = c * ((binaryAverage (Fin.tail w) f x + binaryAverage (Fin.tail w) f (x-w 0))/2)
    ring



lemma potential_pos (θ : ℝ) (f : G → ℝ) : 0 < potential θ f :=
  Finset.expect_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma potential_square (θ : ℝ) (f : G → ℝ) :
    (𝔼 w, potential θ (fun x => f x + f (x-w))) = (potential θ f)^2 := by
  unfold potential
  simp_rw [mul_add, Real.exp_add]
  rw [expect_correlation (fun x => Real.exp (-θ * f x)) (fun x => Real.exp (-θ * f x)), pow_two]

lemma potential_step_failure (θ ε : ℝ) (f : G → ℝ) :
    probability (fun w => Real.exp ε * (potential θ f)^2 <
      potential θ (fun x => f x + f (x-w))) ≤ Real.exp (-ε) := by
  have hp := potential_pos θ f
  have ht : 0 < Real.exp ε * (potential θ f)^2 := mul_pos (Real.exp_pos _) (sq_pos_of_pos hp)
  have h := probability_gt_le
    (fun w => (potential_pos θ (fun x => f x + f (x-w))).le) ht
  rw [potential_square] at h
  convert h using 1
  rw [Real.exp_neg]
  field_simp



lemma potential_iteration_failure (θ ε a : ℝ) (f : G → ℝ)
    (h₀ : potential θ f ≤ Real.exp a) (k : ℕ) :
    probability (fun w : Fin k → G =>
      Real.exp ((2 : ℝ)^k * a + ((2 : ℝ)^k - 1) * ε) <
        potential θ (binarySum w f)) ≤ (k : ℝ) * Real.exp (-ε) := by
  induction k with
  | zero =>
    have h : (fun w : Fin 0 → G =>
        Real.exp ((2 : ℝ)^0 * a + ((2 : ℝ)^0 - 1)*ε) <
          potential θ (binarySum w f)) = (fun _ => False) := by
      funext w
      simp only [pow_zero, one_mul, sub_self, zero_mul, add_zero]
      simp only [show binarySum w f = f by funext x; simp]
      exact propext (iff_false_intro (not_lt_of_ge h₀))
    rw [h, probability_false]
    simp
  | succ k ih =>
    let T : ℝ := Real.exp ((2 : ℝ)^k * a + ((2 : ℝ)^k-1)*ε)
    have hT : 0 < T := Real.exp_pos _
    have hnext : Real.exp ((2 : ℝ)^(k+1)*a + ((2 : ℝ)^(k+1)-1)*ε) =
        Real.exp ε * T^2 := by
      dsimp [T]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [pow_succ]
      ring
    rw [probability_cons_tail]
    have hcond (w : Fin k → G) :
        probability (fun z =>
          Real.exp ((2 : ℝ)^(k+1)*a+((2 : ℝ)^(k+1)-1)*ε) <
            potential θ (binarySum (Fin.cons z w) f)) ≤
          (if T < potential θ (binarySum w f) then 1 else 0) + Real.exp (-ε) := by
      by_cases hw : T < potential θ (binarySum w f)
      · simp only [hw, ↓reduceIte]
        exact (probability_le_one _).trans (by linarith [Real.exp_pos (-ε)])
      · have hle : potential θ (binarySum w f) ≤ T := le_of_not_gt hw
        simp only [hw, ↓reduceIte, zero_add]
        apply (probability_mono (q := fun z => Real.exp ε * (potential θ (binarySum w f))^2 <
          potential θ (fun x => binarySum w f x + binarySum w f (x-z))) ?_).trans
          (potential_step_failure θ ε (binarySum w f))
        intro z hz
        rw [hnext] at hz
        have hs : (potential θ (binarySum w f))^2 ≤ T^2 :=
          pow_le_pow_left₀ (potential_pos θ _).le hle 2
        have hb : binarySum (Fin.cons z w) f =
            fun x => binarySum w f x + binarySum w f (x-z) := by
          funext x
          exact binarySum_cons z w f x
        rw [hb] at hz
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) hz
    have he := expect_mono hcond
    rw [Finset.expect_add_distrib, Fintype.expect_const] at he
    change _ ≤ probability (fun w : Fin k → G => T < potential θ (binarySum w f)) +
      Real.exp (-ε) at he
    dsimp [T] at he
    push_cast
    linarith


lemma exp_le_card_mul_potential (θ : ℝ) (f : G → ℝ) (x : G) :
    Real.exp (-θ * f x) ≤ (Fintype.card G : ℝ) * potential θ f := by
  classical
  rw [potential, Fintype.expect_eq_sum_div_card]
  have hc : (Fintype.card G : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hc]
  exact Finset.single_le_sum (f := fun y => Real.exp (-θ*f y))
    (fun y _ => (Real.exp_pos _).le) (Finset.mem_univ x)

lemma potential_bound_pointwise (θ a : ℝ) (f : G → ℝ)
    (h : potential θ f ≤ Real.exp a) (x : G) :
    -θ * f x ≤ Real.log (Fintype.card G) + a := by
  have hc : (0 : ℝ) < Fintype.card G := by positivity
  have he := (exp_le_card_mul_potential θ f x).trans (mul_le_mul_of_nonneg_left h hc.le)
  have heq : (Fintype.card G : ℝ) * Real.exp a =
      Real.exp (Real.log (Fintype.card G) + a) := by rw [Real.exp_add, Real.exp_log hc]
  rw [heq] at he
  exact Real.exp_le_exp.mp he

lemma potential_bound_binaryAverage {k : ℕ} (w : Fin k → G) (f : G → ℝ)
    {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (h : potential θ (binarySum w f) ≤
      Real.exp ((2 : ℝ)^k * (-θ+1) + ((2 : ℝ)^k-1)*(θ*δ))) (x : G) :
    1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k) ≤ binaryAverage w f x := by
  have hh := potential_bound_pointwise θ _ _ h x
  unfold binarySum at hh
  have hp : (0 : ℝ) < 2^k := by positivity
  have he : θ*(2 : ℝ)^k*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k)) =
      θ*(2 : ℝ)^k-θ*(2 : ℝ)^k*δ-(2 : ℝ)^k-Real.log (Fintype.card G) := by
    field_simp

  apply le_of_mul_le_mul_left (a := θ*(2 : ℝ)^k) _ (mul_pos hθ hp)
  rw [he]
  nlinarith [mul_nonneg hθ.le hδ]



lemma indicator_initial_potential {p : G → Prop} [DecidablePred p] {θ : ℝ}
    (hθ : 0 ≤ θ) (hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ)) :
    potential θ (fun x => if p x then 1 else 0) ≤ Real.exp (-θ+1) := by
  classical
  have hi (x : G) : Real.exp (-θ*(if p x then 1 else 0)) =
      (if ¬p x then 1 else 0) + (if p x then 1 else 0) * Real.exp (-θ) := by
    by_cases h : p x <;> simp [h]
  have he : potential θ (fun x => if p x then 1 else 0) =
      probability (fun x => ¬p x) + probability p * Real.exp (-θ) := by
    unfold potential probability
    simp_rw [hi, Finset.expect_add_distrib, ← Finset.expect_mul]
    congr 1
    · apply Finset.expect_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
    · congr 1
      apply Finset.expect_congr rfl
      intro x _
      by_cases h : p x <;> simp [h]
  rw [he]
  calc
    probability (fun x => ¬p x) + probability p * Real.exp (-θ) ≤
        Real.exp (-2*θ) + Real.exp (-θ) :=
      add_le_add hp (by nlinarith [probability_le_one p, Real.exp_pos (-θ)])
    _ ≤ 2 * Real.exp (-θ) := by
      have : Real.exp (-2*θ) ≤ Real.exp (-θ) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ ≤ Real.exp 1 * Real.exp (-θ) := by
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


lemma second_stage_failure {p : G → Prop} [DecidablePred p] {θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ)) (k : ℕ) :
    probability (fun w : Fin k → G => ∃ x,
      binaryAverage w (fun y => if p y then 1 else 0) x <
        1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^k)) ≤
      (k : ℝ) * Real.exp (-(θ*δ)) := by
  apply (probability_mono (q := fun w : Fin k → G =>
    Real.exp ((2 : ℝ)^k*(-θ+1)+((2 : ℝ)^k-1)*(θ*δ)) <
      potential θ (binarySum w (fun y => if p y then 1 else 0))) ?_).trans
      (potential_iteration_failure θ (θ*δ) (-θ+1) _ (indicator_initial_potential hθ.le hp) k)
  intro w hw
  by_contra h
  obtain ⟨x, hx⟩ := hw
  exact not_lt_of_ge (potential_bound_binaryAverage w _ hθ hδ (le_of_not_gt h) x) hx



lemma two_stage_failure (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ) :
    probability (fun z : (Fin k → G) × (Fin j → G) => ∃ x,
      binaryAverage z.2 (binaryAverage z.1 f) x <
        (1-δ)*(𝔼 y, f y)*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j))) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  classical
  let μ : ℝ := 𝔼 x, f x
  let β (u : Fin k → G) : ℝ := probability (fun x => binaryAverage u f x < (1-δ)*μ)
  let L : ℝ := 1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j)
  have ht : 0 < (1-δ)*μ := mul_pos (sub_pos.mpr hδ₁) hμ
  have hfirst : probability (fun u => Real.exp (-2*θ) < β u) ≤
      ((𝔼 x, (f x-μ)^2) / ((2 : ℝ)^k*(δ*μ)^2)) / Real.exp (-2*θ) := by
    have hb := probability_gt_le (f := β) (fun u => probability_nonneg _) (Real.exp_pos (-2*θ))
    have hc := expected_bad_fraction_le k f hδ hμ
    exact hb.trans (div_le_div_of_nonneg_right hc (Real.exp_pos _).le)
  rw [probability_prod]
  have hcond (u : Fin k → G) :
      probability (fun v : Fin j → G => ∃ x, binaryAverage v (binaryAverage u f) x <
        (1-δ)*μ*L) ≤
      (if Real.exp (-2*θ) < β u then 1 else 0) + (j : ℝ)*Real.exp (-(θ*δ)) := by
    by_cases hu : Real.exp (-2*θ) < β u
    · simp only [hu, ↓reduceIte]
      exact (probability_le_one _).trans (by
        have : 0 ≤ (j : ℝ)*Real.exp (-(θ*δ)) := by positivity
        linarith)
    · simp only [hu, ↓reduceIte, zero_add]
      let p : G → Prop := fun x => (1-δ)*μ ≤ binaryAverage u f x
      have hp : probability (fun x => ¬p x) ≤ Real.exp (-2*θ) := by
        simpa only [p, not_le] using (le_of_not_gt hu)
      have hpoint (x : G) : (1-δ)*μ*(if p x then 1 else 0) ≤ binaryAverage u f x := by
        by_cases hx : p x
        · rw [ite_eq_left hx, mul_one]
          exact hx
        · simpa [hx] using binaryAverage_nonneg u hf x
      have hsample (v : Fin j → G) (x : G) :
          (1-δ)*μ*binaryAverage v (fun y => if p y then 1 else 0) x ≤
            binaryAverage v (binaryAverage u f) x := by
        simpa only [binaryAverage_mul_const] using binaryAverage_mono v hpoint x
      apply (probability_mono (q := fun v : Fin j → G => ∃ x,
        binaryAverage v (fun y => if p y then 1 else 0) x < L) ?_).trans
        (second_stage_failure hθ hδ.le hp j)
      rintro v ⟨x, hx⟩
      refine ⟨x, ?_⟩
      by_contra hn
      have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) ht.le
      exact not_lt_of_ge (hh.trans (hsample v x)) hx
  have he := expect_mono hcond
  rw [Finset.expect_add_distrib, Fintype.expect_const] at he
  have hs : (𝔼 u : Fin k → G, if Real.exp (-2*θ) < β u then (1 : ℝ) else 0) =
      probability (fun u => Real.exp (-2*θ) < β u) := by
    unfold probability
    apply Finset.expect_congr rfl
    intro u _
    by_cases hu : Real.exp (-2*θ) < β u <;> simp
  rw [hs] at he
  exact he.trans (add_le_add hfirst le_rfl)



lemma two_stage_failure_three_delta (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ)
    (hsmall : 1/θ+Real.log (Fintype.card G)/(θ*(2 : ℝ)^j) ≤ δ) :
    probability (fun z : (Fin k → G) × (Fin j → G) => ∃ x,
      binaryAverage z.2 (binaryAverage z.1 f) x < (1-3*δ)*(𝔼 y, f y)) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  have ht : 0 ≤ (1-δ)*(𝔼 y, f y) := mul_nonneg (by linarith) hμ.le
  have hl : (1-3*δ)*(𝔼 y, f y) ≤
      (1-δ)*(𝔼 y, f y)*(1-δ-1/θ-Real.log (Fintype.card G)/(θ*(2 : ℝ)^j)) := by
    calc
      _ ≤ (1-δ)*(𝔼 y, f y)*(1-2*δ) := by
        nlinarith [mul_nonneg (sq_nonneg δ) hμ.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ht
  exact (probability_mono (fun z hz => by
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, hx.trans_le hl⟩)).trans (two_stage_failure f hf hδ hδ₁ hθ hμ k j)


lemma sampler_explicit_parameters (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hθ : 0 < θ) (hμ : 0 < 𝔼 x, f x) (k j : ℕ)
    (hsmall : 1/θ+Real.log (Fintype.card G)/(θ*(2 : ℝ)^j) ≤ δ) :
    probability (fun w : Fin (k+j) → G => ∃ x,
      (∑ e : Fin (k+j) → Bool, f (x-subsetShift w e)) / (2 : ℝ)^(k+j) <
        (1-3*δ)*(𝔼 y, f y)) ≤
      ((𝔼 x, (f x-(𝔼 y, f y))^2) /
        ((2 : ℝ)^k*(δ*(𝔼 y, f y))^2)) / Real.exp (-2*θ) +
          (j : ℝ)*Real.exp (-(θ*δ)) := by
  simp_rw [← binaryAverage_eq_sum]
  rw [probability_append]
  simp_rw [binaryAverage_append]
  exact two_stage_failure_three_delta f hf hδ hδ₁ hθ hμ k j hsmall

end GroupAverages
end SingleLatticeCovering.Sampler




end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_SamplingBounds
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics

namespace SingleLatticeCovering.Sampler.Numeric

lemma cStar_pos : 0 < cStar := div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma tendsto_rpow_ratio {p q : ℝ} (h : p < q) :
    Tendsto (fun b : ℝ => b^p/b^q) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (sub_pos.mpr h)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [← Real.rpow_sub hb]
  congr 1
  ring

lemma tendsto_rpow_mul_exp_neg_rpow (p : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun b : ℝ => b^p * Real.exp (-c*b^a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/a) c hc).comp
    (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hb.le]
  rw [mul_div_cancel₀ _ ha.ne']


lemma eventually_first_stage_log :
    ∀ᶠ b : ℝ in atTop,
      Real.log 8 + (1/5 : ℝ)*Real.log b + 2*b^(65/100 : ℝ) ≤
        (Real.log 2/4)*b^(69/100 : ℝ) := by
  have hp : (0 : ℝ) < 69/100 := by norm_num
  have h0 := (tendsto_rpow_atTop hp).inv_tendsto_atTop.const_mul (Real.log 8)
  have h1 := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero.const_mul (1/5 : ℝ)
  have h2 := (tendsto_rpow_ratio (by norm_num : (65/100 : ℝ) < 69/100)).const_mul (2 : ℝ)
  have hl : Tendsto (fun b : ℝ =>
      (Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ))/b^(69/100 : ℝ)) atTop (𝓝 0) := by
    convert (h0.add h1).add h2 using 1 <;> try norm_num
    funext b
    ring
  have hc : (0 : ℝ) < Real.log 2/4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hl.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with b hb hb₀
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hb₀ _)).mp hb).le


lemma eventually_thresholds :
    ∀ᶠ b : ℝ in atTop,
      1 < b ∧
      Real.log 8 + (1/5 : ℝ)*Real.log b + 2*b^(65/100 : ℝ) ≤
        (Real.log 2/4)*b^(69/100 : ℝ) ∧
      4/cStar ≤ b^(59/100 : ℝ) ∧
      b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4 ∧
      b^(1/2 : ℝ)*Real.exp (-cStar*b^(69/100 : ℝ)) ≤ 1/2 ∧
      b^(3/2 : ℝ)*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ 1/2 := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 59/100)).eventually
    (eventually_ge_atTop (4/cStar))
  have he0 := (tendsto_rpow_mul_exp_neg_rpow (341/100 : ℝ)
    (by norm_num : (0 : ℝ) < 69/100)
    (div_pos (Real.log_pos (by norm_num)) (by norm_num) : (0 : ℝ) < Real.log 2/2)).eventually
    (gt_mem_nhds (div_pos cStar_pos (by norm_num) : (0 : ℝ) < cStar/4))
  have he1 := (tendsto_rpow_mul_exp_neg_rpow (1/2 : ℝ)
    (by norm_num : (0 : ℝ) < 69/100) cStar_pos).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have he2 := (tendsto_rpow_mul_exp_neg_rpow (3/2 : ℝ)
    (by norm_num : (0 : ℝ) < 59/100) (div_pos cStar_pos (by norm_num : (0 : ℝ) < 2))).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_first_stage_log, hpow, he0, he1, he2]
    with b hb hlog hpow he0 he1 he2
  exact ⟨hb, hlog, hpow, he0.le, he1.le, he2.le⟩

lemma delta_pos {b : ℝ} (hb : 0 < b) : 0 < delta b := Real.rpow_pos_of_pos hb _

lemma delta_lt_one {b : ℝ} (hb : 1 < b) : delta b < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hb (by norm_num)

lemma theta_pos {b : ℝ} {s : ℕ} (hb : 0 < b) (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) :
    0 < theta s := div_pos (mul_pos cStar_pos ((Real.rpow_pos_of_pos hb _).trans_le hs)) (by norm_num)

lemma half_counts (s : ℕ) :
    (s : ℝ)/2-1 ≤ (s/2 : ℕ) ∧ (s : ℝ)/2 ≤ (s-s/2 : ℕ) ∧ s-s/2 ≤ s := by
  have hk : s ≤ 2*(s/2)+1 := by omega
  have hj : s ≤ 2*(s-s/2) := by omega
  have hk' : (s : ℝ) ≤ 2*(s/2 : ℕ)+1 := by exact_mod_cast hk
  have hj' : (s : ℝ) ≤ 2*(s-s/2 : ℕ) := by exact_mod_cast hj
  exact ⟨by linarith, by linarith, Nat.sub_le _ _⟩

lemma rpow_delta_identity {b : ℝ} (hb : 0 < b) :
    b^(69/100 : ℝ)*delta b = b^(59/100 : ℝ) := by
  rw [delta, ← Real.rpow_add hb]
  norm_num

lemma theta_delta_lower {b : ℝ} {s : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) :
    (cStar/2)*b^(59/100 : ℝ) ≤ theta s*delta b := by
  rw [← rpow_delta_identity hb]
  have hh := mul_le_mul_of_nonneg_right hs (delta_pos hb).le
  have hh' := mul_le_mul_of_nonneg_left hh (div_pos cStar_pos (by norm_num : (0 : ℝ) < 2)).le
  dsimp [theta]
  nlinarith only [hh']

lemma two_pow_eq_exp (j : ℕ) : (2 : ℝ)^j = Real.exp ((j : ℝ)*Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma two_pow_lower {b : ℝ} {s j : ℕ}
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : (s : ℝ)/2 ≤ (j : ℝ)) :
    Real.exp ((Real.log 2/2)*b^(69/100 : ℝ)) ≤ (2 : ℝ)^j := by
  rw [two_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hs hl.le,
    mul_le_mul_of_nonneg_right hj hl.le]


lemma potential_errors_le {b L : ℝ} {s j : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : (s : ℝ)/2 ≤ (j : ℝ))
    (hL : L ≤ b^4) (hpow : 4/cStar ≤ b^(59/100 : ℝ))
    (hpoly : b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4) :
    1/theta s+L/(theta s*(2 : ℝ)^j) ≤ delta b := by
  have hθ := theta_pos hb hs
  have hδ := delta_pos hb
  have ht := theta_delta_lower hb hs
  have he := two_pow_lower hs hj
  have hpow' := (div_le_iff₀ cStar_pos).mp hpow
  have hfirst : 1/theta s ≤ delta b/2 := by
    apply (div_le_iff₀ hθ).mpr
    nlinarith
  have hpoly' : b^(341/100 : ℝ) ≤ (cStar/4)*Real.exp ((Real.log 2/2)*b^(69/100 : ℝ)) := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hpoly
    exact (div_le_iff₀ (Real.exp_pos _)).mp hpoly
  have hprod : b^(341/100 : ℝ)*b^(59/100 : ℝ) = b^4 := by
    rw [← Real.rpow_add hb]
    norm_num
  have hfour := mul_le_mul_of_nonneg_right hpoly' (Real.rpow_pos_of_pos hb (59/100 : ℝ)).le
  rw [hprod] at hfour
  have hsecond : b^4/(theta s*(2 : ℝ)^j) ≤ delta b/2 := by
    apply (div_le_iff₀ (mul_pos hθ (by positivity))).mpr
    have hmul := mul_le_mul ht he (Real.exp_pos _).le (mul_pos hθ hδ).le
    nlinarith [hfour]
  have hL' := div_le_div_of_nonneg_right hL (mul_pos hθ (by positivity : (0 : ℝ) < 2^j)).le
  linarith

lemma delta_sq {b : ℝ} (hb : 0 < b) :
    (delta b)^2 = Real.exp (-(1/5 : ℝ)*Real.log b) := by
  rw [delta, Real.rpow_def_of_pos hb, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma log_eight : Real.log 8 = 3*Real.log 2 := by
  rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
  norm_num

lemma log_four : Real.log 4 = 2*Real.log 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  norm_num


lemma first_stage_ratio_le {b V μ : ℝ} {s k : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hk : (s : ℝ)/2-1 ≤ (k : ℝ))
    (hμ : 1/2 ≤ μ) (hV : V ≤ Real.exp (2*b^(65/100 : ℝ)))
    (hlog : Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ) ≤
      (Real.log 2/4)*b^(69/100 : ℝ)) :
    (V/((2 : ℝ)^k*(delta b*μ)^2))/Real.exp (-2*theta s) ≤
      Real.exp (-cStar*(s : ℝ)) := by
  have hδ := delta_pos hb
  have hμpos : 0 < μ := by linarith
  have hD : 0 < (2 : ℝ)^k*(delta b*μ)^2 := by positivity
  have hexponent : 2*b^(65/100 : ℝ) ≤
      (k : ℝ)*Real.log 2-(1/5 : ℝ)*Real.log b-Real.log 4-2*cStar*(s : ℝ) := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hs' := mul_le_mul_of_nonneg_left hs (div_pos hl (by norm_num : (0 : ℝ) < 4)).le
    have hk' := mul_le_mul_of_nonneg_right hk hl.le
    rw [log_eight] at hlog
    rw [log_four]
    dsimp [cStar]
    nlinarith
  have heq : (2 : ℝ)^k*(delta b)^2/4*Real.exp (-2*cStar*(s : ℝ)) =
      Real.exp ((k : ℝ)*Real.log 2-(1/5 : ℝ)*Real.log b-Real.log 4-2*cStar*(s : ℝ)) := by
    rw [two_pow_eq_exp, delta_sq hb]
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) by rw [Real.exp_log (by norm_num)]]
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  have hden : (2 : ℝ)^k*(delta b)^2/4 ≤ (2 : ℝ)^k*(delta b*μ)^2 := by
    have hm : (1/4 : ℝ) ≤ μ^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (delta b))
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2^k by positivity)
    nlinarith only [hh']
  have hv : V ≤ (2 : ℝ)^k*(delta b*μ)^2*Real.exp (-2*cStar*(s : ℝ)) := by
    calc
      V ≤ Real.exp (2*b^(65/100 : ℝ)) := hV
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
      _ = _ := heq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  apply (div_le_iff₀ hD).mpr
  have hprod : Real.exp (-cStar*(s : ℝ))*Real.exp (-2*theta s) =
      Real.exp (-2*cStar*(s : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [theta]
    ring
  rw [hprod, mul_comm]
  exact hv


lemma failure_tail_le {b : ℝ} {s j : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : j ≤ s) (hsb : (s : ℝ) ≤ b) :
    Real.exp (-cStar*(s : ℝ)) + (j : ℝ)*Real.exp (-(theta s*delta b)) ≤
      Real.exp (-cStar*b^(69/100 : ℝ)) +
        b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) := by
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr cStar_pos.le)
  · apply mul_le_mul
    · exact (Nat.cast_le.mpr hj).trans hsb
    · apply Real.exp_le_exp.mpr
      have h := theta_delta_lower hb hs
      nlinarith only [h]
    · exact (Real.exp_pos _).le
    · exact hb.le

lemma failure_tail_le_rpow {b : ℝ} (hb : 0 < b)
    (h₁ : b^(1/2 : ℝ)*Real.exp (-cStar*b^(69/100 : ℝ)) ≤ 1/2)
    (h₂ : b^(3/2 : ℝ)*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ 1/2) :
    Real.exp (-cStar*b^(69/100 : ℝ)) +
      b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ b^(-1/2 : ℝ) := by
  apply le_of_mul_le_mul_left (a := b^(1/2 : ℝ)) _ (Real.rpow_pos_of_pos hb _)
  have heq : b^(1/2 : ℝ)*b = b^(3/2 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one b]
    rw [← Real.rpow_add hb]
    norm_num
  have hinv : b^(1/2 : ℝ)*b^(-1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hb]
    norm_num
  rw [mul_add, ← mul_assoc, heq, hinv]
  linarith

end SingleLatticeCovering.Sampler.Numeric

namespace SingleLatticeCovering.Sampler
universe u v
open Numeric

section Endpoint
universe w
variable {G : Type w} [AddCommGroup G] [Fintype G]

lemma variance_le_exp {b : ℝ} {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hupper : ∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) :
    (𝔼 x, (f x-(𝔼 y, f y))^2) ≤ Real.exp (2*b^(65/100 : ℝ)) := by
  rw [variance_eq]
  have h : (𝔼 x, (f x)^2) ≤ Real.exp (2*b^(65/100 : ℝ)) := by
    have hm := expect_mono (fun x => sq_le_sq₀ (hf x) (Real.exp_pos _).le |>.mpr (hupper x))
    rw [Fintype.expect_const, ← Real.exp_nat_mul] at hm
    norm_num at hm
    convert hm using 1 ; norm_num
  linarith [sq_nonneg (𝔼 x, f x)]


lemma sampler_at_thresholds {b : ℝ} (hb : 1 < b)
    (hlog : Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ) ≤
      (Real.log 2/4)*b^(69/100 : ℝ))
    (hpow : 4/cStar ≤ b^(59/100 : ℝ))
    (hpoly : b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4)
    (hG : Real.log (Fintype.card G) ≤ b^4)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hupper : ∀ x, f x ≤ Real.exp (b^(65/100 : ℝ)))
    (hmean : 1/2 ≤ 𝔼 x, f x) (s : ℕ)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hsb : (s : ℝ) ≤ b) :
    probability (fun w : Fin s → G => ∃ x,
      (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
        (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)) ≤
      Real.exp (-cStar*b^(69/100 : ℝ)) +
        b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) := by
  have hb₀ : 0 < b := zero_lt_one.trans hb
  have hh := half_counts s
  have hθ := theta_pos hb₀ hs
  have hd := delta_pos hb₀
  have hd₁ := delta_lt_one hb
  have hμ : 0 < 𝔼 x, f x := lt_of_lt_of_le (by norm_num) hmean
  have hp := potential_errors_le hb₀ hs hh.2.1 hG hpow hpoly
  have hsample := sampler_explicit_parameters f hf hd hd₁ hθ hμ (s/2) (s-s/2) hp
  have heq : s/2+(s-s/2) = s := by omega
  rw [heq] at hsample
  apply hsample.trans
  apply le_trans (add_le_add (first_stage_ratio_le hb₀ hs hh.1 hmean
    (variance_le_exp hf hupper) hlog) le_rfl)
  exact failure_tail_le hb₀ hs hh.2.2 hsb

end Endpoint





theorem uniform_boolean_sampling :
    ∃ b₀ : ℝ, 1 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      ∀ (G : Type u) [AddCommGroup G] [Fintype G],
        Real.log (Fintype.card G) ≤ b^4 →
        ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) →
        (1/2 ≤ 𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
        ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
        probability (fun w : Fin s → G => ∀ x,
          (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y) ≤
            (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s) ≥
          1-Real.exp (-cStar*b^(69/100 : ℝ))-
            b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ∧
        probability (fun w : Fin s → G => ∃ x,
          (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
            (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)) ≤ b^(-1/2 : ℝ) := by
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp eventually_thresholds
  refine ⟨max b₀ 2, by exact lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb G _ _ hG f hf hupper hmean _ s hs hsb
  obtain ⟨hb₁, hlog, hpow, hpoly, h₁, h₂⟩ := hb₀ b ((le_max_left _ _).trans hb)
  have hfail := sampler_at_thresholds hb₁ hlog hpow hpoly hG f hf hupper hmean s hs hsb
  constructor
  · have hc := probability_compl (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
          (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y))
    simp only [not_exists, not_lt] at hc
    rw [hc]
    linarith
  · exact hfail.trans (failure_tail_le_rpow (zero_lt_one.trans hb₁) h₁ h₂)


end SingleLatticeCovering.Sampler




noncomputable section

open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Bits
universe u v
variable {I : Type u} [Fintype I]


lemma bitMass_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (e : Bool) :
    0 ≤ bitMass q e := by cases e <;> simp [bitMass] <;> linarith

lemma productMass_nonneg {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (e : I → Bool) : 0 ≤ productMass q e :=
  Finset.prod_nonneg (fun i _ => bitMass_nonneg (hq i) (hq1 i) _)

lemma sum_bitMass (q : ℝ) : (∑ e : Bool, bitMass q e) = 1 := by
  rw [Fintype.sum_bool]
  simp [bitMass]

lemma sum_productMass (q : I → ℝ) : (∑ e, productMass q e) = 1 := by
  unfold productMass
  rw [← Fintype.prod_sum]
  simp only [sum_bitMass, Finset.prod_const_one]

lemma integral_const (q : I → ℝ) (c : ℝ) : integral q (fun _ => c) = c := by
  simp only [integral, ← Finset.sum_mul, sum_productMass, one_mul]

lemma integral_add (q : I → ℝ) (f g : (I → Bool) → ℝ) :
    integral q (fun e => f e+g e) = integral q f+integral q g := by
  simp only [integral, mul_add, Finset.sum_add_distrib]

lemma integral_sub (q : I → ℝ) (f g : (I → Bool) → ℝ) :
    integral q (fun e => f e-g e) = integral q f-integral q g := by
  simp only [integral, mul_sub, Finset.sum_sub_distrib]

lemma integral_smul (q : I → ℝ) (c : ℝ) (f : (I → Bool) → ℝ) :
    integral q (fun e => c*f e) = c*integral q f := by
  simp only [integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma integral_sum {J : Type v} [Fintype J] (q : I → ℝ) (f : J → (I → Bool) → ℝ) :
    integral q (fun e => ∑ j, f j e) = ∑ j, integral q (f j) := by
  simp only [integral, Finset.mul_sum]
  exact Finset.sum_comm

lemma integral_mono {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    {f g : (I → Bool) → ℝ} (hfg : ∀ e, f e ≤ g e) : integral q f ≤ integral q g :=
  Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hfg e) (productMass_nonneg hq hq1 e))



lemma integral_prod (q : I → ℝ) (h : I → Bool → ℝ) :
    integral q (fun e => ∏ i, h i (e i)) = ∏ i, ∑ a : Bool, bitMass (q i) a*h i a := by
  simp only [integral, productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => bitMass (q i) a*h i a)).symm


lemma integral_coordinate (q : I → ℝ) (i : I) (h : Bool → ℝ) :
    integral q (fun e => h (e i)) = ∑ a : Bool, bitMass (q i) a*h a := by
  classical
  have hp (e : I → Bool) : h (e i) = ∏ j, if j=i then h (e j) else (1 : ℝ) := by simp
  simp_rw [hp]
  rw [integral_prod q (fun j a => if j=i then h a else 1)]
  have he (j : I) : (∑ a : Bool, bitMass (q j) a*(if j=i then h a else 1)) =
      if j=i then (∑ a : Bool, bitMass (q i) a*h a) else 1 := by
    by_cases hj : j=i
    · subst j; simp only [↓reduceIte]
    · simp only [hj, ↓reduceIte, mul_one, sum_bitMass]
  simp_rw [he]
  simp

lemma integral_two_coordinates (q : I → ℝ) {i j : I} (hij : i ≠ j) (h k : Bool → ℝ) :
    integral q (fun e => h (e i)*k (e j)) =
      (∑ a : Bool, bitMass (q i) a*h a)*(∑ a : Bool, bitMass (q j) a*k a) := by
  classical
  have hp (e : I → Bool) : h (e i)*k (e j) =
      ∏ l, (if l=i then h (e l) else 1)*(if l=j then k (e l) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hp]
  rw [integral_prod q (fun l a => (if l=i then h a else 1)*(if l=j then k a else 1))]
  have he (l : I) :
      (∑ a : Bool, bitMass (q l) a*((if l=i then h a else 1)*(if l=j then k a else 1))) =
      (if l=i then (∑ a : Bool, bitMass (q i) a*h a) else 1)*
      (if l=j then (∑ a : Bool, bitMass (q j) a*k a) else 1) := by
    by_cases hli : l=i
    · subst l
      simp only [hij, ↓reduceIte, mul_one]
    · by_cases hlj : l=j
      · subst l
        simp only [hli, ↓reduceIte, one_mul]
      · simp only [hli, hlj, ↓reduceIte, mul_one, sum_bitMass]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp


lemma count_sub_mean (q : I → ℝ) (e : I → Bool) :
    count e - meanCount q = ∑ i, ((if e i then (1 : ℝ) else 0)-q i) := by
  simp only [count, meanCount, Finset.sum_sub_distrib]

lemma variance_count (q : I → ℝ) :
    integral q (fun e => (count e - meanCount q)^2) = ∑ i, q i*(1-q i) := by
  classical
  have hp (e : I → Bool) : (count e-meanCount q)^2 =
      ∑ i, ∑ j, ((if e i then (1 : ℝ) else 0)-q i)*((if e j then (1 : ℝ) else 0)-q j) := by
    rw [count_sub_mean, pow_two, Finset.sum_mul_sum]
  simp_rw [hp]
  rw [integral_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum, Finset.sum_eq_single i]
  · have hid : (fun e : I → Bool => ((if e i then (1 : ℝ) else 0)-q i)*
        ((if e i then (1 : ℝ) else 0)-q i)) =
      (fun e => ((if e i then (1 : ℝ) else 0)-q i)^2) := by funext e; ring
    rw [hid, integral_coordinate q i (fun a => ((if a then (1 : ℝ) else 0)-q i)^2), Fintype.sum_bool]
    simp only [bitMass, Bool.false_eq_true, ↓reduceIte]
    ring
  · intro j _ hji
    rw [integral_two_coordinates q (Ne.symm hji)
      (fun a => (if a then (1 : ℝ) else 0)-q i) (fun a => (if a then (1 : ℝ) else 0)-q j),
      Fintype.sum_bool, Fintype.sum_bool]
    simp only [bitMass, Bool.false_eq_true, ↓reduceIte]
    ring
  · simp


theorem few_selected_probability {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hmean : 0 < meanCount q) {t : ℝ} (ht : t ≤ meanCount q/2) :
    integral q (fun e => if count e < t then (1 : ℝ) else 0) ≤ 4/meanCount q := by
  have hv : integral q (fun e => (count e-meanCount q)^2) ≤ meanCount q := by
    rw [variance_count]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (q i)]
  have hp : (meanCount q)^2/4 * integral q (fun e => if count e < t then (1 : ℝ) else 0) ≤
      integral q (fun e => (count e-meanCount q)^2) := by
    rw [← integral_smul]
    apply integral_mono hq hq1
    intro e
    split_ifs with he
    · have hh : count e < meanCount q/2 := he.trans_le ht
      nlinarith [sq_nonneg (count e-meanCount q/2)]
    · simp only [mul_zero, sq_nonneg]
  have hpos : 0 < (meanCount q)^2/4 := by positivity
  have hquot : meanCount q / ((meanCount q)^2/4) = 4/meanCount q := by field_simp
  rw [← hquot]
  exact (le_div_iff₀ hpos).mpr (by nlinarith [hp.trans hv])


lemma fairRate_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ fairRate q := by
  unfold fairRate
  exact mul_nonneg (by norm_num) (le_min hq (sub_nonneg.mpr hq1))

lemma fairRate_le_one (q : ℝ) : fairRate q ≤ 1 := by
  unfold fairRate
  have h := min_le_left q (1-q)
  have h' := min_le_right q (1-q)
  linarith

lemma conditionalBit_nonneg (q : ℝ) (s e : Bool) : 0 ≤ conditionalBit q s e := by
  unfold conditionalBit
  split_ifs <;> norm_num

lemma bit_mixture (q : ℝ) (e : Bool) :
    (∑ s : Bool, bitMass (fairRate q) s*conditionalBit q s e) = bitMass q e := by
  rw [Fintype.sum_bool]
  by_cases hq : (1/2 : ℝ) ≤ q
  · have hm : min q (1-q) = 1-q := min_eq_right (by linarith)
    have hd : likelyBit q = true := by simp only [likelyBit, decide_eq_true_eq]; exact hq
    cases e <;> simp only [conditionalBit, hd, fairRate, hm, bitMass, Bool.false_eq_true,
      ↓reduceIte] <;> ring
  · have hm : min q (1-q) = q := min_eq_left (by linarith)
    have hd : likelyBit q = false := by simp only [likelyBit, decide_eq_false_iff_not]; exact hq
    cases e <;> simp only [conditionalBit, hd, fairRate, hm, bitMass, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] <;> ring

lemma conditionalMass_nonneg (q : I → ℝ) (s e : I → Bool) : 0 ≤ conditionalMass q s e :=
  Finset.prod_nonneg (fun _ _ => conditionalBit_nonneg _ _ _)


theorem product_mixture (q : I → ℝ) (e : I → Bool) :
    (∑ s, productMass (fun i => fairRate (q i)) s * conditionalMass q s e) = productMass q e := by
  unfold conditionalMass productMass
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => bitMass (fairRate (q i)) a * conditionalBit (q i) a (e i))]
  simp only [bit_mixture]


theorem integral_mixture (q : I → ℝ) (f : (I → Bool) → ℝ) :
    integral q f = integral (fun i => fairRate (q i))
      (fun s => ∑ e, conditionalMass q s e*f e) := by
  unfold integral
  simp_rw [← product_mixture q, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  ring

end SingleLatticeCovering.Bits



namespace SingleLatticeCovering.Bits
universe u w
variable {I : Type u} [Fintype I]


lemma conditionalMass_split (q : I → ℝ) (s e : I → Bool) :
    conditionalMass q s e =
      (1/2 : ℝ)^(Fintype.card (Selected s)) *
        if (fun j : Frozen s => e j)=(fun j : Frozen s => likelyBit (q j)) then 1 else 0 := by
  classical
  unfold conditionalMass
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => s i=true)]
  have h₁ (j : Selected s) : conditionalBit (q j) (s j) (e j) = (1/2 : ℝ) := by
    simp only [conditionalBit, j.property, ↓reduceIte]
  have h₂ (j : Frozen s) : conditionalBit (q j) (s j) (e j) =
      if e j=likelyBit (q j) then (1 : ℝ) else 0 := by
    simp only [conditionalBit, j.property, Bool.false_eq_true, ↓reduceIte]
  simp_rw [h₁, h₂]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.prod_boole, funext_iff]

lemma conditional_integral_eq_subcube (q : I → ℝ) (s : I → Bool) (f : (I → Bool) → ℝ) :
    (∑ e, conditionalMass q s e*f e) =
      (∑ a : Selected s → Bool, f (filled q s a))/(2 : ℝ)^(Fintype.card (Selected s)) := by
  classical
  calc
    _ = ∑ ab : (Selected s → Bool) × (Frozen s → Bool),
        conditionalMass q s ((cubeSplit s).symm ab)*f ((cubeSplit s).symm ab) :=
      Fintype.sum_equiv (cubeSplit s) _ _ (fun e => by simp only [Equiv.symm_apply_apply])
    _ = ∑ a : Selected s → Bool, (1/2 : ℝ)^(Fintype.card (Selected s))*f (filled q s a) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      have he (d : Frozen s → Bool) :
          (fun j : Frozen s => (cubeSplit s).symm (a,d) j) = d := by
        funext j
        simp [cubeSplit, Equiv.piEquivPiSubtypeProd, j.property]
      simp_rw [conditionalMass_split, he]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, filled]
    _ = _ := by
      rw [← Finset.mul_sum, one_div, inv_pow, div_eq_mul_inv, mul_comm]

lemma count_eq_card_selected (s : I → Bool) : count s = (Fintype.card (Selected s) : ℝ) := by
  classical
  simp [count, Selected, Fintype.card_subtype]



theorem mixture_lower_bound {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (good : (I → Bool) → Prop) [DecidablePred good]
    (f : (I → Bool) → ℝ) (hf : ∀ e, 0 ≤ f e) (a : ℝ) (_ : 0 ≤ a)
    (hgood : ∀ s, good s → a ≤ ∑ e, conditionalMass q s e*f e) :
    (1-integral (fun i => fairRate (q i)) (fun s => if good s then 0 else 1))*a ≤ integral q f := by
  rw [integral_mixture q f]
  have hc : integral (fun i => fairRate (q i)) (fun s => if good s then (1 : ℝ) else 0) =
      1-integral (fun i => fairRate (q i)) (fun s => if good s then 0 else 1) := by
    calc
      _ = integral (fun i => fairRate (q i)) (fun s => 1-(if good s then 0 else 1)) := by
        congr 1
        funext s
        split_ifs <;> norm_num
      _ = _ := by rw [integral_sub, integral_const]

  rw [← hc]
  calc
    _ = integral (fun i => fairRate (q i)) (fun s => if good s then a else 0) := by
      rw [mul_comm, ← integral_smul]
      congr 1
      funext s
      split_ifs <;> ring
    _ ≤ _ := by
      apply integral_mono (fun i => fairRate_nonneg (hq i) (hq1 i)) (fun i => fairRate_le_one (q i))
      intro s
      split_ifs with hs
      · exact hgood s hs
      · exact Finset.sum_nonneg (fun e _ => mul_nonneg (conditionalMass_nonneg _ _ _) (hf e))



lemma expect_restrict {G : Type w} [Fintype G] [Nonempty G] (s : I → Bool)
    (f : (Selected s → G) → ℝ) :
    (𝔼 w : I → G, f (fun j : Selected s => w j)) = 𝔼 v : Selected s → G, f v := by
  classical
  let E := Equiv.piEquivPiSubtypeProd (fun i => s i=true) (fun _ => G)
  calc
    _ = 𝔼 ab : (Selected s → G) × (Frozen s → G), f ab.1 :=
      Fintype.expect_equiv E _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, Fintype.card_prod, Nat.cast_mul,
        Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have h : (Fintype.card (Frozen s → G) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end SingleLatticeCovering.Bits




end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Bits
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Bits
universe u v w
variable {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J]
  [AddCommGroup G] [Fintype G]


lemma fairAverage_reindex {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J] [AddCommGroup G] [Fintype G] (E : I ≃ J) (w : J → G) (f : G → ℝ) (x : G) :
    fairAverage (fun i => w (E i)) f x = fairAverage w f x := by
  classical
  unfold fairAverage
  rw [Fintype.card_congr E]
  congr 1
  let D := Equiv.piCongrLeft (fun _ : J => Bool) E
  apply Fintype.sum_equiv D
  intro e
  congr 2
  unfold groupShift
  apply Fintype.sum_equiv E
  intro i
  simp [D]

lemma filled_groupShift {I : Type u} {G : Type w} [Fintype I] [AddCommGroup G] [Fintype G] (q : I → ℝ) (s : I → Bool) (a : Selected s → Bool) (w : I → G) :
    groupShift w (filled q s a) =
      groupShift (fun j : Selected s => w j) a +
        ∑ j : Frozen s, if likelyBit (q j) then w j else 0 := by
  classical
  unfold groupShift
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => s i=true)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    simp [filled, cubeSplit, Equiv.piEquivPiSubtypeProd, j.property]

lemma conditional_shift_average (q : I → ℝ) (s : I → Bool) (w : I → G) (f : G → ℝ) (x : G) :
    (∑ e, conditionalMass q s e*f (x-groupShift w e)) =
      fairAverage (fun j : Selected s => w j) f
        (x-∑ j : Frozen s, if likelyBit (q j) then w j else 0) := by
  rw [conditional_integral_eq_subcube]
  unfold fairAverage
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [filled_groupShift]
  congr 1
  abel


lemma sampler_finite_index {b : ℝ} (f : G → ℝ) (A δ : ℝ) (hthreshold :
    ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hs : b^(69/100 : ℝ) ≤ (Fintype.card I : ℝ)) (hsb : (Fintype.card I : ℝ) ≤ b) :
    SingleLatticeCovering.Sampler.probability (fun w : I → G => ∃ x, fairAverage w f x < A) ≤ δ := by
  classical
  let E : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let D := Equiv.piCongrLeft (fun _ : I => G) E
  have he : SingleLatticeCovering.Sampler.probability (fun w : I → G => ∃ x, fairAverage w f x < A) =
      SingleLatticeCovering.Sampler.probability (fun w : Fin (Fintype.card I) → G => ∃ x,
        (∑ e : Fin (Fintype.card I) → Bool,
          f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^(Fintype.card I) < A) := by
    unfold SingleLatticeCovering.Sampler.probability
    apply (Fintype.expect_equiv D _ _ _).symm
    intro w
    have ha (x : G) : fairAverage (D w) f x =
        (∑ e : Fin (Fintype.card I) → Bool,
          f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^(Fintype.card I) := by
      rw [← fairAverage_reindex E]
      simp only [D, fairAverage, groupShift, SingleLatticeCovering.Sampler.subsetShift]
      simp only [Fintype.card_fin]
      congr 1
      apply Finset.sum_congr (by ext; simp)
      intro e he
      congr 2
      apply Finset.sum_congr (by ext; simp)
      intro i hi
      simp
    congr 1
    apply propext
    constructor <;> rintro ⟨x, hx⟩ <;> refine ⟨x, ?_⟩
    · rw [ha]
      convert hx using 2
    · rw [ha] at hx
      convert hx using 2
  rw [he]
  exact hthreshold _ hs hsb



lemma badMixture_nonneg {I : Type u} {G : Type w} [Fintype I] [AddCommGroup G] [Fintype G] (b A : ℝ) {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (w : I → G) :
    0 ≤ badMixture b A q f w := by
  unfold badMixture integral
  exact Finset.sum_nonneg (fun s _ => mul_nonneg
    (productMass_nonneg (fun i => fairRate_nonneg (hq i) (hq1 i))
      (fun i => fairRate_le_one (q i)) s) (by dsimp; split_ifs <;> norm_num))

lemma component_failure_mean_le {b A δ : ℝ} (f : G → ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hb : (Fintype.card I : ℝ) ≤ b) (s : I → Bool) :
    (𝔼 w : I → G, if componentGood b A f w s then (0 : ℝ) else 1) ≤
      (if count s < b^(69/100 : ℝ) then 1 else 0)+δ := by
  classical
  by_cases hs : b^(69/100 : ℝ) ≤ (Fintype.card (Selected s) : ℝ)
  · have hcard : (Fintype.card (Selected s) : ℝ) ≤ b :=
      (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hb
    have hfail := sampler_finite_index (I := Selected s) f A δ hthreshold hs hcard
    have he (w : I → G) : (if componentGood b A f w s then (0 : ℝ) else 1) =
        if ∃ x, fairAverage (fun j : Selected s => w j) f x < A then 1 else 0 := by
      have hg : componentGood b A f w s ↔
          ¬∃ x, fairAverage (fun j : Selected s => w j) f x < A := by
        simp only [componentGood, hs, true_and, not_exists, not_lt]
      simp only [hg, ite_not]
    simp_rw [he]
    have hs' : ¬ count s < b^(69/100 : ℝ) := by rw [count_eq_card_selected]; exact not_lt_of_ge hs
    simp only [hs', ↓reduceIte, zero_add]
    calc
      _ = 𝔼 v : Selected s → G, if ∃ x, fairAverage v f x < A then (1 : ℝ) else 0 :=
        expect_restrict s (fun v => if ∃ x, fairAverage v f x < A then (1 : ℝ) else 0)
      _ ≤ δ := by
        unfold SingleLatticeCovering.Sampler.probability at hfail
        convert hfail using 1
        congr 1
        · ext v; simp
        · congr! 10
  · have hs' : count s < b^(69/100 : ℝ) := by rw [count_eq_card_selected]; exact lt_of_not_ge hs
    simp only [componentGood, hs, false_and, ↓reduceIte, hs', Fintype.expect_const]
    linarith



theorem expected_badMixture_le {b A δ : ℝ} {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hb : (Fintype.card I : ℝ) ≤ b)
    (hmean : 0 < meanCount (fun i => fairRate (q i)))
    (ht : b^(69/100 : ℝ) ≤ meanCount (fun i => fairRate (q i))/2) :
    (𝔼 w : I → G, badMixture b A q f w) ≤ 4/meanCount (fun i => fairRate (q i))+δ := by
  classical
  have hex : (𝔼 w : I → G, badMixture b A q f w) =
      integral (fun i => fairRate (q i)) (fun s =>
        𝔼 w : I → G, if componentGood b A f w s then (0 : ℝ) else 1) := by
    unfold badMixture integral
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.mul_expect _ _ _).symm
  rw [hex]
  calc
    _ ≤ integral (fun i => fairRate (q i)) (fun s =>
        (if count s < b^(69/100 : ℝ) then 1 else 0)+δ) :=
      integral_mono (fun i => fairRate_nonneg (hq i) (hq1 i))
        (fun i => fairRate_le_one (q i)) (component_failure_mean_le f hδ hthreshold hb)
    _ = integral (fun i => fairRate (q i)) (fun s =>
        if count s < b^(69/100 : ℝ) then 1 else 0)+δ := by rw [integral_add, integral_const]
    _ ≤ _ := add_le_add_left (few_selected_probability
      (fun i => fairRate_nonneg (hq i) (hq1 i)) (fun i => fairRate_le_one (q i)) hmean ht) δ



theorem biasedAverage_of_badMixture_le {b A ε : ℝ} {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hA : 0 ≤ A) (w : I → G) (hw : badMixture b A q f w ≤ ε) (x : G) :
    (1-ε)*A ≤ biasedAverage q w f x := by
  have h := mixture_lower_bound hq hq1 (componentGood b A f w)
    (fun e => f (x-groupShift w e)) (fun e => hf _) A hA (by
      intro s hs
      rw [conditional_shift_average]
      exact hs.2 _)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hw 1) hA).trans h

end SingleLatticeCovering.Bits





noncomputable section

open scoped BigOperators
open Classical
namespace SingleLatticeCovering.WeightedSelection
universe u v
variable {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W]


lemma mean_loss_le {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W] (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (δ : ℝ)
    (hF : ∀ z, 0 ≤ F z) (hqavg : ∀ z ∈ E, (𝔼 w, q w z) ≤ δ) :
    (𝔼 w, loss F E q w) ≤ δ*mass F E := by
  unfold loss mass
  rw [Finset.expect_comm, Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ E
  · simp only [hz, ↓reduceIte, ← Finset.mul_expect]
    exact (mul_le_mul_of_nonneg_left (hqavg z hz) (hF z)).trans_eq (mul_comm _ _)
  · simp only [hz, ↓reduceIte, Finset.expect_const_zero, mul_zero, le_refl]



theorem choose_usable (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (δ ε : ℝ)
    (hF : ∀ z, 0 ≤ F z) (hq : ∀ w z, 0 ≤ q w z)
    (hqavg : ∀ z ∈ E, (𝔼 w, q w z) ≤ δ) (hε : 0 < ε) :
    ∃ w : W, ∃ U : Finset Z, U ⊆ E ∧
      (∀ z ∈ U, q w z ≤ ε) ∧
      mass F (E \ U) ≤ δ*mass F E/ε ∧
      mass F E - δ*mass F E/ε ≤ mass F U ∧ mass F U ≤ mass F E := by
  classical
  have havg := mean_loss_le F E q δ hF hqavg
  obtain ⟨w,_,hw⟩ := Finset.exists_le_of_expect_le (s := Finset.univ)
    Finset.univ_nonempty havg
  let U := E.filter (fun z => q w z ≤ ε)
  have hsub : U ⊆ E := Finset.filter_subset _ _
  have hgood : ∀ z ∈ U, q w z ≤ ε := fun _ h => (Finset.mem_filter.mp h).2
  have hdisc : ε*mass F (E \ U) ≤ loss F E q w := by
    rw [mass, Finset.mul_expect, loss]
    apply Finset.expect_le_expect
    intro z _
    by_cases hz : z ∈ E \ U
    · obtain ⟨hzE,hzU⟩ := Finset.mem_sdiff.mp hz
      have hbad : ε < q w z := lt_of_not_ge (fun h => hzU (Finset.mem_filter.mpr ⟨hzE,h⟩))
      simp only [hz, hzE, ↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left hbad.le (hF z)]
    · simp only [hz, ↓reduceIte, mul_zero]
      split_ifs <;> first | exact mul_nonneg (hF z) (hq w z) | rfl
  have hsplit : mass F (E \ U)+mass F U=mass F E := by
    unfold mass
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro z _
    by_cases hzU : z ∈ U
    · have hzE := hsub hzU
      simp only [hzU, hzE, Finset.mem_sdiff, not_true_eq_false, and_false,
        ↓reduceIte, zero_add]
    · by_cases hzE : z ∈ E <;> simp [hzU, hzE]
  have hdisc' : mass F (E \ U) ≤ δ*mass F E/ε :=
    (le_div_iff₀ hε).mpr (by linarith [hdisc.trans hw])
  have hdisc0 : 0 ≤ mass F (E \ U) := Finset.expect_nonneg (fun z _ => by
    split_ifs <;> first | exact hF z | rfl)
  exact ⟨w,U,hsub,hgood,hdisc',by linarith,by linarith⟩

end SingleLatticeCovering.WeightedSelection

namespace SingleLatticeCovering.Bits
universe u v w
open Filter
open scoped Topology


lemma alpha_pos : 0 < alpha := inv_pos.mpr (by positivity)

lemma eventually_mixture_parameters : ∀ᶠ b : ℝ in atTop,
    1 < b ∧ b^(69/100 : ℝ) ≤ alpha*b^(70/100 : ℝ) ∧ 3*b^(-1/10 : ℝ) ≤ 1 := by
  have hr := SingleLatticeCovering.Sampler.Numeric.tendsto_rpow_ratio
    (show (69/100 : ℝ) < 70/100 by norm_num)
  have hp := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/10 by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_order.1 hr).2 alpha alpha_pos,
    (tendsto_order.1 hp).2 (1/3) (by norm_num)] with b hb hr hp
  refine ⟨hb, ?_, by linarith⟩
  have hb0 : 0 < b := zero_lt_one.trans hb
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hb0 _)).mp hr.le

variable {I : Type u} {Z : Type v} {G : Type w}
  [Fintype I] [Fintype Z] [AddCommGroup G] [Fintype G]

lemma expected_badMixture_uniform_le {b A : ℝ} (hb : 1 ≤ b) (f : G → ℝ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ b^(-1/2 : ℝ))
    (hcard : (Fintype.card I : ℝ) ≤ b) {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hmean : 2*alpha*b^(70/100 : ℝ) ≤ meanCount (fun i => fairRate (q i)))
    (ht : b^(69/100 : ℝ) ≤ alpha*b^(70/100 : ℝ)) :
    (𝔼 w : I → G, badMixture b A q f w) ≤ (2/alpha+1)*b^(-1/2 : ℝ) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hm0 : 0 < 2*alpha*b^(70/100 : ℝ) := mul_pos (mul_pos (by norm_num) alpha_pos) (Real.rpow_pos_of_pos hb0 _)
  have hm : 0 < meanCount (fun i => fairRate (q i)) := hm0.trans_le hmean
  have hbound := expected_badMixture_le hq hq1 f (Real.rpow_nonneg hb0.le _)
    hthreshold hcard hm (by nlinarith)
  have hrec : 4/meanCount (fun i => fairRate (q i)) ≤
      (2/alpha)*b^(-1/2 : ℝ) := by
    calc
      _ ≤ 4/(2*alpha*b^(70/100 : ℝ)) := div_le_div_of_nonneg_left (by norm_num) hm0 hmean
      _ = (2/alpha)*b^(-70/100 : ℝ) := by
        rw [show (-70/100 : ℝ) = -(70/100 : ℝ) by ring, Real.rpow_neg hb0.le]
        field_simp ; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hb (by norm_num)) (div_nonneg (by norm_num) alpha_pos.le)
  nlinarith





end SingleLatticeCovering.Bits


namespace SingleLatticeCovering.Bits
universe u v w
open Filter
open scoped Topology
theorem usable_anchor_selection_uniform :
    ∃ B : ℝ, 1 < B ∧ ∀ b : ℝ, B ≤ b →
      ∀ (I : Type u) [Fintype I] (Z : Type v) [Fintype Z]
        (G : Type w) [AddCommGroup G] [Fintype G],
      (Fintype.card I : ℝ) ≤ b → Real.log (Fintype.card G) ≤ b^4 →
      ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) →
      (1/2 ≤ 𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
      ∀ (F : Z → ℝ) (E : Finset Z) (q : Z → I → ℝ), (∀ z, 0 ≤ F z) →
        (∀ z i, 0 ≤ q z i) → (∀ z i, q z i ≤ 1) →
        (∀ z ∈ E, 2*alpha*b^(70/100 : ℝ) ≤ meanCount (fun i => fairRate (q z i))) →
      ∃ w : I → G, ∃ U : Finset Z, U ⊆ E ∧
        (∀ z ∈ U, ∀ x, (1-b^(-1/20 : ℝ))*(1-3*b^(-1/10 : ℝ))*(𝔼 y, f y) ≤
          biasedAverage (q z) w f x) ∧
        SingleLatticeCovering.WeightedSelection.mass F (E \ U) ≤
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ∧
        SingleLatticeCovering.WeightedSelection.mass F E -
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ≤
            SingleLatticeCovering.WeightedSelection.mass F U ∧
        SingleLatticeCovering.WeightedSelection.mass F U ≤ SingleLatticeCovering.WeightedSelection.mass F E := by
  classical
  obtain ⟨B₀,hB₀,hS⟩ := SingleLatticeCovering.Sampler.uniform_boolean_sampling.{w}
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp eventually_mixture_parameters
  refine ⟨max B₀ B₁, hB₀.trans_le (le_max_left _ _), ?_⟩
  intro b hb I _ Z _ G _ _ hcard hG f hf hfcap hflo hfhi F E q hF hq hq1 hmean
  obtain ⟨hb1,ht,hδ⟩ := hB₁ b ((le_max_right _ _).trans hb)
  have hb0 : 0 < b := zero_lt_one.trans hb1
  let A : ℝ := (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)
  have hA : 0 ≤ A := mul_nonneg (by linarith) (by linarith)
  have hsam : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ b^(-1/2 : ℝ) := by
    intro s hs hsb
    exact (hS b ((le_max_left _ _).trans hb) G hG f hf hfcap hflo hfhi s hs hsb).2
  have hbad : ∀ z ∈ E, (𝔼 w : I → G, badMixture b A (q z) f w) ≤
      (2/alpha+1)*b^(-1/2 : ℝ) := fun z hz =>
    expected_badMixture_uniform_le hb1.le f hsam hcard (hq z) (hq1 z) (hmean z hz) ht
  obtain ⟨w,U,hUE,hU,hdisc,hmass,hmass'⟩ :=
    SingleLatticeCovering.WeightedSelection.choose_usable F E
      (fun w z => badMixture b A (q z) f w)
      ((2/alpha+1)*b^(-1/2 : ℝ)) (b^(-1/20 : ℝ)) hF
      (fun w z => badMixture_nonneg b A (hq z) (hq1 z) f w) hbad (Real.rpow_pos_of_pos hb0 _)
  have hid : (2/alpha+1)*b^(-1/2 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E /
      b^(-1/20 : ℝ) = (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hb0.le]
    have he : b^(-1/2 : ℝ)*b^((1/20 : ℝ))=b^(-9/20 : ℝ) := by
      rw [← Real.rpow_add hb0]; norm_num
    calc
      _ = (2/alpha+1)*(b^(-1/2 : ℝ)*b^(1/20 : ℝ))*SingleLatticeCovering.WeightedSelection.mass F E := by
        norm_num; ring
      _ = _ := by rw [he]
  refine ⟨w,U,hUE,?_,hid ▸ hdisc,hid ▸ hmass,hmass'⟩
  intro z hz x
  have h := biasedAverage_of_badMixture_le (hq z) (hq1 z) f hf hA w (hU z hz) x
  simpa only [A, mul_assoc] using h

end SingleLatticeCovering.Bits





noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Blocks

universe u v
variable {K : Type u} {V : Type v} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]

lemma lineMax_nonneg {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (v x : V) :
    0 ≤ lineMax (K := K) f v x :=
  (hf (x-(0 : K) • v)).trans (Finset.le_sup' (fun a : K => f (x-a • v)) (Finset.mem_univ (0 : K)))

lemma lineMax_le {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) (v x : V) :
    lineMax (K := K) f v x ≤ c := Finset.sup'_le _ _ (fun _ _ => hf _)

lemma lineMax_le_sum {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (v x : V) :
    lineMax (K := K) f v x ≤ lineSum (K := K) f v x := by
  apply Finset.sup'_le
  intro a ha
  exact Finset.single_le_sum (f := fun b : K => f (x-b • v)) (fun b _ => hf _) ha

lemma mean_lineSum (f : V → ℝ) (v : V) :
    (𝔼 x, lineSum (K := K) f v x) = (Fintype.card K : ℝ) * (𝔼 x, f x) := by
  unfold lineSum
  rw [Finset.expect_sum_comm]
  have ht (a : K) : (𝔼 x, f (x-a • v)) = 𝔼 x, f x :=
    Fintype.expect_equiv (Equiv.subRight (a • v)) _ _ (fun _ => rfl)
  simp only [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


lemma collision_of_two {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {U : Finset V} {v x : V} (hv : v ≠ 0)
    {a b : K} (hab : a ≠ b) (hb : x-b • v ∈ U) :
    collision (K := K) U v (x-a • v) := by
  refine ⟨x-b • v,hb, ?_, a-b, ?_⟩
  · intro heq
    have heq' : b • v = a • v := by exact (sub_right_inj.mp heq)
    exact hab ((smul_left_injective K hv heq').symm)
  · rw [sub_smul]
    abel



attribute [local instance] OAI.SingleLatticeCovering.Blocks.instDecidable_solutions
lemma line_loss_le_collision {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0)
    (v : Direction V) (x : V) :
    lineSum (K := K) f v x - lineMax (K := K) f v x ≤
      ∑ a : K, if collision (K := K) U v (x-a • (v : V)) then f (x-a • (v : V)) else 0 := by
  classical
  by_cases hall : ∀ a : K, x-a • (v : V) ∈ U → collision (K := K) U v (x-a • (v : V))
  · have heq : (∑ a : K, if collision (K := K) U v (x-a • (v : V)) then f (x-a • (v : V)) else 0) =
        lineSum (K := K) f v x := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : x-a • (v : V) ∈ U
      · simp only [hall a ha, ↓reduceIte]
      · simp only [hsupp _ ha, ite_self]
    rw [heq]
    exact sub_le_self _ (lineMax_nonneg hf _ _)
  · push Not at hall
    obtain ⟨a,ha,hac⟩ := hall
    have hzero (b : K) (hb : b ≠ a) : f (x-b • (v : V)) = 0 := by
      apply hsupp
      intro hu
      exact hac (collision_of_two v.property (Ne.symm hb) hu)
    have hsum : lineSum (K := K) f v x = f (x-a • (v : V)) := by
      rw [lineSum, Finset.sum_eq_single a]
      · intro b _ hb
        exact hzero b hb
      · simp
    have hmax : f (x-a • (v : V)) ≤ lineMax (K := K) f v x :=
      Finset.le_sup' (fun a : K => f (x-a • (v : V))) (Finset.mem_univ a)
    apply le_trans (b := 0)
    · rw [hsum]
      exact sub_nonpos.mpr hmax
    · exact Finset.sum_nonneg (fun b _ => by split_ifs <;> simp only [hf, le_refl])


lemma direction_point_prob (z : V) :
    (𝔼 v : Direction V, if (v : V)=z then (1 : ℝ) else 0) ≤
      1 / (Fintype.card (Direction V) : ℝ) := by
  classical
  by_cases hz : z=0
  · subst z
    have he (v : Direction V) : (if (v : V)=0 then (1 : ℝ) else 0) = 0 := ite_eq_right v.property
    simp only [he, Finset.expect_const_zero]
    positivity
  · have heq (v : Direction V) : (v : V)=z ↔ v=⟨z,hz⟩ := ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [heq, Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, le_refl]

lemma collision_indicator_le {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] (U : Finset V) (v : Direction V) (z : V) :
    (if collision (K := K) U v z then (1 : ℝ) else 0) ≤
      ∑ w ∈ U, ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
  classical
  by_cases hc : collision (K := K) U v z
  · obtain ⟨w,hw,hwz,a,ha⟩ := hc
    have ha0 : a ≠ 0 := by
      intro h; rw [h,zero_smul] at ha
      exact hwz (sub_eq_zero.mp ha.symm)
    have hv : (v : V)=a⁻¹ • (w-z) := by rw [← ha, inv_smul_smul₀ ha0]
    calc
      _ = 1 := ite_eq_left ⟨w,hw,hwz,a,ha⟩
      _ ≤ ∑ b : Direction K, if (v : V)=(b : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
        apply le_trans (b := if (v : V)=a⁻¹ • (w-z) then (1 : ℝ) else 0)
        · simp only [hv, ↓reduceIte, le_refl]
        · exact Finset.single_le_sum (f := fun b : Direction K =>
            if (v : V)=(b : K)⁻¹ • (w-z) then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ ⟨a,ha0⟩)
      _ ≤ _ := Finset.single_le_sum (f := fun w => ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0)
        (fun w _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) hw
  · simp only [hc, ↓reduceIte]
    exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))



lemma collision_probability_le (U : Finset V) (z : V) :
    (𝔼 v : Direction V, if collision (K := K) U v z then (1 : ℝ) else 0) ≤
      (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) := by
  classical
  calc
    _ ≤ 𝔼 v : Direction V, ∑ w ∈ U, ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun v _ => collision_indicator_le U v z)
    _ = ∑ w ∈ U, ∑ a : Direction K, 𝔼 v : Direction V,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      exact Finset.expect_sum_comm _ _ _
    _ ≤ ∑ w ∈ U, ∑ a : Direction K, 1/(Fintype.card (Direction V) : ℝ) :=
      Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun a _ => direction_point_prob _))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

lemma mean_line_loss_le {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0)
    (v : Direction V) :
    (Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x) ≤
      (Fintype.card K : ℝ)*(𝔼 z, if collision (K := K) U v z then f z else 0) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun x : V => fun _ => line_loss_le_collision (K := K) hf hsupp v x)
  rw [Finset.expect_sub_distrib, mean_lineSum] at h
  change (Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x) ≤
    (𝔼 x, lineSum (K := K) (fun z => if collision (K := K) U v z then f z else 0) v x) at h
  rwa [mean_lineSum] at h



lemma mean_direction_loss_le {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0) :
    (𝔼 v : Direction V,
      ((Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x))) ≤
      ((U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) := by
  classical
  let e : ℝ := (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)
  calc
    (𝔼 v : Direction V, ((Fintype.card K : ℝ)*(𝔼 x, f x) -
      (𝔼 x, lineMax (K := K) f (v : V) x))) ≤ 𝔼 v : Direction V,
        (Fintype.card K : ℝ)*(𝔼 z, if collision (K := K) U v z then f z else 0) :=
      Finset.expect_le_expect (fun v _ => mean_line_loss_le (K := K) hf hsupp v)
    _ = (Fintype.card K : ℝ) * (𝔼 z, f z * (𝔼 v : Direction V,
        if collision (K := K) U v z then (1 : ℝ) else 0)) := by
      rw [← Finset.mul_expect, Finset.expect_comm]
      congr 1
      apply Finset.expect_congr rfl
      intro z _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro v _
      split_ifs <;> simp
    _ ≤ (Fintype.card K : ℝ) * (𝔼 z, f z * e) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.expect_le_expect (fun z _ => mul_le_mul_of_nonneg_left
        (collision_probability_le U z) (hf z))
    _ = ((U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) := by rw [← Finset.expect_mul]; dsimp [e]; ring




theorem exists_sparse_line [Nontrivial V] {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0) :
    ∃ v : Direction V,
      (1-(U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) ≤ (𝔼 x, lineMax (K := K) f v x) ∧
      (𝔼 x, lineMax (K := K) f v x) ≤ (Fintype.card K : ℝ)*(𝔼 x, f x) := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  let : Nonempty (Direction V) := ⟨⟨v,hv⟩⟩
  obtain ⟨v,_,hv⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty
    (mean_direction_loss_le (K := K) hf hsupp)
  refine ⟨v, by linarith, ?_⟩
  rw [← mean_lineSum (K := K) f v]
  exact Finset.expect_le_expect (fun x _ => lineMax_le_sum hf _ _)

lemma card_direction (W : Type*) [Zero W] [Fintype W] :
    Fintype.card (Direction W) = Fintype.card W - 1 := by
  classical
  simpa only [Direction, Fintype.card_unique] using Fintype.card_subtype_compl (fun w : W => w=0)

lemma collision_factor_le_twice {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] [Nontrivial V] (U : Finset V) :
    (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) ≤
      2*(Fintype.card K : ℝ)*((U.card : ℝ)/(Fintype.card V : ℝ)) := by
  have hV : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hK : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [card_direction K, card_direction V, Nat.cast_sub hK, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
  norm_num only [Nat.cast_one]
  have hV' : (2 : ℝ) ≤ Fintype.card V := Nat.cast_le.mpr hV
  have hK' : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast hK
  have hc : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < (Fintype.card V : ℝ)-1)).mpr
  have hVp : (0 : ℝ) < Fintype.card V := by linarith
  field_simp
  nlinarith [mul_nonneg hc (by linarith : 0 ≤ (Fintype.card K : ℝ)),
    mul_nonneg hc (by nlinarith : 0 ≤ (Fintype.card K : ℝ)*((Fintype.card V : ℝ)-2))]


lemma mean_sparseWeight {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] (U : Finset V) (F : V → ℝ) :
    (Fintype.card K : ℝ)*(𝔼 z, sparseWeight (K := K) U F z) = usableMass U F := by
  have hp : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro z _
  simp only [sparseWeight]
  split_ifs <;> field_simp ; simp

lemma usable_density_le {V : Type v} [AddCommGroup V] [Fintype V] {U : Finset V} {F : V → ℝ} {a : ℝ} (ha : 0 < a)
    (hF : ∀ z ∈ U, a ≤ F z) :
    (U.card : ℝ)/(Fintype.card V : ℝ) ≤ usableMass U F / a := by
  have hm : (𝔼 z, if z ∈ U then (1 : ℝ) else 0) = (U.card : ℝ)/(Fintype.card V : ℝ) := by
    simp [Fintype.expect_eq_sum_div_card]
  rw [← hm, le_div_iff₀ ha, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ U
  · simp only [hz, ↓reduceIte, one_mul]
    exact hF z hz
  · simp only [hz, ↓reduceIte, zero_mul, le_refl]




theorem gaussian_window_sparse_line [Nontrivial V] (U : Finset V) (F : V → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (t r : ℝ)
    (hFl : ∀ z ∈ U, Real.exp (t-r) ≤ F z)
    (hFu : ∀ z ∈ U, F z ≤ Real.exp (t+r))
    (hpl : Real.exp (t-4*r) ≤ (Fintype.card K : ℝ))
    (hpu : (Fintype.card K : ℝ) ≤ Real.exp (t-3*r))
    (hM : usableMass U F ≤ 2) :
    ∃ v : Direction V,
      usableMass U F - 4*usableMass U F*Real.exp (-2*r) ≤
        (𝔼 x, lineMax (K := K) (sparseWeight (K := K) U F) v x) ∧
      (𝔼 x, lineMax (K := K) (sparseWeight (K := K) U F) v x) ≤ usableMass U F ∧
      ∀ x, 0 ≤ lineMax (K := K) (sparseWeight (K := K) U F) v x ∧
        lineMax (K := K) (sparseWeight (K := K) U F) v x ≤ Real.exp (5*r) := by
  classical
  have hp : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hweight0 (z : V) : 0 ≤ sparseWeight (K := K) U F z := by
    unfold sparseWeight
    split_ifs
    · exact div_nonneg (hF0 z) hp.le
    · rfl
  have hweightsupp (z : V) (hz : z ∉ U) : sparseWeight (K := K) U F z = 0 := by
    simp only [sparseWeight, hz, ↓reduceIte]
  have hM0 : 0 ≤ usableMass U F := Finset.expect_nonneg (fun z _ => by
    split_ifs <;> simp only [hF0, le_refl])
  have hratio : (Fintype.card K : ℝ)/Real.exp (t-r) ≤ Real.exp (-2*r) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    convert hpu using 1 ; congr 1 ; ring
  have hsmall : (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) ≤
      4*Real.exp (-2*r) := by
    calc
      _ ≤ 2*(Fintype.card K : ℝ)*((U.card : ℝ)/(Fintype.card V : ℝ)) := collision_factor_le_twice U
      _ ≤ 2*(Fintype.card K : ℝ)*(usableMass U F / Real.exp (t-r)) :=
        mul_le_mul_of_nonneg_left (usable_density_le (Real.exp_pos _) hFl) (by positivity)
      _ = 2*usableMass U F*((Fintype.card K : ℝ)/Real.exp (t-r)) := by ring
      _ ≤ 2*usableMass U F*Real.exp (-2*r) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ 4*Real.exp (-2*r) := by nlinarith [Real.exp_pos (-2*r)]
  obtain ⟨v,hv,hvu⟩ := exists_sparse_line (K := K) hweight0 hweightsupp
  rw [mean_sparseWeight] at hv hvu
  refine ⟨v, ?_, hvu, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hsmall hM0
    nlinarith
  · intro x
    refine ⟨lineMax_nonneg hweight0 _ _, lineMax_le (fun z => ?_) _ _⟩
    unfold sparseWeight
    split_ifs with hz
    · calc
        F z / (Fintype.card K : ℝ) ≤ Real.exp (t+r) / (Fintype.card K : ℝ) :=
          div_le_div_of_nonneg_right (hFu z hz) hp.le
        _ ≤ Real.exp (t+r) / Real.exp (t-4*r) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hpl
        _ = Real.exp (5*r) := by rw [← Real.exp_sub]; congr 1; ring
    · exact (Real.exp_pos _).le

end SingleLatticeCovering.Blocks





end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Lines
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Folded
open ConstructionA MeasureTheory Filter Topology
open scoped BigOperators
universe u
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gridMass_eq_usableMass {p : ℕ} [NeZero p] (h : ℝ) (E : Finset (ι → ZMod p)) :
    gridMass h p E = Blocks.usableMass E (fun z => folded h (anchor p z)) := by
  classical
  unfold gridMass Blocks.usableMass
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, div_eq_mul_inv,
    ←Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [inv_pow]
  ring

lemma probability_eq_bitMass {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    probability h t e = Bits.bitMass (probability h t true) e := by
  cases e
  · simp only [Bits.bitMass, Bool.false_eq_true, ↓reduceIte]
    linarith [probability_sum hh t]
  · simp only [Bits.bitMass, ↓reduceIte]

lemma wordMass_eq_productMass {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool) :
    wordMass h t e = Bits.productMass (fun j => probability h (t j) true) e := by
  unfold wordMass Bits.productMass
  apply Finset.prod_congr rfl
  intro j _
  exact probability_eq_bitMass hh _ _

lemma mean_fairRate_lower {ι : Type*} [Fintype ι] [DecidableEq ι] {h r : ℝ} (hh : 0 < h) (t : ι → ℝ)
    (hN : r ≤ ((Finset.univ.filter fun j => |t j-1/2| ≤ (h^2)⁻¹).card : ℝ)) :
    2*Bits.alpha*r ≤ Bits.meanCount (fun j => Bits.fairRate (probability h (t j) true)) := by
  classical
  let S := Finset.univ.filter fun j => |t j-1/2| ≤ (h^2)⁻¹
  have hsum : (2*Bits.alpha)*(S.card : ℝ) ≤
      ∑ j ∈ S, Bits.fairRate (probability h (t j) true) := by
    calc
      _ = ∑ _j ∈ S, 2*Bits.alpha := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := probability_central hh (Finset.mem_filter.mp hj).2 true
        unfold Bits.fairRate
        apply mul_le_mul_of_nonneg_left (le_min ht.1 (by change alpha ≤ _; linarith)) (by norm_num)
  have hall : (∑ j ∈ S, Bits.fairRate (probability h (t j) true)) ≤
      Bits.meanCount (fun j => Bits.fairRate (probability h (t j) true)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro j _ _
    exact Bits.fairRate_nonneg (probability_pos hh _ _).le (probability_le_one hh _ _)
  exact (mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) Bits.alpha_pos.le)).trans (hsum.trans hall)

lemma eligible_window {p : ℕ} [NeZero p] {h μ D r : ℝ} (hh : 0 < h)
    {z : ι → ZMod p} (hz : z ∈ gridEligible h μ D r p) :
    Real.exp ((Fintype.card ι : ℝ)*μ-D) ≤ folded h (anchor p z) ∧
    folded h (anchor p z) ≤ Real.exp ((Fintype.card ι : ℝ)*μ+D) := by
  classical
  have he := (Finset.mem_filter.mp hz).2.1
  have hl : (Fintype.card ι : ℝ)*μ-D ≤ Real.log (folded h (anchor p z)) := by linarith [(abs_le.mp he).1]
  have hu : Real.log (folded h (anchor p z)) ≤ (Fintype.card ι : ℝ)*μ+D := by linarith [(abs_le.mp he).2]
  exact ⟨(Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (folded_pos hh _)),
    (Real.exp_log (folded_pos hh _)).symm.trans_le (Real.exp_le_exp.mpr hu)⟩

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA Blocks
open scoped BigOperators

lemma eventually_previous_cap : ∀ᶠ b : ℝ in atTop, ∀ a : ℝ, 1 ≤ a →
    a ≤ b^((1 : ℝ)/(9/10)) → 5*a^(56/100 : ℝ) ≤ b^(65/100 : ℝ) := by
  filter_upwards [eventually_rpow_ratio_bound (by norm_num : ((1 : ℝ)/(9/10))*(56/100) < 65/100)
    (by norm_num : (0 : ℝ) < 1/5), eventually_gt_atTop (0 : ℝ)] with b hb hb0
  intro a ha hab
  have ht := Real.rpow_le_rpow (show 0 ≤ a by linarith) hab (by norm_num : (0 : ℝ) ≤ 56/100)
  rw [←Real.rpow_mul hb0.le] at ht
  linarith

lemma eventually_line_collision : ∀ᶠ b : ℝ in atTop,
    Real.exp (-2*b^(56/100 : ℝ)) ≤ b^(-(1/20 : ℝ)) := by
  have ht := Sampler.Numeric.tendsto_rpow_mul_exp_neg_rpow (1/20 : ℝ)
    (by norm_num : (0 : ℝ) < 56/100) (by norm_num : (0 : ℝ) < 2)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  rw [Real.rpow_neg hb0.le]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hb0 (1/20 : ℝ))).mpr
  simpa only [mul_comm] using hb.le

lemma window_line_choice {b p : ℕ} (hb : 1 ≤ b) [Fact p.Prime]
    (U : Finset (Fin b → ZMod p)) (hU : U ⊆ gridEligible (height b) (logMean (height b))
      ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p)
    (hh : 0 < height b)
    (hpl : (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p)
    (hpu : Real.log p ≤ (b : ℝ)*logMean (height b)-3*(b : ℝ)^(56/100 : ℝ))
    (hM : usableMass U (fun z => folded (height b) (anchor p z)) ≤ 2) :
    ∃ v : Direction (Fin b → ZMod p),
      usableMass U (fun z => folded (height b) (anchor p z)) -
        4*usableMass U (fun z => folded (height b) (anchor p z))*Real.exp (-2*(b : ℝ)^(56/100 : ℝ)) ≤
        (𝔼 x, lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x) ∧
      (𝔼 x, lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x) ≤
        usableMass U (fun z => folded (height b) (anchor p z)) ∧
      ∀ x, 0 ≤ lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x ∧
        lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (fun z => folded (height b) (anchor p z))) v x ≤
          Real.exp (5*(b : ℝ)^(56/100 : ℝ)) := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0,by omega⟩⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply gaussian_window_sparse_line U (fun z => folded (height b) (anchor p z))
    (fun z => (folded_pos hh _).le) ((b : ℝ)*logMean (height b)) ((b : ℝ)^(56/100 : ℝ))
    (fun z hz => by simpa only [Fintype.card_fin] using (eligible_window hh (hU hz)).1)
    (fun z hz => by simpa only [Fintype.card_fin] using (eligible_window hh (hU hz)).2)
    _ _ hM
  · simpa only [ZMod.card, Real.exp_log hp0] using Real.exp_le_exp.mpr hpl
  · simpa only [ZMod.card, Real.exp_log hp0] using Real.exp_le_exp.mpr hpu

lemma line_mean_error {M g D ε τ : ℝ} (hM : |M-1| ≤ D*ε) (hM2 : M ≤ 2)
    (hτ : 0 ≤ τ) (hτε : τ ≤ ε) (hgl : M-4*M*τ ≤ g) (hgu : g ≤ M) :
    |g-1| ≤ (D+8)*ε := by
  have hε : 0 ≤ ε := hτ.trans hτε
  have hmul := mul_le_mul_of_nonneg_right hM2 hτ
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hM).1,(abs_le.mp hM).2]

lemma usable_mass_error {M U C b : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hM : |M-1| ≤ 7*b^(-(1/20 : ℝ))) (hM2 : M ≤ 2)
    (hu : M-C*b^(-(9/20 : ℝ))*M ≤ U) (hu' : U ≤ M) :
    |U-1| ≤ (7+2*C)*b^(-(1/20 : ℝ)) := by
  have he := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(9/20 : ℝ)) ≤ -(1/20 : ℝ))
  have hp : 0 ≤ b^(-(9/20 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hs := mul_le_mul_of_nonneg_left he hC
  have hm := mul_le_mul_of_nonneg_left hM2 (mul_nonneg hC hp)
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hM).1,(abs_le.mp hM).2,
    mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/20 : ℝ)))]

lemma sampler_factor_lower {b A : ℝ} (hb : 1 ≤ b) (hA : 4 ≤ A) :
    1-A*b^(-(1/100 : ℝ)) ≤ (1-b^(-(1/20 : ℝ)))*(1-3*b^(-(1/10 : ℝ))) := by
  have h1 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(1/20 : ℝ)) ≤ -(1/100 : ℝ))
  have h2 := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (-(1/10 : ℝ)) ≤ -(1/100 : ℝ))
  have h3 := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/100 : ℝ)))
  nlinarith [mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/20 : ℝ)))
    (Real.rpow_nonneg (by linarith : 0 ≤ b) (-(1/10 : ℝ)))]

end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA Blocks
open scoped BigOperators
universe u




theorem eventually_usable_gaussian : ∃ A : ℝ, 0 < A ∧
    ∀ᶠ b : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime],
      (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
      Real.log p ≤ (b : ℝ)*logMean (height b)-3*(b : ℝ)^(56/100 : ℝ) →
      ∀ (H : Type u) [AddCommGroup H] [Fintype H], Real.log (Fintype.card H) ≤ (b : ℝ)^4 →
      ∀ a : ℝ, 1 ≤ a → a ≤ (b : ℝ)^((1 : ℝ)/(9/10)) →
      ∀ f : H → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (5*a^(56/100 : ℝ))) →
      1/2 ≤ (𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
      ∃ w : Fin b → H, ∃ U : Finset (Fin b → ZMod p), ∃ v : Direction (Fin b → ZMod p),
        U ⊆ eligible b p ∧
        (∀ z ∈ U, ∀ x, (1-A*(b : ℝ)^(-(1/100 : ℝ)))*(𝔼 y, f y) ≤
          ∑ e, wordMass (height b) (anchor p z) e * f (x-Bits.groupShift w e)) ∧
        |usableMass U (anchorWeight b p)-1| ≤ A*(b : ℝ)^(-(1/20 : ℝ)) ∧
        |(𝔼 x, blockFunction b p U v x)-1| ≤ A*(b : ℝ)^(-(1/100 : ℝ)) ∧
        ∀ x, 0 ≤ blockFunction b p U v x ∧ blockFunction b p U v x ≤ Real.exp (5*(b : ℝ)^(56/100 : ℝ)) := by
  classical
  obtain ⟨Bs,hBs,hsel⟩ := Bits.usable_anchor_selection_uniform.{0,0,u}
  let C : ℝ := 2/Bits.alpha+1
  let D : ℝ := 7+2*C
  let A : ℝ := D+8
  have hC : 0 ≤ C := by dsimp [C]; exact add_nonneg (div_nonneg (by norm_num) Bits.alpha_pos.le) (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hA : 4 ≤ A := by dsimp [A,D]; linarith
  refine ⟨A,by linarith,?_⟩
  have he : ∀ᶠ b : ℝ in atTop, 7*b^(-(1/20 : ℝ)) ≤ 1 := by
    filter_upwards [(tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/7))] with b hb
    linarith
  filter_upwards [eventually_grid_mass, height_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Bs),
    tendsto_natCast_atTop_atTop.eventually eventually_previous_cap,
    tendsto_natCast_atTop_atTop.eventually eventually_line_collision,
    tendsto_natCast_atTop_atTop.eventually he, eventually_ge_atTop (2 : ℕ)]
    with b hmass hh hbs hprev hcol he hb
  intro p inst hpl hpu H _ _ hH a ha hab f hf hcap hflo hfhi
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hh0 : 0 < height b := by linarith
  let F := anchorWeight b p
  let E := eligible b p
  have hF : ∀ z, 0 ≤ F z := fun z => (folded_pos hh0 _).le
  have herr := (hmass p (Fact.out : p.Prime).pos hpl).2
  rw [gridMass_eq_usableMass] at herr
  change |usableMass E F-1| ≤ 7*(b : ℝ)^(-(1/20 : ℝ)) at herr
  have hM2 : usableMass E F ≤ 2 := by linarith [(abs_le.mp herr).2]
  have hfcap : ∀ x, f x ≤ Real.exp ((b : ℝ)^(65/100 : ℝ)) := fun x =>
    (hcap x).trans (Real.exp_le_exp.mpr (hprev a ha hab))
  obtain ⟨w,U,hUE,hU,hdisc,hMU,hMU'⟩ := hsel (b : ℝ) hbs (Fin b) (Fin b → ZMod p) H
    (by simp only [Fintype.card_fin,le_refl]) hH f hf hfcap hflo hfhi F E
    (fun z j => probability (height b) (anchor p z j) true) hF
    (fun z j => (probability_pos hh0 _ _).le) (fun z j => probability_le_one hh0 _ _)
    (fun z hz => mean_fairRate_lower hh0 _ (Finset.mem_filter.mp hz).2.2)
  have hMU0 : usableMass E F-C*(b : ℝ)^(-(9/20 : ℝ))*usableMass E F ≤ usableMass U F := by
    simpa only [C, WeightedSelection.mass, usableMass, neg_div] using hMU
  clear hMU
  have hMU := hMU0
  change usableMass U F ≤ usableMass E F at hMU'
  have hUE' : U ⊆ gridEligible (height b) (logMean (height b))
      ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p := hUE
  obtain ⟨v,hvl,hvu,hv⟩ := window_line_choice (show 1 ≤ b by omega) U hUE' hh0 hpl hpu (hMU'.trans hM2)
  have huerr : |usableMass U F-1| ≤ D*(b : ℝ)^(-(1/20 : ℝ)) :=
    usable_mass_error hb1 hC herr hM2 hMU hMU'
  have hverr := line_mean_error huerr (hMU'.trans hM2) (Real.exp_pos _).le hcol hvl hvu
  refine ⟨w,U,v,hUE,?_,?_,?_,hv⟩
  · intro z hz x
    have h := hU z hz x
    have hfactor := mul_le_mul_of_nonneg_right (sampler_factor_lower hb1 hA)
      (show 0 ≤ 𝔼 y, f y by linarith)
    refine le_trans hfactor ?_
    simp only [mul_assoc, neg_div, Bits.biasedAverage, Bits.integral, ←wordMass_eq_productMass hh0] at h
    convert h using 1
    all_goals try simp only [mul_assoc]
    all_goals try rfl
    all_goals
      apply Finset.sum_congr
      · ext e; simp
      · intro e he; rfl
  · exact huerr.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
      (Real.rpow_nonneg (by linarith) _))
  · exact hverr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)) (by linarith : 0 ≤ A))


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Filter Topology


lemma balanced_probability {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool) :
    wordMass h t e ≤ exp (-alpha*(balanced h t).card) := by
  apply wordMass_le_exp_card hh t e (balanced h t)
  intro j hj
  exact (Finset.mem_filter.mp hj).2


lemma window_atom {h p m r N : ℝ} (hh : 0 < h) (hp : 0 < p) (t : ι → ℝ)
    (hF : folded h t ≤ exp (m+r)) (hprime : exp (m-4*r) ≤ p)
    (hN : N ≤ ((balanced h t).card : ℝ)) (e : ι → Bool) :
    folded h t / p * wordMass h t e ≤ exp (5*r-alpha*N) := by
  have hratio : folded h t / p ≤ exp (5*r) := by
    calc
      _ ≤ exp (m+r)/p := div_le_div_of_nonneg_right hF hp.le
      _ ≤ exp (m+r)/exp (m-4*r) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hprime
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hprob : wordMass h t e ≤ exp (-alpha*N) := by
    apply (balanced_probability hh t e).trans
    apply Real.exp_le_exp.mpr
    nlinarith [alpha_pos]
  calc
    _ ≤ exp (5*r)*exp (-alpha*N) := mul_le_mul hratio hprob
      (Finset.prod_nonneg (fun j _ => (probability_pos hh _ _).le)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma eventually_atom_exponent :
    ∀ᶠ b : ℝ in atTop, 5*b^(56/100 : ℝ)+1 ≤ (alpha/2)*b^(70/100 : ℝ) := by
  have hratio : Tendsto (fun b : ℝ => b^(56/100 : ℝ)/b^(70/100 : ℝ)) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 14/100)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    rw [← Real.rpow_sub hb]
    norm_num
  have hinv := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 70/100)).inv_tendsto_atTop
  have ht : Tendsto (fun b : ℝ => (5*b^(56/100 : ℝ)+1)/b^(70/100 : ℝ)) atTop (𝓝 0) := by
    convert (hratio.const_mul 5).add hinv using 1 <;> try norm_num
    funext b
    ring
  filter_upwards [ht.eventually (gt_mem_nhds (div_pos alpha_pos (by norm_num) : 0 < alpha/2)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hb0 _)).mp hb).le




end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.ConstructionA
open SingleLatticeCovering.Folded SingleLatticeCovering.Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma anchor_mem_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) (z : ι → ZMod p) (j : ι) :
    anchor p z j ∈ Set.Icc 0 1 := by
  let : NeZero p := ⟨hp.ne'⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨div_nonneg (Nat.cast_nonneg _) hp0.le, ?_⟩
  apply (div_le_one hp0).mpr
  exact_mod_cast (ZMod.val_lt (z j)).le


lemma lineMax_anchor {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime] (U : Finset (ι → ZMod p))
    (F : (ι → ZMod p) → ℝ) (v x : ι → ZMod p)
    (hg : 0 < lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x) :
    ∃ z ∈ U, x-z ∈ Submodule.span (ZMod p) {v} ∧
      lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x = F z / p := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a : ZMod p => sparseWeight (K := ZMod p) U F (x-a • v))
  have hae : lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U F) v x =
      sparseWeight (K := ZMod p) U F (x-a • v) := ha
  have hz : x-a • v ∈ U := by
    by_contra hz
    simp only [hae, sparseWeight, hz, ↓reduceIte] at hg
    exact lt_irrefl _ hg
  refine ⟨x-a • v,hz,?_,?_⟩
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨a,rfl⟩
  · simp only [hae, sparseWeight, hz, ↓reduceIte, ZMod.card]



theorem gaussian_cell {p : ℕ} [Fact p.Prime] {h : ℝ} (hh : 0 < h)
    (U : Finset (ι → ZMod p)) (v : ι → ZMod p) (τ : ι → ℝ)
    (hg : 0 < lineMax (K := ZMod p)
      (sparseWeight (K := ZMod p) U (fun z => folded h (anchor p z))) v
      (residue p (floorVector p τ))) :
    ∃ z ∈ U, ∃ lam : ι → ℝ,
      lam ∈ codeLattice p (Submodule.span (ZMod p) {v}) ∧
      τ-lam ∈ gridCell p z ∧
      lineMax (K := ZMod p)
        (sparseWeight (K := ZMod p) U (fun z => folded h (anchor p z))) v
        (residue p (floorVector p τ)) = folded h (anchor p z)/(p : ℝ) ∧
      ∀ e : ι → Bool,
        lam+(fun j => bitValue (e j)) ∈ codeLattice p (Submodule.span (ZMod p) {v}) ∧
        (∀ j, |h*(τ j-lam j-bitValue (e j))| ≤ h) ∧
        exp (-((Fintype.card ι : ℝ)*h^2/(p : ℝ))) *
          (folded h (anchor p z)/(p : ℝ)*wordMass h (anchor p z) e) ≤
            atom h (τ-lam) e/(p : ℝ) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨z,hz,hC,hmax⟩ := lineMax_anchor U (fun z => folded h (anchor p z)) v _ hg
  refine ⟨z,hz,cellPoint p τ z,cellPoint_mem p _ τ z hC,
    cell_residual_mem_grid p hp τ z,hmax,?_⟩
  intro e
  obtain ⟨hmem,hres⟩ := cell_bits p hp (Submodule.span (ZMod p) {v}) τ z hC e
  refine ⟨hmem,?_,?_⟩
  · intro j
    rw [abs_mul, abs_of_pos hh]
    exact mul_le_of_le_one_right hh.le (abs_le.mpr (hres j))
  · have hτ : ∀ j, (τ-cellPoint p τ z) j ∈ Set.Icc 0 1 := fun j =>
      ⟨(gridCell_subset_cube p hp z _ (cell_residual_mem_grid p hp τ z) j).1,
        (gridCell_subset_cube p hp z _ (cell_residual_mem_grid p hp τ z) j).2.le⟩
    have hd : ∀ j, |(τ-cellPoint p τ z) j-anchor p z j| ≤ (p : ℝ)⁻¹ := by
      intro j
      have hj := cell_residual_mem_grid p hp τ z j
      rw [abs_of_nonneg hj.1]
      exact hj.2.le
    have hr := (rounding hh (anchor p z) (τ-cellPoint p τ z) e
      (anchor_mem_cube p hp z) hτ hd).2.2.1
    have he : (Fintype.card ι : ℝ)*h^2*(p : ℝ)⁻¹ = (Fintype.card ι : ℝ)*h^2/(p : ℝ) := by ring
    rw [he] at hr
    calc
      _ = (exp (-((Fintype.card ι : ℝ)*h^2/(p : ℝ))) *
          (folded h (anchor p z)*wordMass h (anchor p z) e))/(p : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hr hp0.le


end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA
open scoped BigOperators



theorem eventually_eligible_atom : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ b : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime],
      (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
      ∀ z ∈ eligible b p, ∀ t : Fin b → ℝ, t ∈ gridCell p z →
      ∀ e : Fin b → Bool,
        folded (height b) (anchor p z)/p*wordMass (height b) (anchor p z) e ≤
          Real.exp (-c*(b : ℝ)^(70/100 : ℝ)) ∧
        atom (height b) t e/p ≤ Real.exp (-c*(b : ℝ)^(70/100 : ℝ)) := by
  classical
  refine ⟨alpha/2,div_pos alpha_pos (by norm_num),?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_atom_exponent,
    tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
    eventually_ge_atTop (2 : ℕ)] with b hb hs hb2
  intro p _ hpl z hz t ht e
  have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  have hh : 0 < height b := heightR_pos (by exact_mod_cast (show 1 < b by omega))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs' := hs p hp0 hpl
  have hη : (b : ℝ)*height b^2/p ≤ 1 := hs'.1.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hb1 (by norm_num))
  have hF := (eligible_window hh hz).2
  have hN : (b : ℝ)^(70/100 : ℝ) ≤ ((balanced (height b) (anchor p z)).card : ℝ) :=
    (Finset.mem_filter.mp hz).2.2
  have hprime : Real.exp ((b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ)) ≤ p :=
    (Real.exp_le_exp.mpr hpl).trans_eq (Real.exp_log hp0)
  have he := window_atom hh hp0 (anchor p z) (by simpa only [Fintype.card_fin] using hF) hprime hN e
  have hbal : 5*(b : ℝ)^(56/100 : ℝ)-alpha*(b : ℝ)^(70/100 : ℝ) ≤
      -(alpha/2)*(b : ℝ)^(70/100 : ℝ) := by linarith
  refine ⟨he.trans (Real.exp_le_exp.mpr hbal),?_⟩
  have hr := (rounding hh (anchor p z) t e (anchor_mem_cube p hp z)
    (fun j => ⟨(gridCell_subset_cube p hp z t ht j).1,(gridCell_subset_cube p hp z t ht j).2.le⟩)
    (fun j => by rw [abs_of_nonneg (ht j).1]; exact (ht j).2.le)).2.2.2
  have hround : atom (height b) t e/p ≤ Real.exp ((b : ℝ)*height b^2/p)*
      (folded (height b) (anchor p z)/p*wordMass (height b) (anchor p z) e) := by
    have h := div_le_div_of_nonneg_right hr hp0.le
    simpa only [Fintype.card_fin,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  calc
    _ ≤ Real.exp ((b : ℝ)*height b^2/p)*
        Real.exp (5*(b : ℝ)^(56/100 : ℝ)-alpha*(b : ℝ)^(70/100 : ℝ)) :=
      hround.trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
    _ = Real.exp ((b : ℝ)*height b^2/p+5*(b : ℝ)^(56/100 : ℝ)-alpha*(b : ℝ)^(70/100 : ℝ)) := by
      rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Real Filter Topology
open scoped BigOperators

lemma eventually_logMean_height_le : ∀ᶠ b : ℕ in atTop, logMean (height b) ≤ (b : ℝ) := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  have he : ∀ᶠ b : ℝ in atTop, logMean (heightR b) ≤ b := by
    filter_upwards [eventually_height_bound (s := 1) (c := Real.sqrt (2*Real.pi)/2)
      (by norm_num) (by positivity), eventually_gt_atTop (1 : ℝ)] with b hb hb1
    have hh := heightR_pos hb1
    have ht : 0 < 2*heightR b/Real.sqrt (2*Real.pi) := by positivity
    calc
      _ ≤ Real.log (2*heightR b/Real.sqrt (2*Real.pi)) := logMean_upper hh
      _ ≤ 2*heightR b/Real.sqrt (2*Real.pi) :=
        (Real.log_le_sub_one_of_pos ht).trans (by linarith)
      _ ≤ b := by
        rw [div_le_iff₀ hs]
        rw [Real.rpow_one] at hb
        nlinarith
  exact tendsto_natCast_atTop_atTop.eventually he



lemma group_log_bound {a b p : ℕ} [NeZero p] (hb : 1 ≤ b)
    (ha : logMean (height a) ≤ (a : ℝ))
    (hab : (a : ℝ) ≤ (b : ℝ)^((1 : ℝ)/(9/10)))
    (hp : Real.log p ≤ (a : ℝ)*logMean (height a)-3*(a : ℝ)^(56/100 : ℝ)) :
    Real.log (Fintype.card (Fin a → ZMod p)) ≤ (b : ℝ)^4 := by
  have hp' : Real.log p ≤ (a : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
    have ht : 0 ≤ (a : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  calc
    _ = (a : ℝ)*Real.log p := by simp [Real.log_pow]
    _ ≤ (a : ℝ)^3 := by
      have h := mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      nlinarith
    _ ≤ ((b : ℝ)^((1 : ℝ)/(9/10)))^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hab _
    _ = (b : ℝ)^(10/3 : ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg b)]
      norm_num
    _ ≤ (b : ℝ)^4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ b by exact_mod_cast hb)
        (by norm_num : (10/3 : ℝ) ≤ (4 : ℝ))
      simpa using h


end SingleLatticeCovering.Folded





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical

variable {E V W : Type*} [Fintype E]

lemma mem_join (P : E → Finset V) (point : E → W) (x : V × W) :
    x ∈ join P point ↔ ∃ e, x.1 ∈ P e ∧ x.2 = point e := by
  classical
  simp only [join, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨e,v,hv,rfl⟩
    exact ⟨e,hv,rfl⟩
  · rintro ⟨e,hv,he⟩
    exact ⟨e,x.1,hv,Prod.ext rfl he.symm⟩

lemma sum_join (P : E → Finset V) (point : E → W) (hp : Function.Injective point)
    (f : V × W → ℝ) :
    ∑ x ∈ join P point, f x = ∑ e, ∑ x ∈ P e, f (x,point e) := by
  classical
  rw [join, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_image]
    exact fun x hx y hy h => congrArg Prod.fst h
  · intro e he e' he' hee'
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp hx
    obtain ⟨v',hw,hw'⟩ := Finset.mem_image.mp hx'
    exact hee' (hp (congrArg Prod.snd (hv'.trans hw'.symm)))




theorem weighted_join (P : E → Finset V) (point : E → W) (hp : Function.Injective point)
    (preWeight : E → V → ℝ) (block : E → ℝ) (weight : V × W → ℝ)
    (prob g : E → ℝ) (a c d s : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hprob : ∀ e, 0 ≤ prob e) (hg : ∀ e, 0 ≤ g e)
    (hb : ∀ e, c*d*prob e ≤ block e)
    (hpreWeight : ∀ e, a*g e ≤ ∑ x ∈ P e, preWeight e x)
    (hweight : ∀ e, ∀ x ∈ P e, weight (x,point e) = preWeight e x * block e)
    (hs : s ≤ ∑ e, prob e*g e) :
    a*c*d*s ≤ ∑ x ∈ join P point, weight x := by
  classical
  rw [sum_join P point hp]
  calc
    a*c*d*s ≤ a*c*d * ∑ e, prob e*g e :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg ha hc) hd)
    _ = ∑ e, (a*g e)*(c*d*prob e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ ∑ e, (∑ x ∈ P e, preWeight e x)*block e := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul (hpreWeight e) (hb e) (mul_nonneg (mul_nonneg hc hd) (hprob e))
        ((mul_nonneg ha (hg e)).trans (hpreWeight e))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x hx => (hweight e x hx).symm)

lemma bits_injective (b : ℕ) (lam : Fin b → ℝ) : Function.Injective (bits b lam) := by
  intro e e' h
  funext j
  have hj := congrFun h j
  dsimp only [bits] at hj
  cases he : e j <;> cases he' : e' j <;> simp_all

lemma bits_scalar (b : ℕ) (lam : Fin b → ℝ) (e : Fin b → Bool) (j : Fin b) :
    bits b lam e j=lam j ∨ bits b lam e j=lam j+1 := by
  cases he : e j <;> simp [bits,he]


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Chains
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete _root_.OAI.SingleLatticeCovering.Vertical.Block.lattice_discrete _root_.OAI.SingleLatticeCovering.Vertical.Block.lattice_full _root_.OAI.SingleLatticeCovering.Vertical.Chain.raw_discrete _root_.OAI.SingleLatticeCovering.Vertical.Chain.raw_full
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


lemma append_injective {m b : ℕ} :
    Function.Injective (fun x : (Fin m → ℝ) × (Fin b → ℝ) => Fin.append x.1 x.2) := by
  intro x y h
  apply Prod.ext
  · funext j
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd b j)
  · funext j
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd m j)

lemma mem_concat {m b : ℕ} (P : (Fin b → Bool) → Finset (Fin m → ℝ))
    (lam : Fin b → ℝ) (x : Fin (m+b) → ℝ) :
    x ∈ concat P lam ↔ ∃ e, ∃ v ∈ P e, x=Fin.append v (bits b lam e) := by
  classical
  rw [concat, Finset.mem_image]
  constructor
  · rintro ⟨⟨v,w⟩,hvw,rfl⟩
    obtain ⟨e,he,hwe⟩ := (mem_join P (bits b lam) (v,w)).mp hvw
    exact ⟨e,v,he,by rw [hwe]⟩
  · rintro ⟨e,v,hv,rfl⟩
    exact ⟨(v,bits b lam e),(mem_join _ _ _).mpr ⟨e,hv,rfl⟩,rfl⟩




theorem suffixBinary_concat {m b : ℕ}
    (P : (Fin b → Bool) → Finset (Fin m → ℝ)) (lam : Fin b → ℝ)
    (hP : ∀ e, SuffixBinary (P e)) : SuffixBinary (concat P lam) := by
  classical
  intro j y
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · by_cases hn : ∃ e : Fin b → Bool, bits b lam e = (fun k => y (Fin.natAdd m k))
    · obtain ⟨e,he⟩ := hn
      obtain ⟨a,ha⟩ := hP e j (fun k => y (Fin.castAdd b k))
      refine ⟨a,?_⟩
      intro x hx hxy
      obtain ⟨e',v,hv,rfl⟩ := (mem_concat P lam x).mp hx
      have he' : bits b lam e' = bits b lam e := by
        funext k
        rw [he]
        simpa only [Fin.append_right] using hxy (Fin.natAdd m k) (by
          change j.val < m+k.val
          omega)
      have heq : e'=e := bits_injective b lam he'
      subst e'
      simpa only [Fin.append_left] using ha v hv (fun k hk => by
        simpa only [Fin.append_left] using hxy (Fin.castAdd b k) (by
          exact hk))
    · refine ⟨0,?_⟩
      intro x hx hxy
      obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam x).mp hx
      apply False.elim
      apply hn
      refine ⟨e,?_⟩
      funext k
      simpa only [Fin.append_right] using hxy (Fin.natAdd m k) (by
        change j.val < m+k.val
        omega)
  · refine ⟨lam j,?_⟩
    intro x hx hxy
    obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam x).mp hx
    simpa only [Fin.append_right] using bits_scalar b lam e j


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators


namespace Block

lemma g_nonneg (B : Block) (x : B.Group) : 0 ≤ B.g x :=
  lineMax_nonneg (K := ZMod B.p) (fun z => by
    unfold sparseWeight
    split_ifs
    · exact div_nonneg (folded_pos B.h_pos _).le (Nat.cast_nonneg _)
    · exact le_refl 0) _ _

lemma weight_pos (B : Block) (y l : B.Vec) : 0 < B.weight y l := by
  unfold weight gamma
  exact mul_pos (div_pos (pow_pos B.h_pos _) (by exact_mod_cast B.prime.pos))
    (Finset.prod_pos (fun j _ => gamma1_pos _))

lemma weight_bits (B : Block) (y lam : B.Vec) (e : Fin B.b → Bool) :
    B.weight y (bits B.b lam e) =
      atom B.h ((fun j => y j/B.h)-lam) e/(B.p : ℝ) := by
  have he : (fun j => y j-B.h*bits B.b lam e j) =
      (fun j => B.h*(((fun j => y j/B.h)-lam) j-bitValue (e j))) := by
    funext j
    simp only [bits, bitValue, Pi.sub_apply]
    field_simp [B.h_pos.ne']
    ring
  simp only [weight, atom, Fintype.card_fin, he]
  ring


lemma shift_grid_bits (A B : Block) (w : Fin B.b → A.Group) (y : A.Vec)
    (lam : B.Vec) (e : Fin B.b → Bool) :
    A.grid (y-A.shift B w (bits B.b lam e)) =
      A.grid (y-A.shift B w lam)-Bits.groupShift w e := by
  ext j
  have hp : (A.p : ℝ) ≠ 0 := by exact_mod_cast A.prime.pos.ne'
  have hh : A.h ≠ 0 := A.h_pos.ne'
  have hs :
      (A.p : ℝ)*((y-A.shift B w (bits B.b lam e)) j/A.h) =
      (A.p : ℝ)*((y-A.shift B w lam) j/A.h)-
        (((∑ k, if e k then ((w k j).val : ℤ) else 0) : ℤ) : ℝ) := by
    simp only [Pi.sub_apply, shift, bits]
    rw [Int.cast_sum]
    simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero]
    have hs' : (∑ k, ((w k j).val : ℝ)*(lam k+if e k then 1 else 0)) =
        (∑ k, ((w k j).val : ℝ)*lam k) + (∑ k, if e k then ((w k j).val : ℝ) else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      cases he : e k <;> simp [mul_add]
    rw [hs']
    field_simp
    ring
  simp only [Pi.sub_apply] at hs
  simp only [grid, residue, floorVector, Pi.sub_apply]
  rw [hs, Int.floor_sub_intCast, Int.cast_sub, Int.cast_sum]
  congr 1
  simp only [Bits.groupShift, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases he : e k <;> simp



end Block
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators



namespace Chain
variable {A B : Block}

lemma coefficient_nonneg (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss) :
    0 ≤ c.coefficient loss := by
  induction c with
  | base B => exact (Real.exp_pos _).le
  | append c B w ih =>
    exact mul_nonneg (mul_nonneg (mul_nonneg (ih hc.1) (Real.exp_pos _).le) hc.2.1) hc.2.2.1

lemma weight_pos (c : Chain B) (y l : c.Vec) : 0 < c.weight y l := by
  induction c with
  | base B => exact B.weight_pos y l
  | append c B w ih => exact mul_pos (ih _ _) (B.weight_pos _ _)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded Blocks ConstructionA Filter Topology
open scoped BigOperators

lemma regular_mean {A : ℝ} {B : Block} (hB : Regular A B) (hsmall : blockLoss A B ≤ 1/2) :
    1/2 ≤ (𝔼 x, B.g x) ∧ (𝔼 x, B.g x) ≤ 2 := by
  have h := abs_le.mp hB.2.2.2.2.1
  constructor <;> linarith




theorem block_preparation : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 2 ≤ N ∧
    (∀ b ≥ N, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 ∧ logMean (height b) ≤ (b : ℝ)) ∧
    (∀ b ≥ N, ∃ B : Block, B.b=b ∧ Regular A B) ∧
    (∀ (P : Block), N ≤ P.b → Regular A P → ∀ b ≥ N,
      (P.b : ℝ) ≤ (b : ℝ)^((1 : ℝ)/(9/10)) →
      ∃ B : Block, ∃ w : Fin B.b → P.Group,
        B.b=b ∧ Regular A B ∧
        ∀ z ∈ B.usable, ∀ x : P.Group,
          (1-blockLoss A B)*(𝔼 y, P.g y) ≤
            ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * P.g (x-Bits.groupShift w e)) := by
  classical
  obtain ⟨A,hA,hsel⟩ := eventually_usable_gaussian.{0}
  have hsmall : ∀ᶠ b : ℕ in atTop, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul A
    have hn : Tendsto (fun b : ℕ => A*(b : ℝ)^(-(1/100 : ℝ))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,mul_zero] using ht.comp hcast
    exact hn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hsel.and (eventually_height_prime.and (hsmall.and (eventually_logMean_height_le.and (eventually_ge_atTop (2 : ℕ))))))
  let N' := max N 2
  have hN' : 2 ≤ N' := le_max_right _ _
  have hbN (b : ℕ) (hb : N' ≤ b) := hN b ((le_max_left _ _).trans hb)
  refine ⟨A,hA,N',hN',?_,?_,?_⟩
  · intro b hb
    exact ⟨(hbN b hb).2.2.1,(hbN b hb).2.2.2.1⟩
  · intro b hb
    obtain ⟨p,hp,hpl,hpu⟩ := (hbN b hb).2.1
    let : Fact p.Prime := ⟨hp⟩
    have hb1 : 1 ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
    obtain ⟨w,U,v,hU,hs,hM,hg,hcap⟩ := (hbN b hb).1 p hpl hpu PUnit (by simp) 1 (by norm_num)
      (Real.one_le_rpow hb1 (by norm_num)) (fun _ => 1) (by simp)
      (fun x => by simp)
      (by norm_num) (by norm_num)
    let B : Block := ⟨b,p,hp,height b,heightR_pos (by exact_mod_cast (show 1 < b by omega)),U,v,v.property⟩
    refine ⟨B,rfl,rfl,hpl,hpu,hU,?_,?_⟩
    · exact hg
    · exact fun x => (hcap x).2
  · intro P hP hPreg b hb hrel
    obtain ⟨p,hp,hpl,hpu⟩ := (hbN b hb).2.1
    let : Fact p.Prime := ⟨hp⟩
    have hb1 : 1 ≤ b := by omega
    have hP1 : 1 ≤ (P.b : ℝ) := by exact_mod_cast (show 1 ≤ P.b by omega)
    have hg := regular_mean hPreg (hbN P.b hP).2.2.1
    have hcard := group_log_bound hb1 (hbN P.b hP).2.2.2.1 hrel hPreg.2.2.1
    obtain ⟨w,U,v,hU,hs,hM,hmean,hcap⟩ := (hbN b hb).1 p hpl hpu P.Group hcard
      (P.b : ℝ) hP1 hrel P.g P.g_nonneg hPreg.2.2.2.2.2 hg.1 hg.2
    let B : Block := ⟨b,p,hp,height b,heightR_pos (by exact_mod_cast (show 1 < b by omega)),U,v,v.property⟩
    refine ⟨B,w,rfl,⟨rfl,hpl,hpu,hU,hmean,fun x => (hcap x).2⟩,?_⟩
    exact hs


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators
namespace Block

lemma roundingLoss_nonneg (B : Block) : 0 ≤ B.roundingLoss := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
end Block

namespace Chain
variable {A B : Block}

lemma every_last {P : Block → Prop} (c : Chain B) (hc : c.Every P) : P B := by
  cases c with
  | base B => exact hc
  | append c B w => exact hc.2
lemma every_mono {P Q : Block → Prop} (c : Chain B) (hc : c.Every P)
    (h : ∀ B, P B → Q B) : c.Every Q := by
  induction c with
  | base B => exact h B hc
  | append c B w ih => exact ⟨ih hc.1,h B hc.2⟩

lemma blockSum_le (c : Chain B) (f g : Block → ℝ) (h : c.Every (fun B => f B ≤ g B)) :
    c.blockSum f ≤ c.blockSum g := by
  induction c with
  | base B => exact h
  | append c B w ih => exact add_le_add (ih h.1) h.2
lemma blockSum_mul (c : Chain B) (a : ℝ) (f : Block → ℝ) :
    c.blockSum (fun B => a*f B) = a*c.blockSum f := by
  induction c with
  | base B => rfl
  | append c B w ih => simp only [blockSum,ih,mul_add]


theorem inverse_power_sum (c : Chain B) (a : ℝ) (ha : 0 < a)
    (hc : c.Halving) (hpos : c.Every (fun B => 0 < B.b)) :
    c.blockSum (fun B => (B.b : ℝ)^(-a)) ≤ (B.b : ℝ)^(-a)/(1-(2 : ℝ)^(-a)) := by
  have hq0 : 0 ≤ (2 : ℝ)^(-a) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (2 : ℝ)^(-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)
  have hd : 0 < 1-(2 : ℝ)^(-a) := sub_pos.mpr hq1
  induction c with
  | base B =>
    change (B.b : ℝ)^(-a) ≤ (B.b : ℝ)^(-a)/(1-(2 : ℝ)^(-a))
    apply (le_div_iff₀ hd).mpr
    have hu := Real.rpow_nonneg (Nat.cast_nonneg B.b) (-a)
    nlinarith
  | @append A c B w ih =>
    have hi := ih hc.1 hpos.1
    have hp : (0 : ℝ) < B.b := by exact_mod_cast hpos.2
    have hh : (2 : ℝ)*B.b ≤ A.b := by exact_mod_cast hc.2
    have he : (A.b : ℝ)^(-a) ≤ (2 : ℝ)^(-a)*(B.b : ℝ)^(-a) := by
      have ht := Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hp) hh (neg_nonpos.mpr ha.le)
      rwa [Real.mul_rpow (by norm_num) hp.le] at ht
    change c.blockSum (fun B => (B.b : ℝ)^(-a))+(B.b : ℝ)^(-a) ≤ _
    have hi' := (le_div_iff₀ hd).mp hi
    apply (le_div_iff₀ hd).mpr
    nlinarith

lemma mul_deficit {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) :
    1-x*y ≤ (1-x)+(1-y) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]



theorem coefficient_bounds (c : Chain B) (loss : Block → ℝ)
    (hl : c.Every (fun B => loss B ∈ Set.Icc 0 1)) :
    0 ≤ c.coefficient loss ∧ c.coefficient loss ≤ 1 ∧
      1-c.coefficient loss+loss B ≤ c.blockSum (fun B => B.roundingLoss+2*loss B) := by
  have he (B : Block) : 0 ≤ Real.exp (-B.roundingLoss) ∧
      Real.exp (-B.roundingLoss) ≤ 1 ∧ 1-Real.exp (-B.roundingLoss) ≤ B.roundingLoss := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr B.roundingLoss_nonneg),?_⟩
    have h := Real.add_one_le_exp (-B.roundingLoss)
    linarith
  induction c with
  | base B =>
    change 0 ≤ Real.exp (-B.roundingLoss) ∧ Real.exp (-B.roundingLoss) ≤ 1 ∧ _
    refine ⟨(he B).1,(he B).2.1,?_⟩
    change 1-Real.exp (-B.roundingLoss)+loss B ≤ B.roundingLoss+2*loss B
    linarith [(he B).2.2,hl.1]
  | @append A c B w ih =>
    obtain ⟨hc0,hc1,hcd⟩ := ih hl.1
    have hA := c.every_last hl.1
    have hB := hl.2
    have hx0 : 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss) := mul_nonneg hc0 (he B).1
    have hx1 : c.coefficient loss*Real.exp (-B.roundingLoss) ≤ 1 :=
      (mul_le_mul hc1 (he B).2.1 (he B).1 (by norm_num)).trans_eq (by ring)
    have hy0 : 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B) :=
      mul_nonneg hx0 (sub_nonneg.mpr hB.2)
    have hy1 : c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B) ≤ 1 :=
      (mul_le_mul hx1 (by linarith [hB.1] : 1-loss B ≤ 1) (sub_nonneg.mpr hB.2) (by norm_num)).trans_eq (by ring)
    change 0 ≤ c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B)*(1-loss A) ∧ _
    refine ⟨mul_nonneg hy0 (sub_nonneg.mpr hA.2),?_,?_⟩
    · exact (mul_le_mul hy1 (by linarith [hA.1] : 1-loss A ≤ 1) (sub_nonneg.mpr hA.2) (by norm_num)).trans_eq (by ring)
    · have hd1 := mul_deficit hc1 (he B).2.1
      have hd2 := mul_deficit hx1 (show 1-loss B ≤ 1 by linarith [hB.1])
      have hd3 := mul_deficit hy1 (show 1-loss A ≤ 1 by linarith [hA.1])
      change 1-c.coefficient loss*Real.exp (-B.roundingLoss)*(1-loss B)*(1-loss A)+loss B ≤
        c.blockSum (fun B => B.roundingLoss+2*loss B)+(B.roundingLoss+2*loss B)
      linarith [(he B).2.2]



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks Filter Topology
open scoped BigOperators


lemma nextSize_relation (b : ℕ) : (b : ℝ) ≤ (nextSize b : ℝ)^((1 : ℝ)/(9/10)) := by
  have hn : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have he := Real.rpow_le_rpow (Real.rpow_nonneg hn _) (Nat.le_ceil ((b : ℝ)^(9/10 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1/(9/10))
  rw [←Real.rpow_mul hn] at he
  norm_num at he
  simpa [nextSize] using he

lemma eventually_nextSize_half : ∀ᶠ b : ℕ in atTop, 2*nextSize b ≤ b := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_rpow_ratio_bound (by norm_num : (9/10 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/4)), eventually_ge_atTop (4 : ℕ)] with b hb hb4
  have hb4' : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hc : (nextSize b : ℝ) < (b : ℝ)^(9/10 : ℝ)+1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg b) (9/10 : ℝ))
  have hp : (b : ℝ)^(9/10 : ℝ) ≤ (b : ℝ)/4 := by
    simpa only [Real.rpow_one,div_eq_mul_inv,mul_comm,one_mul] using hb
  have hn : (2 : ℝ)*(nextSize b : ℝ) ≤ b := by
    linarith only [hc,hp,hb4']
  exact_mod_cast hn



theorem hierarchy_preparation : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 2 ≤ N ∧
    (∀ b ≥ N, A*(b : ℝ)^(-(1/100 : ℝ)) ≤ 1/2 ∧ logMean (height b) ≤ (b : ℝ)) ∧
    ∀ cutoff ≥ N, ∀ b₁ ≥ cutoff,
      ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.Every (fun B => cutoff ≤ B.b ∧ Regular A B) ∧
        c.Good (blockLoss A) ∧ c.Halving ∧ c.CeilingSizes ∧ nextSize B.b < cutoff := by
  classical
  obtain ⟨A,hA,N,hN,hsmall,hfirst,hnext⟩ := block_preparation
  obtain ⟨M,hM⟩ := eventually_atTop.mp eventually_nextSize_half
  let N' := max N M
  have hNN : N ≤ N' := le_max_left _ _
  have hMN : M ≤ N' := le_max_right _ _
  refine ⟨A,hA,N',hN.trans hNN,fun b hb => hsmall b (hNN.trans hb),?_⟩
  intro cutoff hcut b₁ hb₁
  have hcutN : N ≤ cutoff := hNN.trans hcut
  have hext : ∀ b : ℕ, ∀ P : Block, P.b=b → ∀ c : Chain P,
      c.Every (fun B => cutoff ≤ B.b ∧ Regular A B) →
      c.Good (blockLoss A) → c.Halving → c.CeilingSizes →
      ∃ B : Block, ∃ d : Chain B,
        d.first=c.first ∧ d.Every (fun B => cutoff ≤ B.b ∧ Regular A B) ∧
        d.Good (blockLoss A) ∧ d.Halving ∧ d.CeilingSizes ∧ nextSize B.b < cutoff := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro P hPb c hc hg hh hs
      have hP := c.every_last hc
      by_cases hstop : nextSize P.b < cutoff
      · exact ⟨P,c,rfl,hc,hg,hh,hs,hstop⟩
      · have hgo : cutoff ≤ nextSize P.b := le_of_not_gt hstop
        have hhalf : 2*nextSize P.b ≤ P.b := hM P.b (hMN.trans (hcut.trans hP.1))
        have hlt : nextSize P.b < b := by
          have hP2 : 2 ≤ P.b := hN.trans (hcutN.trans hP.1)
          omega
        obtain ⟨Q,w,hQb,hQ,hws⟩ := hnext P (hcutN.trans hP.1) hP.2
          (nextSize P.b) (hcutN.trans hgo) (nextSize_relation P.b)
        have hQcut : cutoff ≤ Q.b := hQb ▸ hgo
        have hc' : (Chain.append c Q w).Every (fun B => cutoff ≤ B.b ∧ Regular A B) :=
          ⟨hc,hQcut,hQ⟩
        have hsmP : blockLoss A P ≤ 1/2 := (hsmall P.b (hcutN.trans hP.1)).1
        have hsmQ : blockLoss A Q ≤ 1/2 := (hsmall Q.b (hcutN.trans hQcut)).1
        have hmean : 1-blockLoss A P ≤ (𝔼 x, P.g x) := by
          have ht := (abs_le.mp hP.2.2.2.2.2.1).1
          linarith
        have hg' : (Chain.append c Q w).Good (blockLoss A) :=
          ⟨hg,by linarith,by linarith,hmean,hws⟩
        have hh' : (Chain.append c Q w).Halving := ⟨hh,by rwa [hQb]⟩
        have hs' : (Chain.append c Q w).CeilingSizes := ⟨hs,hQb⟩
        obtain ⟨R,d,hdf,hdc,hdg,hdh,hds,hdt⟩ := ih (nextSize P.b) hlt Q hQb
          (Chain.append c Q w) hc' hg' hh' hs'
        exact ⟨R,d,hdf,hdc,hdg,hdh,hds,hdt⟩
  obtain ⟨P,hPb,hP⟩ := hfirst b₁ (hcutN.trans hb₁)
  have hPc : cutoff ≤ P.b := hPb ▸ hb₁
  obtain ⟨B,c,hcf,hc,hg,hh,hs,ht⟩ := hext P.b P rfl (Chain.base P)
    ⟨hPc,hP⟩ trivial trivial trivial
  refine ⟨B,c,?_,hc,hg,hh,hs,ht⟩
  rw [hcf]
  exact hPb


end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma mem_image {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    x ∈ image L e ↔ ∃ l ∈ L, e l=x := by
  change e.symm x ∈ L ↔ _
  constructor
  · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  · rintro ⟨l,hl,rfl⟩; simpa using hl

lemma image_covolume (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (image L e) = |LinearMap.det e.toLinearMap| * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let b' : Basis ι ℤ (image L e) := b.ofZLatticeComap ℝ L e.symm
  rw [ZLattice.covolume_eq_det _ b',ZLattice.covolume_eq_det _ b,
    ←Pi.basisFun_det_apply, ←Pi.basisFun_det_apply]
  have he : Subtype.val ∘ b' = e.toLinearMap ∘ (Subtype.val ∘ b) := by
    ext j k
    simp [b', Basis.ofZLatticeComap_apply]
  rw [he, Basis.det_comp, abs_mul]


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Chain
variable {A B : Block}

lemma subLast_eq_sub (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.subLast y t = y-c.injectLast t := by
  cases c with
  | base B => rfl
  | append c B w =>
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [subLast,injectLast,appendEquiv]

lemma mem_raw (c : Chain B) (l : c.Vec) : l ∈ c.rawLattice ↔ c.RawMem l := by
  induction c with
  | base B => rfl
  | append c B w ih => exact and_congr (ih _) Iff.rfl

lemma residual_append (c : Chain A) (B : Block) (w : Fin B.b → A.Group)
    (y l : (Chain.append c B w).Vec) :
    y-(Chain.append c B w).linear l =
      Fin.append
        (c.subLast (fun j => y (Fin.castAdd B.b j))
          (A.shift B w (fun j => l (Fin.natAdd c.dim j))) -
          c.linear (fun j => l (Fin.castAdd B.b j)))
        (fun j => y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [linear,triangular,sub_eq_add_neg,add_comm,add_assoc]

lemma gamma_append {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    gamma (Fin.append x y) = gamma x*gamma y := by
  simp only [gamma,Fin.prod_univ_add,Fin.append_left,Fin.append_right]



lemma weight_eq (c : Chain B) (y l : c.Vec) :
    c.weight y l = c.det*gamma (y-c.linear l) := by
  induction c with
  | base B => rfl
  | @append A c B w ih =>
    rw [weight, ih, residual_append, gamma_append]
    simp only [Block.weight,det,Block.det]
    ring



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


lemma binaryExpansion (k n : ℕ) (hn : n < 2^k) :
    ∃ e : Fin k → Bool, (∑ j, if e j then 2^(j : ℕ) else 0) = n := by
  induction k generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    exact ⟨Fin.elim0,by simp [hn0]⟩
  | succ k ih =>
    by_cases hh : n < 2^k
    · obtain ⟨e,he⟩ := ih n hh
      refine ⟨Fin.snoc e false,?_⟩
      rw [Fin.sum_univ_castSucc]
      simpa using he
    · have hn' : n-2^k < 2^k := by rw [pow_succ] at hn; omega
      obtain ⟨e,he⟩ := ih (n-2^k) hn'
      refine ⟨Fin.snoc e true,?_⟩
      rw [Fin.sum_univ_castSucc]
      simp [he,Nat.sub_add_cancel (by omega : 2^k ≤ n)]


theorem terminal_exhaustion (b p : ℕ) [NeZero p] :
    Function.Surjective (fun e : Fin (b*Nat.clog 2 p) → Bool =>
      ∑ i, if e i then terminalColumns b p i else 0) := by
  classical
  intro z
  have hb (j : Fin b) : (z j).val < 2^(Nat.clog 2 p) :=
    (ZMod.val_lt (z j)).trans_le (Nat.le_pow_clog (by norm_num) p)
  choose e he using fun j => binaryExpansion (Nat.clog 2 p) (z j).val (hb j)
  refine ⟨fun i => e (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2,?_⟩
  ext j
  change (∑ i, if e (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 then terminalColumns b p i else 0) j = z j
  simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
  rw [←Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply,terminalColumns,     Fintype.sum_prod_type]
  have hdiag : (∑ a : Fin b, ∑ k : Fin (Nat.clog 2 p),
      (if e a k then Pi.single a ((2 : ZMod p)^(k : ℕ)) j else 0)) =
      ∑ k : Fin (Nat.clog 2 p), if e j k then (2 : ZMod p)^(k : ℕ) else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ haj
      apply Finset.sum_eq_zero
      intro k _
      simp [Pi.single_eq_of_ne (Ne.symm haj)]
    · simp
  rw [hdiag]
  have he' := congrArg (fun n : ℕ => (n : ZMod p)) (he j)
  simpa using he'


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma integerLattice_covolume (n : ℕ) : ZLattice.covolume (integerLattice n) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume),
    ZSpan.volume_real_fundamentalDomain]
  have hm : Matrix.of (Pi.basisFun ℝ (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hm,Matrix.det_one,abs_one]
lemma integer_mem (n : ℕ) (k : Fin n → ℤ) : (fun j => (k j : ℝ)) ∈ integerLattice n := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨k j,by simp⟩

namespace Block

lemma shiftDim_grid_bits (B : Block) (d : ℕ) (w : Fin d → B.Group) (y : B.Vec)
    (lam : Fin d → ℝ) (e : Fin d → Bool) :
    B.grid (y-B.shiftDim d w (bits d lam e)) =
      B.grid (y-B.shiftDim d w lam)-Bits.groupShift w e := by
  ext j
  have hp : (B.p : ℝ) ≠ 0 := by exact_mod_cast B.prime.pos.ne'
  have hh : B.h ≠ 0 := B.h_pos.ne'
  have hs : (B.p : ℝ)*((y-B.shiftDim d w (bits d lam e)) j/B.h) =
      (B.p : ℝ)*((y-B.shiftDim d w lam) j/B.h)-
        (((∑ k, if e k then ((w k j).val : ℤ) else 0) : ℤ) : ℝ) := by
    simp only [Pi.sub_apply, shiftDim, bits]
    rw [Int.cast_sum]
    simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero]
    have hs' : (∑ k, ((w k j).val : ℝ)*(lam k+if e k then 1 else 0)) =
        (∑ k, ((w k j).val : ℝ)*lam k) + (∑ k, if e k then ((w k j).val : ℝ) else 0) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      cases he : e k <;> simp [mul_add]
    rw [hs']
    field_simp
    ring
  simp only [Pi.sub_apply] at hs
  simp only [grid,residue,floorVector,Pi.sub_apply]
  rw [hs,Int.floor_sub_intCast,Int.cast_sub,Int.cast_sum]
  congr 1
  simp only [Bits.groupShift,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases he : e k <;> simp



lemma terminal_index (B : Block) (y : B.Vec) (t : Fin B.terminalDim → ℝ) (z : B.Group) :
    ∃ l ∈ integerLattice B.terminalDim,
      (∀ j, |t j-l j| ≤ 1) ∧ B.grid (y-B.terminalShift l)=z := by
  classical
  let lam : Fin B.terminalDim → ℝ := fun j => (⌊t j⌋ : ℤ)
  obtain ⟨e,he⟩ := terminal_exhaustion B.b B.p
    (B.grid (y-B.terminalShift lam)-z)
  refine ⟨bits B.terminalDim lam e,?_,?_,?_⟩
  · convert integer_mem B.terminalDim (fun j => ⌊t j⌋+if e j then 1 else 0) using 1
    ext j
    cases he : e j <;> simp [bits,lam,he]
  · intro j
    have hfl := Int.floor_le (t j)
    have hfu := Int.lt_floor_add_one (t j)
    rw [abs_le]
    cases he : e j <;>
      simp only [bits,lam,he,Bool.false_eq_true,↓reduceIte,add_zero] <;> constructor <;> linarith
  · simp only [terminalShift,shiftDimMap_apply]
    rw [shiftDim_grid_bits]
    have he' : Bits.groupShift (terminalColumns B.b B.p) e =
        B.grid (y-B.shiftDim B.terminalDim (terminalColumns B.b B.p) lam)-z := by
      simpa only [Bits.groupShift,terminalShift,shiftDimMap_apply] using he
    rw [he']
    abel
end Block

namespace Chain
variable {B : Block}

lemma full_residual (c : Chain B) (y : c.FullVec) (v : c.Vec) (t : Fin B.terminalDim → ℝ) :
    y-c.fullLinear (Fin.append v t) = Fin.append
      (c.subLast (fun j => y (Fin.castAdd B.terminalDim j)) (B.terminalShift t)-c.linear v)
      (fun j => y (Fin.natAdd c.dim j)-t j) := by
  rw [subLast_eq_sub]
  ext j
  refine Fin.addCases ?_ ?_ j <;> intro k <;>
    simp [fullLinear,triangular_append,sub_eq_add_neg,add_comm,add_assoc]

lemma full_weight (c : Chain B) (y : c.FullVec) (v : c.Vec) (t : Fin B.terminalDim → ℝ) :
    c.det*gamma (y-c.fullLinear (Fin.append v t)) =
      c.weight (c.subLast (fun j => y (Fin.castAdd B.terminalDim j)) (B.terminalShift t)) v *
        gamma (fun j => y (Fin.natAdd c.dim j)-t j) := by
  rw [full_residual,gamma_append,weight_eq]
  ring



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators

namespace Block

lemma cell_selected (B : Block) (y : B.Vec) (hg : 0 < B.g (B.grid y)) :
    ∃ z ∈ B.usable, ∃ lam : B.Vec,
      lam ∈ B.lattice ∧
      B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) ∧
      (∀ e : Fin B.b → Bool, bits B.b lam e ∈ B.lattice ∧
        (∀ j, |y j-B.h*bits B.b lam e j| ≤ B.h) ∧
        (Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
          (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) ≤ B.weight y (bits B.b lam e)) ∧
        B.Selected y (bits B.b lam e)) := by
  obtain ⟨z,hz,lam,hlam,ht,hg',he⟩ := gaussian_cell B.h_pos B.usable B.direction
    (fun j => y j/B.h) hg
  change B.g (B.grid y) = folded B.h (anchor B.p z)/(B.p : ℝ) at hg'
  refine ⟨z,hz,lam,hlam,hg',?_⟩
  intro e
  obtain ⟨hm,hr,hw⟩ := he e
  refine ⟨hm,?_,?_,⟨z,hz,lam,ht,e,rfl⟩⟩
  · intro j
    convert hr j using 1
    congr 1
    dsimp only [bits]
    simp only [bitValue]
    field_simp [B.h_pos.ne']
    ring
  · rw [weight_bits, hg']
    simpa only [Fintype.card_fin] using hw

lemma selected_weight_le (B : Block) (y l : B.Vec) (hl : B.Selected y l)
    (q : ℝ) (hq : ∀ z ∈ B.usable, ∀ t : B.Vec, t ∈ gridCell B.p z →
      ∀ e : Fin B.b → Bool, atom B.h t e/(B.p : ℝ) ≤ q) : B.weight y l ≤ q := by
  obtain ⟨z,hz,lam,ht,e,rfl⟩ := hl
  rw [weight_bits]
  exact hq z hz _ ht e
end Block

namespace Chain
variable {A B : Block}

lemma base_pattern_selected (B : Block) (y : B.Vec) :
    ∃ P : Finset B.Vec, SuffixBinary P ∧
      (∀ l ∈ P, l ∈ B.lattice ∧ (∀ j, |y j-B.h*l j| ≤ B.h) ∧ B.Selected y l) ∧
      Real.exp (-((B.b : ℝ)*B.h^2/B.p))*B.g (B.grid y) ≤ ∑ l ∈ P, B.weight y l := by
  classical
  by_cases hg : 0 < B.g (B.grid y)
  · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell_selected y hg
    let P : Finset B.Vec := Finset.univ.image (bits B.b lam)
    refine ⟨P,?_,?_,?_⟩
    · intro j t
      refine ⟨lam j,?_⟩
      intro l hl hlt
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact bits_scalar B.b lam e j
    · intro l hl
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(he e).1,(he e).2.1,(he e).2.2.2⟩
    · change _ ≤ ∑ l ∈ Finset.univ.image (bits B.b lam), _
      rw [Finset.sum_image (fun e he e' he' h => bits_injective B.b lam h)]
      calc
        _ = ∑ e, Real.exp (-((B.b : ℝ)*B.h^2/B.p)) *
            (B.g (B.grid y)*wordMass B.h (anchor B.p z) e) := by
          rw [←Finset.mul_sum, ←Finset.mul_sum, wordMass_sum B.h_pos, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun e _ => (he e).2.2.1)
  · have heq : B.g (B.grid y)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
    refine ⟨∅,?_,by simp,?_⟩
    · intro j t
      exact ⟨0,by simp⟩
    · simp [heq]




theorem truncated_patterns_selected (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss)
    (y : c.Vec) :
    ∃ P : Finset c.Vec, SuffixBinary P ∧
      (∀ l ∈ P, c.RawMem l ∧ c.Residual y l ∧ c.Selected y l) ∧
      c.coefficient loss*B.g (B.grid (c.last y)) ≤ ∑ l ∈ P, c.weight y l := by
  classical
  induction c with
  | base B => exact base_pattern_selected B y
  | @append A c B w ih =>
    let yl : c.Vec := fun j => y (Fin.castAdd B.b j)
    let yr : B.Vec := fun j => y (Fin.natAdd c.dim j)
    by_cases hg : 0 < B.g (B.grid yr)
    · obtain ⟨z,hz,lam,hlam,hmax,he⟩ := B.cell_selected yr hg
      have hcp := fun e : Fin B.b → Bool => ih hc.1 (c.subLast yl (A.shift B w (bits B.b lam e)))
      choose P hPb hPm hPw using hcp
      refine ⟨concat P lam,suffixBinary_concat P lam hPb,?_,?_⟩
      · intro l hl
        obtain ⟨e,v,hv,rfl⟩ := (mem_concat P lam l).mp hl
        have hv' := hPm e v hv
        exact ⟨by simpa [RawMem] using And.intro hv'.1 (he e).1,
          by simpa [Residual] using And.intro hv'.2.1 (he e).2.1,
          by simpa [Selected] using And.intro hv'.2.2 (he e).2.2.2⟩
      · let x := A.grid (c.last yl-A.shift B w lam)
        have hgrid (e : Fin B.b → Bool) :
            A.grid (c.last (c.subLast yl (A.shift B w (bits B.b lam e)))) =
              x-Bits.groupShift w e := by
          rw [last_subLast, Block.shift_grid_bits]
        have hs : (1-loss B)*(1-loss A) ≤
            ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e) :=
          (mul_le_mul_of_nonneg_left hc.2.2.2.1 hc.2.1).trans (hc.2.2.2.2 z hz x)
        have hw := weighted_join P (bits B.b lam) (bits_injective B.b lam)
          (fun e l => c.weight (c.subLast yl (A.shift B w (bits B.b lam e))) l)
          (fun e => B.weight yr (bits B.b lam e))
          (fun l => (Chain.append c B w).weight y (Fin.append l.1 l.2))
          (wordMass B.h (anchor B.p z)) (fun e => A.g (x-Bits.groupShift w e))
          (c.coefficient loss) (B.g (B.grid yr)) (Real.exp (-((B.b : ℝ)*B.h^2/B.p)))
          ((1-loss B)*(1-loss A)) (coefficient_nonneg c loss hc.1) (B.g_nonneg _)
          (Real.exp_pos _).le
          (fun e => Finset.prod_nonneg (fun j _ => (probability_pos B.h_pos _ _).le))
          (fun e => A.g_nonneg _)
          (fun e => by convert (he e).2.2.1 using 1 ; ring)
          (fun e => by rw [←hgrid e]; exact hPw e)
          (fun e l hl => by simp [weight,yl,yr]) hs
        change _ ≤ ∑ l ∈ (join P (bits B.b lam)).image (fun x => Fin.append x.1 x.2), _
        rw [Finset.sum_image (fun x hx y hy h => append_injective h)]
        convert hw using 1 ; dsimp [coefficient, last,yr] ; ring
    · have heq : B.g (B.grid yr)=0 := le_antisymm (le_of_not_gt hg) (B.g_nonneg _)
      refine ⟨∅,?_,by simp,?_⟩
      · intro j t
        exact ⟨0,by simp⟩
      · change _*B.g (B.grid yr) ≤ _
        simp [heq]


end Chain
end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Residuals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma suffixBinary_fixed {m n : ℕ} (P : Finset (Fin m → ℝ)) (t : Fin n → ℝ)
    (hP : SuffixBinary P) : SuffixBinary (P.image (fun v => Fin.append v t)) := by
  classical
  intro j y
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · obtain ⟨a,ha⟩ := hP j (fun k => y (Fin.castAdd n k))
    refine ⟨a,?_⟩
    intro l hl hly
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simpa only [Fin.append_left] using ha v hv (fun k hk => by
      simpa only [Fin.append_left] using hly (Fin.castAdd n k) hk)
  · refine ⟨t j,?_⟩
    intro l hl hly
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simp only [Fin.append_right,true_or]

lemma gamma_unit_box {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    gamma1 1^n ≤ gamma x := by
  have hl (j : Fin n) : gamma1 1 ≤ gamma1 (x j) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hj := (sq_le_one_iff_abs_le_one (x j)).mpr (hx j)
    norm_num
    nlinarith
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun _ _ => (gamma1_pos 1).le) (fun j _ => hl j)
  simpa only [gamma,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hprod

namespace Chain
variable {B : Block}




theorem full_patterns (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss)
    (hmean : (1 : ℝ)/2 ≤ (𝔼 z, B.g z)) (y : c.FullVec) :
    ∃ P : Finset c.FullVec, SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.FullSelected y l) ∧
      (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
      c.coefficient loss*(1/2)*gamma1 1^B.terminalDim ≤
        ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  classical
  obtain ⟨z,hz,hgz⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let yl : c.Vec := fun j => y (Fin.castAdd B.terminalDim j)
  let yr : Fin B.terminalDim → ℝ := fun j => y (Fin.natAdd c.dim j)
  obtain ⟨t,ht,htr,htg⟩ := B.terminal_index (c.last yl) yr z
  let y' := c.subLast yl (B.terminalShift t)
  obtain ⟨P,hPb,hPm,hPw⟩ := c.truncated_patterns_selected loss hc y'
  have hg' : B.g (B.grid (c.last y'))=B.g z := by
    rw [last_subLast,htg]
  have hPw' : c.coefficient loss*(1/2) ≤ ∑ l ∈ P, c.weight y' l := by
    rw [hg'] at hPw
    exact (mul_le_mul_of_nonneg_left hgz (c.coefficient_nonneg loss hc)).trans hPw
  refine ⟨P.image (fun v => Fin.append v t),suffixBinary_fixed P t hPb,?_,⟨t,?_⟩,?_⟩
  · intro l hl
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    have hv' := hPm v hv
    refine ⟨?_,?_,?_⟩
    · change (Fin.append v t) ∈ finProduct c.rawLattice (integerLattice B.terminalDim)
      simp only [mem_finProduct,Fin.append_left,Fin.append_right]
      exact ⟨(c.mem_raw v).mpr hv'.1,ht⟩
    · simpa only [FullResidual,Fin.append_left,Fin.append_right] using And.intro hv'.2.1 htr
    · simpa only [FullSelected,Fin.append_left,Fin.append_right] using hv'.2.2
  · intro l hl j
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simp only [Fin.append_right]
  · rw [Finset.sum_image]
    · simp only [full_weight]
      rw [←Finset.sum_mul]
      apply mul_le_mul hPw' (gamma_unit_box (yr-t) htr)
        (pow_nonneg (gamma1_pos 1).le _)
        ((mul_nonneg (c.coefficient_nonneg loss hc) (by norm_num)).trans hPw')
    · intro v hv w hw he
      funext j
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd B.terminalDim j)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma gamma_le_one {n : ℕ} (x : Fin n → ℝ) : gamma x ≤ 1 := by
  apply Finset.prod_le_one (fun j _ => (gamma1_pos _).le)
  intro j _
  have hs : (1 : ℝ) ≤ Real.sqrt (2*Real.pi) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2*Real.pi by positivity)
    nlinarith [Real.pi_gt_three,Real.sqrt_nonneg (2*Real.pi)]
  have he : Real.exp (-((x j)^2)/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x j)])
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs)).mpr (by simpa using he.trans hs)

namespace Chain
variable {A B : Block}

lemma dim_last_le (c : Chain B) (hc : c.Halving) : c.dim+B.b ≤ 2*c.first.b := by
  induction c with
  | base B => simp [dim,first, two_mul]
  | @append A c B w ih =>
    have ht := ih hc.1
    change c.dim+B.b+B.b ≤ 2*c.first.b
    have hh := hc.2
    omega
lemma last_le_first (c : Chain B) (hc : c.Halving) : B.b ≤ c.first.b := by
  induction c with
  | base B => exact le_refl _
  | @append A c B w ih =>
    have ht := ih hc.1
    change B.b ≤ c.first.b
    have hh := hc.2
    omega
lemma every_le_first (c : Chain B) (hc : c.Halving) : c.Every (fun Q => Q.b ≤ c.first.b) := by
  induction c with
  | base B => exact le_refl _
  | @append A c B w ih =>
    exact ⟨ih hc.1,last_le_first (.append c B w) hc⟩

lemma blockSum_dim (c : Chain B) : c.blockSum (fun Q => (Q.b : ℝ)) = (c.dim : ℝ) := by
  induction c with
  | base B => rfl
  | append c B w ih => simp only [blockSum,dim,ih,Nat.cast_add]

lemma selected_cap (c : Chain B) (k : ℝ) (hk : 0 ≤ k)
    (hc : c.Every (AtomBound (fun Q => Real.exp (-k*(Q.b : ℝ)^(70/100 : ℝ)))))
    (y l : c.Vec) (hl : c.Selected y l) :
    c.weight y l ≤ Real.exp (-k*(c.first.b : ℝ)^(70/100 : ℝ)) := by
  induction c with
  | base B => exact B.selected_weight_le y l hl _ hc
  | @append A c B w ih =>
    have hp := ih hc.1 _ _ hl.1
    have hb := B.selected_weight_le _ _ hl.2 _ hc.2
    have he : Real.exp (-k*(B.b : ℝ)^(70/100 : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    change c.weight _ _*B.weight _ _ ≤ _
    exact (mul_le_mul_of_nonneg_left (hb.trans he) (c.weight_pos _ _).le).trans
      (by simpa only [mul_one,first] using hp)

lemma full_selected_cap (c : Chain B) (k : ℝ) (hk : 0 ≤ k)
    (hc : c.Every (AtomBound (fun Q => Real.exp (-k*(Q.b : ℝ)^(70/100 : ℝ)))))
    (y l : c.FullVec) (hl : c.FullSelected y l) :
    c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(c.first.b : ℝ)^(70/100 : ℝ)) := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_weight]
  exact (mul_le_mul_of_nonneg_left (gamma_le_one _) (c.weight_pos _ _).le).trans
    (by simpa only [mul_one] using c.selected_cap k hk hc _ _ hl)



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Filter Topology
open scoped BigOperators

lemma gamma1_le_one (x : ℝ) : gamma1 x ≤ 1 := by
  have h := gamma_le_one (fun _ : Fin 1 => x)
  simpa only [gamma,Fin.prod_univ_one] using h

namespace Chain
variable {B : Block}

lemma radius_bound (c : Chain B) (A : ℝ)
    (hc : c.Halving) (hr : c.Every (Regular A))
    (hp : c.Every (fun Q => 1 ≤ Q.b)) :
    c.radiusSq ≤ (9/2 : ℝ)*(c.first.b : ℝ)*Real.log ((c.first.b : ℝ)+1) := by
  have hf : 0 < (c.first.b : ℝ)+1 := by positivity
  have hlog : 0 ≤ Real.log ((c.first.b : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg c.first.b : (0 : ℝ) ≤ c.first.b)])
  have hle := c.every_le_first hc
  have he : c.Every (fun Q => (Q.b : ℝ)*Q.h^2 ≤
      ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) := by
    have hm : ∀ {Q : Block} (d : Chain Q), d.Every (Regular A) →
        d.Every (fun Q => 1 ≤ Q.b) → d.Every (fun Q => Q.b ≤ c.first.b) →
        d.Every (fun Q => (Q.b : ℝ)*Q.h^2 ≤
          ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) := by
      intro Q d
      induction d with
      | base Q =>
        intro hQ hpQ hlQ
        change 1 ≤ Q.b at hpQ
        change Q.b ≤ c.first.b at hlQ
        change (Q.b : ℝ)*Q.h^2 ≤ _
        rw [hQ.1]
        change (Q.b : ℝ)*heightR (Q.b : ℝ)^2 ≤ _
        rw [heightR_sq (by exact_mod_cast hpQ)]
        have hql : Real.log (Q.b : ℝ) ≤ Real.log ((c.first.b : ℝ)+1) :=
          Real.log_le_log (by exact_mod_cast (show 0 < Q.b by omega))
            (by
              have hcast : (Q.b : ℝ) ≤ c.first.b := by exact_mod_cast hlQ
              linarith)
        nlinarith [mul_le_mul_of_nonneg_left hql (Nat.cast_nonneg Q.b)]
      | append d Q w ih =>
        intro hr hp hl
        refine ⟨ih hr.1 hp.1 hl.1,?_⟩
        change (Q.b : ℝ)*Q.h^2 ≤ _
        rw [hr.2.1]
        change (Q.b : ℝ)*heightR (Q.b : ℝ)^2 ≤ _
        rw [heightR_sq (by exact_mod_cast hp.2)]
        have hql : Real.log (Q.b : ℝ) ≤ Real.log ((c.first.b : ℝ)+1) :=
          Real.log_le_log (by exact_mod_cast (show 0 < Q.b by have := hp.2; omega))
            (by
              have hcast : (Q.b : ℝ) ≤ c.first.b := by exact_mod_cast hl.2
              linarith)
        nlinarith [mul_le_mul_of_nonneg_left hql (Nat.cast_nonneg Q.b)]
    exact hm c hr hp hle
  calc
    c.radiusSq ≤ c.blockSum (fun Q => ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) :=
      c.blockSum_le _ _ he
    _ = ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(c.dim : ℝ) := by
      rw [blockSum_mul,blockSum_dim]
    _ ≤ (9/2 : ℝ)*(c.first.b : ℝ)*Real.log ((c.first.b : ℝ)+1) := by
      have hd : (c.dim : ℝ) ≤ 2*(c.first.b : ℝ) := by
        exact_mod_cast (show c.dim ≤ 2*c.first.b by have := c.dim_last_le hc; omega)
      nlinarith [mul_le_mul_of_nonneg_left hd hlog]

lemma coefficient_half (c : Chain B) (A : ℝ) (hA : 0 ≤ A) (cutoff : ℕ)
    (hcut : 1 ≤ cutoff) (hc : c.Halving)
    (hr : c.Every (fun Q => cutoff ≤ Q.b ∧
      Q.roundingLoss ≤ (Q.b : ℝ)^(-(1/100 : ℝ)) ∧ blockLoss A Q ≤ 1/2))
    (hsmall : (1+2*A)*(cutoff : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ))) ≤ 1/2) :
    1/2 ≤ c.coefficient (blockLoss A) := by
  have hl := c.every_mono hr (fun Q hQ => show blockLoss A Q ∈ Set.Icc (0 : ℝ) 1 from
    ⟨mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _),hQ.2.2.trans (by norm_num)⟩)
  obtain ⟨h0,h1,hd⟩ := c.coefficient_bounds (blockLoss A) hl
  have hsum := c.inverse_power_sum (1/100 : ℝ) (by norm_num) hc
    (c.every_mono hr (fun Q hQ => by omega))
  have hd0 : 0 < 1-(2 : ℝ)^(-(1/100 : ℝ)) := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hlast : (B.b : ℝ)^(-(1/100 : ℝ)) ≤ (cutoff : ℝ)^(-(1/100 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < cutoff by omega))
      (by exact_mod_cast (c.every_last hr).1) (by norm_num)
  have hsum' : c.blockSum (fun Q => Q.roundingLoss+2*blockLoss A Q) ≤
      (1+2*A)*c.blockSum (fun Q => (Q.b : ℝ)^(-(1/100 : ℝ))) := by
    rw [←blockSum_mul]
    apply c.blockSum_le
    exact c.every_mono hr (fun Q hQ => by dsimp [blockLoss]; nlinarith [hQ.2.1])
  have hb0 : 0 ≤ blockLoss A B := (c.every_last hl).1
  have hbound : (1+2*A)*c.blockSum (fun Q => (Q.b : ℝ)^(-(1/100 : ℝ))) ≤ 1/2 := by
    calc
      _ ≤ (1+2*A)*((B.b : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1+2*A)*((cutoff : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlast hd0.le) (by positivity)
      _ ≤ _ := by simpa only [mul_div_assoc] using hsmall
  linarith

lemma terminal_bound (c : Chain B) (A : ℝ) {cutoff M Q : ℕ}
    (hr : Regular A B) (hstop : nextSize B.b < cutoff)
    (hM : (cutoff : ℝ)^((1 : ℝ)/(9/10)) ≤ M)
    (hQ : Real.exp ((M : ℝ)^2) ≤ Q)
    (hlog : logMean (height B.b) ≤ (B.b : ℝ)) :
    B.b ≤ M ∧ B.p ≤ Q ∧ B.terminalDim ≤ M*Nat.clog 2 Q := by
  have _ := c
  have hb : (B.b : ℝ) ≤ M := by
    exact (nextSize_relation B.b).trans ((Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hstop.le) (by norm_num : (0 : ℝ) ≤ 1/(9/10))).trans hM)
  have hb' : B.b ≤ M := by exact_mod_cast hb
  have hp : Real.log B.p ≤ (M : ℝ)^2 := by
    have hs : 0 ≤ (B.b : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg B.b)
    have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg B.b) hb 2
    nlinarith [hr.2.2.1]
  have hp' : B.p ≤ Q := by
    have hexp := (Real.exp_le_exp.mpr hp).trans hQ
    rw [Real.exp_log (by exact_mod_cast B.prime.pos)] at hexp
    exact_mod_cast hexp
  exact ⟨hb',hp',Nat.mul_le_mul hb' (Nat.clog_mono_right 2 hp')⟩

end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Chain
variable {B : Block}

lemma denominators_pos (c : Chain B) : ∀ j, 0 < c.denominators j := by
  induction c with
  | base B => exact fun _ => B.prime.pos
  | append c B w ih =>
    intro j
    exact Fin.addCases (fun k => by simpa [denominators] using ih k)
      (fun k => by simpa [denominators] using B.prime.pos) j

end Chain


lemma rationalAlphabet_card (Q p : ℕ) : (rationalAlphabet Q p).card ≤ 2*Q*p+1 := by
  classical
  apply le_trans Finset.card_image_le
  rw [Int.card_Icc]
  have he : (Q : ℤ)*p+1-(-((Q : ℤ)*p)) = ((2*Q*p+1 : ℕ) : ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

lemma rationalAlphabet_log_card (Q p : ℕ) (hQ : 1 ≤ Q) (hp : 1 ≤ p) :
    Real.log ((rationalAlphabet Q p).card+1 : ℝ) ≤
      Real.log 4+Real.log (Q : ℝ)+Real.log (p : ℝ) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcard : ((rationalAlphabet Q p).card : ℝ) ≤ 2*(Q : ℝ)*p+1 := by
    exact_mod_cast rationalAlphabet_card Q p
  have hprod : (1 : ℝ) ≤ (Q : ℝ)*p := by nlinarith [mul_nonneg (sub_nonneg.mpr hQr) (sub_nonneg.mpr hpr)]
  have hle : ((rationalAlphabet Q p).card+1 : ℝ) ≤ 4*(Q : ℝ)*p := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (rationalAlphabet Q p).card+1) hle
  calc
    _ ≤ Real.log (4*(Q : ℝ)*p) := hlog
    _ = _ := by rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]

namespace Chain
variable {B : Block}
lemma every_and {P Q : Block → Prop} (c : Chain B) (hP : c.Every P) (hQ : c.Every Q) :
    c.Every (fun B => P B ∧ Q B) := by
  induction c with
  | base B => exact ⟨hP,hQ⟩
  | append c B w ih => exact ⟨ih hP.1 hQ.1, hP.2,hQ.2⟩

lemma denominator_log_le (c : Chain B) {R : ℝ}
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) :
    ∀ j, Real.log (c.denominators j : ℝ) ≤ R := by
  induction c with
  | base B => exact fun _ => hc
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [denominators,Fin.append_left] using ih hc.1 k
    · simpa only [denominators,Fin.append_right] using hc.2

lemma full_denominator_log_le (c : Chain B) {R : ℝ} (hR : 0 ≤ R)
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) :
    ∀ j, Real.log (c.fullDenominators j : ℝ) ≤ R := by
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [fullDenominators,Fin.append_left] using c.denominator_log_le hc k
  · simpa only [fullDenominators,Fin.append_right,Nat.cast_one,Real.log_one] using hR

lemma alphabet_log_card (c : Chain B) {R : ℝ} (hR : 0 ≤ R)
    (hc : c.Every (fun B => Real.log (B.p : ℝ) ≤ R)) (j : Fin c.fullDim) :
    Real.log ((c.alphabets j).card+1 : ℝ) ≤
      Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+R := by
  have hp : 1 ≤ c.fullDenominators j := by
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [fullDenominators,Fin.append_left] using Nat.succ_le_iff.mpr (c.denominators_pos k)
    · simp [fullDenominators]
  have hQ : 1 ≤ c.alphabetRadius := by dsimp [alphabetRadius]; omega
  have hlog := rationalAlphabet_log_card c.alphabetRadius (c.fullDenominators j) hQ hp
  have hx : (1 : ℝ) ≤ ((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := one_le_pow₀ (by norm_cast; omega)
  have hQr : (c.alphabetRadius : ℝ) ≤ 2*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
    have heq : (c.alphabetRadius : ℝ) = 1+((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
      simp only [alphabetRadius,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
    rw [heq]
    linarith
  have hlogQ : Real.log (c.alphabetRadius : ℝ) ≤
      Real.log 2+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2) := by
    have h : (0 : ℝ) < c.alphabetRadius := by exact_mod_cast (show 0 < c.alphabetRadius by omega)
    have ht := Real.log_le_log h hQr
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at ht
    convert ht using 1 ; push_cast ; rfl
  have hlogp := c.full_denominator_log_le hR hc j
  have h48 : Real.log (4 : ℝ)+Real.log 2=Real.log 8 := by
    rw [←Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  change Real.log ((rationalAlphabet c.alphabetRadius (c.fullDenominators j)).card+1 : ℝ) ≤ _
  linarith

lemma regular_primes_log_bound (c : Chain B) (A : ℝ) (hc : c.Halving)
    (hr : c.Every (fun W => Regular A W ∧ logMean (height W.b) ≤ (W.b : ℝ))) :
    c.Every (fun W => Real.log (W.p : ℝ) ≤ (c.first.b : ℝ)^2) := by
  apply c.every_mono (c.every_and hr (c.every_le_first hc))
  intro W hW
  have hs : 0 ≤ (W.b : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hm := mul_le_mul_of_nonneg_left hW.1.2 (Nat.cast_nonneg W.b)
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg W.b)
    (show (W.b : ℝ) ≤ c.first.b by exact_mod_cast hW.2) 2
  nlinarith [hW.1.1.2.2.1]


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Filter Topology
open scoped BigOperators




theorem vertical_patterns_alphabets :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧ ∃ C k κ : ℝ, 0 < C ∧ 0 < k ∧ 0 < κ ∧
      ∀ b₁ ≥ cutoff, ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.CeilingSizes ∧
        (c.dim+B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)+1) ∧
        c.radiusSq+(B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)*Real.log ((b₁ : ℝ)+1)+1) ∧
        (∀ j, Real.log ((c.alphabets j).card+1 : ℝ) ≤
          Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(b₁ : ℝ)^2) ∧
        ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
          P.Nonempty ∧ SuffixBinary P ∧
          (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
            c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(b₁ : ℝ)^(70/100 : ℝ))) ∧
          (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
          κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  classical
  obtain ⟨A,hA,N,hN,hsmall,hbuild⟩ := hierarchy_preparation
  obtain ⟨k,hk,hatom⟩ := eventually_eligible_atom
  have hround : ∀ᶠ b : ℕ in atTop, ∀ p : ℕ, 0 < p →
      (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
      (b : ℝ)*height b^2/p ≤ (b : ℝ)^(-(1/100 : ℝ)) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
      eventually_ge_atTop (1 : ℕ)] with b hb hb1 p hp hpl
    exact (hb p (by exact_mod_cast hp) hpl).1.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1) (by norm_num))
  have hden : 0 < 1-(2 : ℝ)^(-(1/100 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hsumSmall : ∀ᶠ b : ℕ in atTop,
      (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ))) ≤ 1/2 := by
    have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul (1+2*A)).div_const
      (1-(2 : ℝ)^(-(1/100 : ℝ)))
    have hn : Tendsto (fun b : ℕ => (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/
        (1-(2 : ℝ)^(-(1/100 : ℝ)))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,mul_zero,zero_div] using ht.comp hcast
    exact hn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N',hN'⟩ := eventually_atTop.mp (hatom.and (hround.and hsumSmall))
  let cutoff := max N N'
  have hcutN : N ≤ cutoff := le_max_left _ _
  have hcutN' : N' ≤ cutoff := le_max_right _ _
  have hcut2 : 2 ≤ cutoff := hN.trans hcutN
  let M : ℕ := ⌈(cutoff : ℝ)^((1 : ℝ)/(9/10))⌉₊
  let Q : ℕ := ⌈Real.exp ((M : ℝ)^2)⌉₊
  let T : ℕ := M*Nat.clog 2 Q
  let C : ℝ := (T : ℝ)+5
  let κ : ℝ := (1/4 : ℝ)*gamma1 1^T
  have hκ : 0 < κ := mul_pos (by norm_num) (pow_pos (gamma1_pos 1) _)
  refine ⟨cutoff,hcut2,C,k,κ,by dsimp [C]; positivity,hk,hκ,?_⟩
  intro b₁ hb₁
  obtain ⟨B,c,hfirst,hreg,hgood,hhalf,hsizes,hstop⟩ := hbuild cutoff hcutN b₁ hb₁
  have hbN (W : Block) (hW : cutoff ≤ W.b) := hsmall W.b (hcutN.trans hW)
  have hbN' (W : Block) (hW : cutoff ≤ W.b) := hN' W.b (hcutN'.trans hW)
  have hr := c.every_mono hreg (fun W hW => hW.2)
  have hpos := c.every_mono hreg (fun W hW => show 1 ≤ W.b by omega)
  have hB := c.every_last hreg
  have hBound := c.terminal_bound A hB.2 hstop (Nat.le_ceil _) (Nat.le_ceil _) (hbN B hB.1).2
  have hT : B.terminalDim ≤ T := hBound.2.2
  have hloss : c.Every (fun W => cutoff ≤ W.b ∧
      W.roundingLoss ≤ (W.b : ℝ)^(-(1/100 : ℝ)) ∧ blockLoss A W ≤ 1/2) := by
    apply c.every_mono hreg
    intro W hW
    refine ⟨hW.1,?_,(hbN W hW.1).1⟩
    dsimp [Block.roundingLoss]
    rw [hW.2.1]
    exact (hbN' W hW.1).2.1 W.p W.prime.pos hW.2.2.1
  have hcoeff : 1/2 ≤ c.coefficient (blockLoss A) :=
    c.coefficient_half A hA.le cutoff (by omega) hhalf hloss (hN' cutoff hcutN').2.2
  have hcAtoms : c.Every (Chain.AtomBound (fun W => Real.exp (-k*(W.b : ℝ)^(70/100 : ℝ)))) := by
    apply c.every_mono hreg
    intro W hW z hz t ht e
    rw [hW.2.1]
    exact ((hbN' W hW.1).1 W.p hW.2.2.1 z (hW.2.2.2.2.1 hz) t ht e).2
  refine ⟨B,c,hfirst,hsizes,?_,?_,?_,?_⟩
  · have hd : (c.dim : ℝ) ≤ 2*(b₁ : ℝ) := by
      exact_mod_cast (show c.dim ≤ 2*b₁ by have := c.dim_last_le hhalf; omega)
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [C]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T),(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁),
      mul_nonneg (show (0 : ℝ) ≤ T by positivity) (show (0 : ℝ) ≤ b₁ by positivity)]
  · have hradius := c.radius_bound A hhalf hr hpos
    rw [hfirst] at hradius
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    have hlog : 0 ≤ Real.log ((b₁ : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁)])
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg b₁) hlog,
      mul_nonneg (Nat.cast_nonneg T) (mul_nonneg (Nat.cast_nonneg b₁) hlog)]
  · have hrlog : c.Every (fun W => Regular A W ∧ logMean (height W.b) ≤ (W.b : ℝ)) := by
      apply c.every_mono hreg
      intro W hW
      exact ⟨hW.2,(hbN W hW.1).2⟩
    have hlog := c.regular_primes_log_bound A hhalf hrlog
    rw [hfirst] at hlog
    exact c.alphabet_log_card (sq_nonneg _) hlog
  · intro y
    obtain ⟨P,hPb,hPl,hPt,hPw⟩ := c.full_patterns (blockLoss A) hgood
      (regular_mean hB.2 (hbN B hB.1).1).1 y
    have hgT : gamma1 1^T ≤ gamma1 1^B.terminalDim :=
      pow_le_pow_of_le_one (gamma1_pos 1).le (gamma1_le_one 1) hT
    have hweight : κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
      apply le_trans _ hPw
      dsimp [κ]
      have h0 : 0 ≤ gamma1 1^B.terminalDim := (pow_pos (gamma1_pos 1) _).le
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) h0]
    have hPn : P.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hweight
      exact (not_le_of_gt hκ) hweight
    refine ⟨P,hPn,hPb,?_,hPt,hweight⟩
    intro l hl
    have hle := hPl l hl
    refine ⟨hle.1,hle.2.1,?_⟩
    have hcap := c.full_selected_cap k hk.le hcAtoms y l hle.2.2
    simpa only [hfirst] using hcap


end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear

universe u



namespace Pattern
variable {α : Type*}

lemma size_le_two_pow {q : ℕ} (p : Pattern α q) : p.size ≤ 2^q := by
  induction p with
  | leaf => simp [size]
  | @mono q v p ih =>
    simpa only [size, pow_succ] using ih.trans (Nat.le_mul_of_pos_right (2^q) (by decide))
  | @split q v p r ih ihr =>
    simp only [size, pow_succ]
    omega

end Pattern



end SingleLatticeCovering.Shear


end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear
variable {α : Type*}

namespace Pattern
lemma UniqueLabels_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : UniqueLabels s) (v : ℝ) : UniqueLabels (slice s v) := by
  intro l hl r hr h
  have heq : (appendPoint v l).1 = (appendPoint v r).1 := congrArg (fun x : Fin q → ℝ => Fin.snoc (α := fun _ => ℝ) x v) h
  exact hs _ ((mem_slice _ _ _).mp hl) _ ((mem_slice _ _ _).mp hr) heq

lemma SuffixBinary_slice {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) (v : ℝ) : SuffixBinary (slice s v) := by
  intro j y
  obtain ⟨a,ha⟩ := hs j.castSucc (Fin.snoc (α := fun _ => ℝ) y v)
  refine ⟨a, ?_⟩
  intro l hl hy
  have htail : ∀ k : Fin (q+1), j.castSucc < k →
      (appendPoint v l).1 k = (Fin.snoc (α := fun _ => ℝ) y v) k := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · intro hk
      simp only [appendPoint, Fin.snoc_last]
    · intro hk
      simp only [appendPoint, Fin.snoc_castSucc]
      exact hy k (by simpa using hk)
  simpa only [appendPoint, Fin.snoc_castSucc] using ha _ ((mem_slice _ _ _).mp hl) htail

lemma suffix_last_bound {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)}
    (hs : SuffixBinary s) : ∃ v : ℝ, ∀ l ∈ s,
      l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  obtain ⟨v,hv⟩ := hs (Fin.last q) 0
  refine ⟨v, fun l hl => hv l hl ?_⟩
  intro k hk
  exact False.elim ((not_lt_of_ge (Fin.le_last k)) hk)

attribute [local instance] OAI.SingleLatticeCovering.Shear.instDecidableEqProdForallFinReal_solutions
lemma slice_partition {q : ℕ} {s : Finset ((Fin (q+1) → ℝ) × α)} (v : ℝ)
    (hv : ∀ l ∈ s, l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1) :
    s = (slice s v).image (appendPoint v) ∪ (slice s (v+1)).image (appendPoint (v+1)) := by
  classical
  have hin (l : (Fin (q+1) → ℝ) × α) (a : ℝ) (hl : l ∈ s) (ha : l.1 (Fin.last q)=a) :
      l ∈ (slice s a).image (appendPoint a) := by
    have heq : appendPoint a (Fin.init l.1, l.2) = l := by
      simp only [appendPoint, ← ha, Fin.snoc_init_self]
    exact Finset.mem_image.mpr ⟨(Fin.init l.1,l.2), (mem_slice _ _ _).mpr (heq.symm ▸ hl), heq⟩
  ext l
  constructor
  · intro hl
    rcases hv l hl with h | h
    · exact Finset.mem_union_left _ (hin l v hl h)
    · exact Finset.mem_union_right _ (hin l (v+1) hl h)
  · intro hl
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact (mem_slice _ _ _).mp ha


lemma exists_tree {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (hs : SourcePattern s) :
    ∃ p : Pattern α q, p.points=s := by
  classical
  induction q with
  | zero =>
    obtain ⟨a,ha⟩ := hs.1
    refine ⟨.leaf a.2, ?_⟩
    have hcoord (l : (Fin 0 → ℝ) × α) : l.1=0 := by ext i; exact Fin.elim0 i
    ext l
    simp only [points, Finset.mem_singleton]
    constructor
    · rintro rfl
      convert ha using 1
      exact Prod.ext (hcoord a).symm rfl
    · intro hl
      exact Prod.ext (hcoord l) (hs.2.1 l hl a ha ((hcoord l).trans (hcoord a).symm))
  | succ q ih =>
    obtain ⟨v,hv⟩ := suffix_last_bound hs.2.2
    have hpart := slice_partition v hv
    have h0 := UniqueLabels_slice hs.2.1 v
    have h1 := UniqueLabels_slice hs.2.1 (v+1)
    have hb0 := SuffixBinary_slice hs.2.2 v
    have hb1 := SuffixBinary_slice hs.2.2 (v+1)
    by_cases hn0 : (slice s v).Nonempty
    · obtain ⟨p,hp⟩ := ih _ ⟨hn0,h0,hb0⟩
      by_cases hn1 : (slice s (v+1)).Nonempty
      · obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
        exact ⟨.split v p r, by rw [points, hp, hr, ← hpart]⟩
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn1
        exact ⟨.mono v p, by simpa only [points, hp, he, Finset.image_empty, Finset.union_empty] using hpart.symm⟩
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn0
      have hn1 : (slice s (v+1)).Nonempty := by
        by_contra hn1
        have he1 := Finset.not_nonempty_iff_eq_empty.mp hn1
        simp only [he, he1, Finset.image_empty, Finset.union_self] at hpart
        exact hs.1.ne_empty hpart
      obtain ⟨r,hr⟩ := ih _ ⟨hn1,h1,hb1⟩
      exact ⟨.mono (v+1) r, by simpa only [points, hr, he, Finset.image_empty, Finset.empty_union] using hpart.symm⟩

end Pattern
end SingleLatticeCovering.Shear



namespace SingleLatticeCovering.Shear
open scoped BigOperators

lemma source_card_le_two_pow {α : Type*} {q : ℕ}
    {s : Finset ((Fin q → ℝ) × α)} (hs : SourcePattern s) : s.card ≤ 2^q := by
  obtain ⟨p,hp⟩ := Pattern.exists_tree s hs
  rw [←hp,Pattern.points_card]
  exact p.size_le_two_pow



lemma small_subsets_card {α : Type*} (s : Finset α) (k : ℕ) :
    (s.powerset.filter (fun t => t.card ≤ k)).card ≤ (s.card+1)^k := by
  classical
  induction k with
  | zero =>
    have hsub : s.powerset.filter (fun t => t.card ≤ 0) ⊆ {∅} := by
      intro t ht
      have ht0 := (Finset.mem_filter.mp ht).2
      simp only [Nat.le_zero, Finset.card_eq_zero] at ht0
      simpa using ht0
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    let F := s.powerset.filter (fun t => t.card ≤ k)
    have hsub : s.powerset.filter (fun t => t.card ≤ k+1) ⊆
        F ∪ s.biUnion (fun a => F.image (insert a)) := by
      intro t ht
      obtain ⟨hts,htk⟩ := Finset.mem_filter.mp ht
      have hts' := Finset.mem_powerset.mp hts
      by_cases hem : t=∅
      · subst t
        apply Finset.mem_union_left
        simp [F]
      · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hem
        have hE : t.erase a ∈ F := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr ((Finset.erase_subset a t).trans hts'),?_⟩
          have hcard := Finset.card_erase_add_one ha
          omega
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨a,hts' ha,Finset.mem_image.mpr
          ⟨t.erase a,hE,Finset.insert_erase ha⟩⟩
    calc
      _ ≤ (F ∪ s.biUnion (fun a => F.image (insert a))).card := Finset.card_le_card hsub
      _ ≤ F.card+(s.biUnion (fun a => F.image (insert a))).card := Finset.card_union_le _ _
      _ ≤ F.card+∑ a ∈ s, (F.image (insert a)).card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
      _ ≤ F.card+s.card*F.card := by
        apply Nat.add_le_add_left
        simpa using Finset.sum_le_sum (fun a (ha : a ∈ s) => Finset.card_image_le (s := F) (f := insert a))
      _ = (s.card+1)*F.card := by ring
      _ ≤ (s.card+1)*(s.card+1)^k := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

lemma mem_allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ)
    (s : Finset ((Fin q → ℝ) × α)) : s ∈ allPatterns A labels q ↔
      s ⊆ alphabetPoints A labels q ∧ SourcePattern s := by
  classical
  simp [allPatterns]

lemma allPatterns_card_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    (allPatterns A labels q).card ≤ ((alphabetPoints A labels q).card+1)^(2^q) := by
  classical
  apply le_trans _ (small_subsets_card (alphabetPoints A labels q) (2^q))
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsub,hsource⟩ := (mem_allPatterns A labels q s).mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub,source_card_le_two_pow hsource⟩

lemma allPatterns_total_bound {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α)
    (D N : ℕ) (hN : ∀ q ≤ D, (alphabetPoints A labels q).card ≤ N) :
    (∑ q ∈ Finset.range (D+1), (allPatterns A labels q).card) ≤ (D+1)*(N+1)^(2^D) := by
  have hf (q : ℕ) (hq : q ∈ Finset.range (D+1)) :
      (allPatterns A labels q).card ≤ (N+1)^(2^D) := by
    have hq' : q ≤ D := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hq
    calc
      _ ≤ ((alphabetPoints A labels q).card+1)^(2^q) := allPatterns_card_bound A labels q
      _ ≤ (N+1)^(2^q) := Nat.pow_le_pow_left (Nat.add_le_add_right (hN q hq') 1) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hq')
  simpa using Finset.sum_le_sum hf


end SingleLatticeCovering.Shear

end
end

section



noncomputable section
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

namespace SingleLatticeCovering.Completion

lemma mem_contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n))
    (a : ℝ) (ha : a ≠ 0) (x : RealSpace n) :
    x ∈ contractLattice L a ha ↔ a • x ∈ L := Iff.rfl

lemma contractLattice_covolume {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : 0 < a) :
    ZLattice.covolume (contractLattice L a ha.ne') = a⁻¹^n * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let e := LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha.ne'
  let b' := b.ofZLatticeComap ℝ L e
  let : DiscreteTopology (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_discrete L a ha.ne'
  let : IsZLattice ℝ (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_fullSpan L a ha.ne'
  change ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) = _
  rw [ZLattice.covolume_eq_det _ b', ZLattice.covolume_eq_det _ b]
  have hm : Matrix.of (Subtype.val ∘ b') = a⁻¹ • (Matrix.of (Subtype.val ∘ b) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.smul_apply,
      Basis.ofZLatticeComap_apply, LinearEquiv.smulOfNeZero_symm_apply, Pi.smul_apply,
      smul_eq_mul, b', e]
    simp [Units.smul_def]
  rw [hm, Matrix.det_smul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr ha), Fintype.card_fin]



end SingleLatticeCovering.Completion

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affine_image_volume {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (t : Fin n → ℝ) (K : Set (Fin n → ℝ)) :
    volume ((fun x => e x+t) '' K) = ENNReal.ofReal |LinearMap.det e.toLinearMap| * volume K := by
  have hs : (fun x => e x+t) '' K = (fun x => x+t) '' (e '' K) := by
    rw [Set.image_image]
  rw [hs,Set.image_add_right,measure_preimage_add_right]
  exact volume.addHaar_image_linearMap e.toLinearMap K

lemma affine_image_cover {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hcover : K+(L : Set (Fin n → ℝ))=Set.univ) :
    (fun x => e x+t) '' K+(image L e : Set (Fin n → ℝ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : e.symm (x-t) ∈ K+(L : Set (Fin n → ℝ)) := by rw [hcover]; trivial
  obtain ⟨k,hk,l,hl,hkl⟩ := hx
  refine ⟨e k+t,⟨k,hk,rfl⟩,e l,(mem_image L e (e l)).mpr ⟨l,hl,rfl⟩,?_⟩
  change e k+t+e l=x
  have he : e k+e l=x-t := by
    rw [←map_add]
    change k+l=e.symm (x-t) at hkl
    rw [hkl,e.apply_symm_apply]
  calc e k+t+e l = (e k+e l)+t := by abel
       _ = x := by rw [he]; abel

lemma affine_image_density {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) :
    (volume ((fun x => e x+t) '' K)).toReal / ZLattice.covolume (image L e) =
      (volume K).toReal / ZLattice.covolume L := by
  rw [affine_image_volume,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),image_covolume]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr e.isUnit_det'.ne_zero)


end SingleLatticeCovering.LatticeGeometry

noncomputable section
namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affineEquiv_eq_linear_add {n : ℕ}
    (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) : e x=e.linear x+e 0 := by
  have h := e.map_vadd (0 : Fin n → ℝ) x
  simpa using h



lemma pull_back_cover {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hcover : e '' K+(L : Set (Fin n → ℝ))=Set.univ) {d : ℝ}
    (hd : (volume (e '' K)).toReal/ZLattice.covolume L ≤ d) :
    ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      K+(Λ : Set (Fin n → ℝ))=Set.univ ∧ (volume K).toReal/ZLattice.covolume Λ ≤ d := by
  let Λ := image L e.symm.linear
  have he : (fun x => e.symm.linear x+e.symm 0) '' (e '' K)=K := by
    simp_rw [←affineEquiv_eq_linear_add]
    exact e.symm_image_image K
  refine ⟨Λ,inferInstance,inferInstance,?_,?_⟩
  · have h := affine_image_cover L e.symm.linear (e.symm 0) (e '' K) hcover
    rwa [he] at h
  · have h := affine_image_density L e.symm.linear (e.symm 0) (e '' K)
    rw [he] at h
    exact h.trans_le hd


end SingleLatticeCovering.LatticeGeometry

end
end

section


noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators




noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fiber_compact {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K) (y : F) :
    IsCompact (fiber K y) := by
  have he : fiber K y = Prod.fst '' (K ∩ Prod.snd ⁻¹' {y}) := by
    ext x; constructor
    · intro hx; exact ⟨(x,y),⟨hx,by simp⟩,rfl⟩
    · rintro ⟨⟨x',y'⟩,⟨hxy,hy⟩,hx⟩
      have hy' : y'=y := hy
      change x'=x at hx
      subst x'; subst y'; exact hxy
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst




end SingleLatticeCovering.Sections





end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma eventually_fiber_subset {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K)
    {y : F} {U : Set E} (hU : IsOpen U) (hyU : fiber K y ⊆ U) :
    ∀ᶠ z in 𝓝 y, fiber K z ⊆ U := by
  let A : Set F := Prod.snd '' (K ∩ Prod.fst ⁻¹' Uᶜ)
  have hA : IsClosed A := ((hK.inter_right (hU.isClosed_compl.preimage continuous_fst)).image continuous_snd).isClosed
  have hy : y ∈ Aᶜ := by
    rintro ⟨⟨x,z⟩,⟨hx,hxU⟩,he⟩
    change z=y at he
    subst z
    exact hxU (hyU hx)
  filter_upwards [hA.isOpen_compl.mem_nhds hy] with z hz
  intro x hx
  by_contra hxU
  exact hz ⟨(x,z),⟨hx,hxU⟩,rfl⟩

lemma upperSemicontinuous_fiber_measure [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [OuterRegular μ] {K : Set (E × F)} (hK : IsCompact K) :
    UpperSemicontinuous (fun y : F => μ (fiber K y)) := by
  intro y r hyr
  obtain ⟨U,hfU,hU,hμU⟩ := (fiber K y).exists_isOpen_lt_of_lt r hyr
  filter_upwards [eventually_fiber_subset hK hU hfU] with z hz
  exact (measure_mono hz).trans_lt hμU



end SingleLatticeCovering.Sections

end
end
end
end
end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory
open scoped BigOperators

lemma gaussian_toLp {D : ℕ} (y : Fin D → ℝ) :
    gaussian (EuclideanSpace ℝ (Fin D)) (WithLp.toLp 2 y)=Folded.gamma y := by
  classical
  unfold gaussian Folded.gamma Folded.gamma1
  rw [finrank_euclideanSpace_fin,EuclideanSpace.real_norm_sq_eq]
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← Real.exp_sum,zpow_neg,zpow_natCast]
  rw [div_eq_mul_inv,mul_comm]
  congr 2
  simp only [div_eq_mul_inv,Finset.sum_mul,Finset.sum_neg_distrib,neg_mul]

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory LatticeGeometry
open scoped BigOperators

lemma appendEquiv_measurePreserving (m D : ℕ) :
    MeasurePreserving (appendEquiv m D)
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin D → ℝ))) volume := by
  have h := (volume_preserving_arrowCongr' (finSumFinEquiv (m := m) (n := D))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin D => ℝ))
  have he : (fun t : (Fin m → ℝ) × (Fin D → ℝ) =>
      (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin D => ℝ)).symm t))=
      appendEquiv m D := by
    funext t i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [MeasurableEquiv.arrowCongr',MeasurableEquiv.sumPiEquivProdPi,
        Equiv.arrowCongr',appendEquiv,Fin.appendEquiv]
  exact he ▸ h

lemma flatten_measurePreserving (m D : ℕ) :
    MeasurePreserving (flatten m D) volume volume :=
  (appendEquiv_measurePreserving m D).comp
    ((MeasurePreserving.id (volume : Measure (Fin m → ℝ))).prod
      (PiLp.volume_preserving_ofLp (Fin D)))

lemma flatten_volume (m D : ℕ) {K : Set ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D))}
    (hK : IsCompact K) : volume (flatten m D '' K)=volume K := by
  have h := (flatten_measurePreserving m D).measure_preimage
    ((hK.image (flatten m D).toContinuousLinearEquiv.continuous).measurableSet.nullMeasurableSet)
  change volume ((flatten m D) ⁻¹' ((flatten m D) '' K))=volume ((flatten m D) '' K) at h
  rw [(flatten m D).injective.preimage_image] at h
  exact h.symm

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory Set
open scoped BigOperators



lemma flatten_fiber {m D : ℕ} (K : Set (Fin (m+D) → ℝ)) (y : EuclideanSpace ℝ (Fin D)) :
    fiber ((flatten m D).symm '' K) y=coordinateFiber K (WithLp.ofLp y) := by
  ext x
  change (x,y) ∈ (flatten m D).symm '' K ↔ _
  constructor
  · rintro ⟨z,hz,hzxy⟩
    change flatten m D (x,y) ∈ K
    rw [←hzxy,(flatten m D).apply_symm_apply]
    exact hz
  · intro hx
    exact ⟨flatten m D (x,y),hx,(flatten m D).symm_apply_apply _⟩



end SingleLatticeCovering.Sections

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Rates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Real Filter Topology Asymptotics

namespace SingleLatticeCovering.FinalRates

lemma loglog_nat_atTop : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma loglog_sq_littleO :
    (fun n : ℕ => (Real.log (Real.log (n : ℝ)))^2) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
  simpa only [Function.comp_def,Real.rpow_two,Real.rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp_tendsto log_nat_atTop

lemma firstSize_tendsto : Tendsto firstSize atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  simpa only [Function.comp_def,Real.rpow_two] using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp loglog_nat_atTop

lemma eventually_firstSize_le_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (firstSize n : ℝ)+1 ≤ c*Real.log (n : ℝ) := by
  filter_upwards [loglog_sq_littleO.bound (half_pos hc),
    log_nat_atTop.eventually (eventually_ge_atTop (4/c))] with n hs hl
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n : ℝ))))
  have he : 4 ≤ c*Real.log (n : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hl
  change (firstSize n : ℝ) < (Real.log (Real.log (n : ℝ)))^2+1 at hceil
  linarith



lemma eventually_dimension_power {C a r : ℝ} (hC : 0 < C) (ha : 1 < a) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      a^D ≤ (n : ℝ)^r := by
  have hal : 0 < Real.log a := Real.log_pos ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  filter_upwards [eventually_firstSize_le_log (div_pos hr (mul_pos hC hal)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 D hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  apply (Real.log_le_log_iff (pow_pos ha0 _) (Real.rpow_pos_of_pos hn0 r)).mp
  rw [Real.log_pow,Real.log_rpow hn0]
  calc
    (D : ℝ)*Real.log a ≤ C*((firstSize n : ℝ)+1)*Real.log a :=
      mul_le_mul_of_nonneg_right hD hal.le
    _ = (C*Real.log a)*((firstSize n : ℝ)+1) := by ring
    _ ≤ (C*Real.log a)*(r/(C*Real.log a)*Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (mul_pos hC hal).le
    _ = r*Real.log (n : ℝ) := by field_simp

lemma eventually_superlinear_power {k : ℝ} (hk : 0 < k) :
    ∀ᶠ s : ℝ in atTop, 2*s ≤ k*s^(7/5 : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually
      (eventually_ge_atTop (2/k))] with s hs hpow
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hmul : 2 ≤ k*s^(2/5 : ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hk).mp hpow
  have he : s^(7/5 : ℝ)=s*s^(2/5 : ℝ) := by
    rw [show (7/5 : ℝ)=1+2/5 by norm_num,Real.rpow_add hs0,Real.rpow_one]
  rw [he]
  nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hmul)]



lemma cap_log_tendsto {k : ℝ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-Real.log (Real.log (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp loglog_nat_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le)) ?_ hexp
  filter_upwards [loglog_nat_atTop.eventually (eventually_superlinear_power hk),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with n hpow hs hn
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hs0 : 0 ≤ Real.log (Real.log (n : ℝ)) := le_trans zero_le_one hs
  have hceil := Nat.le_ceil ((Real.log (Real.log (n : ℝ)))^2)
  have hcappow : (Real.log (Real.log (n : ℝ)))^(7/5 : ℝ) ≤
      (firstSize n : ℝ)^(70/100 : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (Real.log (Real.log (n : ℝ)))) hceil
      (by norm_num : (0 : ℝ) ≤ 70/100)
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hs0] at hh
    norm_num at hh
    simpa only [firstSize,show (70/100 : ℝ)=(7/10 : ℝ) by norm_num] using hh
  conv_lhs => rw [←Real.exp_log hnlog,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hcappow hk.le]



end SingleLatticeCovering.FinalRates
noncomputable section

namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

lemma eventually_log_power_bound (k : ℕ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ))^k ≤ ε*(n : ℝ)^r := by
  have h : (fun n : ℕ => (Real.log (n : ℝ))^k) =o[atTop]
      (fun n : ℕ => (n : ℝ)^r) := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h.bound hε] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn

lemma eventually_dimension_small {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (D : ℝ) ≤ Real.log (n : ℝ) ∧ (D : ℝ) ≤ (n : ℝ)/2 := by
  filter_upwards [eventually_firstSize_le_log (inv_pos.mpr hC),
    eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2)] with n hn hlog D hD
  have hDl : (D : ℝ) ≤ Real.log (n : ℝ) := by
    calc
      _ ≤ C*((firstSize n : ℝ)+1) := hD
      _ ≤ C*(C⁻¹*Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hn hC.le
      _ = Real.log (n : ℝ) := by field_simp
  refine ⟨hDl,hDl.trans ?_⟩
  simpa only [pow_one,Real.rpow_one,one_div,mul_comm,div_eq_mul_inv,one_mul] using hlog

lemma eta_linear_lower :
    ∀ᶠ m : ℕ in atTop, (Real.log (27/16 : ℝ)/8)*(m : ℝ) ≤ eta m := by
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_log_power_bound 1 (by norm_num : (0 : ℝ) < 1)
    (div_pos hlog (by norm_num : (0 : ℝ) < 24))] with m hm
  simp only [pow_one,Real.rpow_one] at hm
  dsimp [eta]
  linarith

lemma eventually_cap_linear {k H ε : ℝ} (hk : 0 < k) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ)/2 ≤ m →
      H*(n : ℝ)*Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ ε*m := by
  have _ := hH
  have ht : Tendsto (fun n : ℕ => H*(Real.log (n : ℝ)*
      Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (cap_log_tendsto hk).const_mul H
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with n hn m hm
  calc
    _ = (n : ℝ)*(H*(Real.log (n : ℝ)*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)))) := by ring
    _ ≤ (n : ℝ)*(ε/2) := mul_le_mul_of_nonneg_left hn.le (Nat.cast_nonneg n)
    _ ≤ ε*m := by nlinarith



lemma eventually_cap_eta {C k H : ℝ} (hC : 0 < C) (hk : 0 < k) (hH : 0 ≤ H) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ H*(n : ℝ)*Real.log (n : ℝ)*
        Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp eta_linear_lower
  have hlog : 0 < Real.log (27/16 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_dimension_small hC,
    eventually_cap_linear hk hH (div_pos hlog (by norm_num : (0 : ℝ) < 8)),
    eventually_ge_atTop (2*M)] with n hD hn hnM D hdim
  have hhalf := (hD D hdim).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hm : (n : ℝ)/2 ≤ (n-D : ℕ) := by rw [Nat.cast_sub hDn]; linarith
  have hMm : M ≤ n-D := by
    have hnMr : (2 : ℝ)*M ≤ n := by exact_mod_cast hnM
    exact_mod_cast (show (M : ℝ) ≤ (n-D : ℕ) from by linarith)
  exact ⟨hDn,(hn (n-D) hm).trans (hM _ hMm)⟩

lemma eventually_rpow_bound {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^a ≤ ε*(n : ℝ)^b := by
  filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1/ε)),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm : 1 ≤ ε*(n : ℝ)^(b-a) := by
    simpa only [Function.comp_def,mul_comm] using (div_le_iff₀ hε).mp hn
  have he : (n : ℝ)^b=(n : ℝ)^a*(n : ℝ)^(b-a) := by
    rw [←Real.rpow_add hn0]; congr 1; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hn0 a).le]

lemma sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop

lemma sqrt_half_bound {n m : ℕ} (hm : (n : ℝ)/2 ≤ m) :
    Real.sqrt (n : ℝ) ≤ 2*Real.sqrt (m : ℝ) := by
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  have hm0 := Real.sqrt_nonneg (m : ℝ)
  have hn2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm2 := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith


lemma eventually_discard_bound {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) → m ≤ n →
      (2 : ℝ)^D*Real.sqrt (m : ℝ) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  filter_upwards [eventually_dimension_power hC (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1/4),
    eventually_rpow_bound (by norm_num : (3/4 : ℝ) < 1) hε,
    log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hp hr hlog hn1 D m hD hmn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    _ ≤ (n : ℝ)^(1/4 : ℝ)*Real.sqrt (n : ℝ) :=
      mul_le_mul (hp D hD) (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
        (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hn0 _).le
    _ = (n : ℝ)^(3/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hn0]; norm_num
    _ ≤ ε*(n : ℝ) := by simpa only [Real.rpow_one] using hr
    _ ≤ ε*(n : ℝ)*Real.log (n : ℝ) := le_mul_of_one_le_right (by positivity) hlog



lemma eventually_label_criterion {C Cs CR : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∀ᶠ n : ℕ in atTop, ∀ D m : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      (n : ℝ)/2 ≤ m → m ≤ n →
      (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) < 1 := by
  have hCR1 : 0 < 1+CR := by linarith
  have hCs0 : 0 < Cs := lt_of_lt_of_le zero_lt_one hCs
  filter_upwards [eventually_dimension_small hC,
    eventually_log_power_bound 2 (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (0 : ℝ) < 1/48),
    sqrt_nat_atTop.eventually (eventually_ge_atTop (16*(Real.log (1+CR)+1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Cs),
    eventually_ge_atTop (2 : ℕ)] with n hdim hpoly hsqrt hCsn hn2 D m hD hm hmn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm1 : (1 : ℝ) ≤ m := by
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hDl := (hdim D hD).1
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hm0 (by exact_mod_cast hmn)
  have hlogC : Real.log Cs ≤ Real.log (n : ℝ) := Real.log_le_log hCs0 hCsn
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlogC0 : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hlogs : (D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) ≤ 3*(Real.log (n : ℝ))^2 := by
    calc
      _ ≤ Real.log (n : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hDl (by linarith)
      _ ≤ Real.log (n : ℝ)*(3*Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.log_natCast_nonneg n)
      _ = _ := by ring
  rw [←Real.sqrt_eq_rpow] at hpoly
  have hs := sqrt_half_bound hm
  have hneg : Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2 < 0 := by linarith [Real.sqrt_nonneg (m : ℝ)]
  have he : (1+CR)*(Cs*(m : ℝ)^2)^D*Real.exp (-Real.sqrt (m : ℝ)/2) =
      Real.exp (Real.log (1+CR)+(D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))-
      Real.sqrt (m : ℝ)/2) := by
    have hp : (Cs*(m : ℝ)^2)^D =
        Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ))) := by
      rw [Real.exp_nat_mul,Real.exp_add,Real.exp_log hCs0]
      rw [show (2 : ℝ)*Real.log (m : ℝ)=Real.log ((m : ℝ)^2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (pow_pos hm0 2)]
    calc
      _ = Real.exp (Real.log (1+CR))*
          Real.exp ((D : ℝ)*(Real.log Cs+2*Real.log (m : ℝ)))*
          Real.exp (-Real.sqrt (m : ℝ)/2) := by rw [Real.exp_log hCR1,hp]
      _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr hneg




end SingleLatticeCovering.FinalRates

end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators



lemma pointBudget_pos {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    0 < pointBudget A s D := by
  dsimp [pointBudget]
  exact Nat.mul_pos (by omega) (Finset.prod_pos (fun j hj => by omega))

lemma alphabetPoints_card_le_budget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    {q D : ℕ} (hq : q ≤ D) : (alphabetPoints A s q).card ≤ pointBudget A s D := by
  classical
  have hp : ∏ j ∈ Finset.range q, (A j).card ≤
      ∏ j ∈ Finset.range D, ((A j).card+1) := by
    calc
      _ ≤ ∏ j ∈ Finset.range q, ((A j).card+1) := Finset.prod_le_prod (fun j hj => Nat.zero_le _) (fun j hj => Nat.le_succ _)
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hq) (fun j hj => Nat.zero_le _) (fun j hj _ => Nat.succ_pos _)
  dsimp [alphabetPoints,pointBudget]
  rw [Finset.card_product,Fintype.card_piFinset]
  have he : (∏ i : Fin q, (A i.val).card) = ∏ j ∈ Finset.range q, (A j).card :=
    Fin.prod_univ_eq_prod_range (fun j => (A j).card) q
  rw [he]
  exact le_trans (Nat.mul_le_mul_right s.card hp) (by simp [mul_comm])

lemma patternTotal_bound {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    patternTotal A s D ≤ (D+1)*(pointBudget A s D+1)^(2^D) :=
  allPatterns_total_bound A s D (pointBudget A s D) (fun _ hq => alphabetPoints_card_le_budget A s hq)

lemma log_pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    Real.log (pointBudget A s D : ℝ) = Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) := by
  simp only [pointBudget,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_prod]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_prod]
  intro j hj; positivity

lemma scalar_pattern_cost (D N Q : ℕ) (hN : 0 < N)
    (hQ : Q ≤ (D+1)*(N+1)^(2^D)) :
    (2 : ℝ)^D*Real.log (2*((Q : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hD : (0 : ℝ) < (D : ℝ)+1 := by positivity
  have hbase : (1 : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]) (one_le_pow₀ (by linarith))
  have hQr : (Q : ℝ) ≤ ((D : ℝ)+1)*((N : ℝ)+1)^(2^D) := by exact_mod_cast hQ
  have hl : Real.log (2*((Q : ℝ)+1)) ≤ Real.log 4+Real.log ((D : ℝ)+1)+
      (2^D : ℕ)*Real.log ((N : ℝ)+1) := by
    calc
      _ ≤ Real.log (4*(((D : ℝ)+1)*((N : ℝ)+1)^(2^D))) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul hD.ne' (by positivity),Real.log_pow]; ring
  have hNl : Real.log ((N : ℝ)+1) ≤ Real.log 2+Real.log (N : ℝ) := by
    rw [←Real.log_mul (by norm_num) hNp.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^D := one_le_pow₀ (by norm_num)
  have hDl : 0 ≤ Real.log ((D : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hNlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have h4log : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcast : ((2^D : ℕ) : ℝ)=(2 : ℝ)^D := by norm_cast
  rw [hcast] at hl
  have h24 : (2 : ℝ)^D*(2 : ℝ)^D=(4 : ℝ)^D := by rw [←mul_pow]; norm_num
  have h8 : Real.log 8=Real.log 4+Real.log 2 := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]; norm_num
  calc
    _ ≤ (2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1)+(2 : ℝ)^D*Real.log ((N : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ (2 : ℝ)^D*((2 : ℝ)^D*(Real.log 4+Real.log ((D : ℝ)+1))+
        (2 : ℝ)^D*(Real.log 2+Real.log (N : ℝ))) := by gcongr; nlinarith
    _ = _ := by rw [h8,←h24]; ring

lemma all_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
        ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := by
  have h := scalar_pattern_cost D (pointBudget A s D) (patternTotal A s D)
    (pointBudget_pos A s D) (patternTotal_bound A s D)
  rw [log_pointBudget] at h
  convert h using 1 ; ring


end SingleLatticeCovering.Shear

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators

lemma polynomial_pattern_cost {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α)
    (D : ℕ) {L CL CA : ℝ} (hL : 1 ≤ L) (hCL : 0 ≤ CL) (hCA : 0 ≤ CA)
    (hD : (D : ℝ) ≤ L)
    (hlabel : Real.log (s.card+1 : ℝ) ≤ CL*L^2)
    (halphabet : ∀ j < D, Real.log ((A j).card+1 : ℝ) ≤ CA*L^2) :
    (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤
      (4 : ℝ)^D*(Real.log 8+1+CL+CA)*L^3 := by
  have hs : ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (D : ℝ)*(CA*L^2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range D, CA*L^2 := Finset.sum_le_sum (fun j hj => halphabet j (Finset.mem_range.mp hj))
      _ = _ := by simp [nsmul_eq_mul]
  have hlogD : Real.log ((D : ℝ)+1) ≤ L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+1 by positivity)
    linarith
  have h12 : L ≤ L^2 := by nlinarith
  have h23 : L^2 ≤ L^3 := by nlinarith [sq_nonneg (L-1)]
  have h01 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hterm : Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ) ≤ (Real.log 8+1+CL+CA)*L^3 := by
    have hsd := mul_le_mul_of_nonneg_right hD (show 0 ≤ CA*L^2 by positivity)
    have hlab := mul_le_mul_of_nonneg_left h23 hCL
    have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^3 by nlinarith) h01
    nlinarith
  calc
    _ ≤ (4 : ℝ)^D*(Real.log 8+Real.log ((D : ℝ)+1)+Real.log (s.card+1 : ℝ)+
      ∑ j ∈ Finset.range D, Real.log ((A j).card+1 : ℝ)) := all_pattern_cost A s D
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hterm (show 0 ≤ (4 : ℝ)^D by positivity)]

lemma log_label_count {α : Type*} (s : Finset α) {D n : ℕ} {Cs : ℝ}
    (hn : 1 ≤ Real.log (n : ℝ)) (hCs : 1 ≤ Cs) (hD : (D : ℝ) ≤ Real.log (n : ℝ))
    (hs : (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D) :
    Real.log (s.card+1 : ℝ) ≤ (Real.log 2+Real.log Cs+2)*(Real.log (n : ℝ))^2 := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h; have h0 : n=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    subst n; norm_num at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hn0)))
  have hp : 0 < Cs*(n : ℝ)^2 := by positivity
  have hp1 : 1 ≤ (Cs*(n : ℝ)^2)^D := one_le_pow₀ (by nlinarith [sq_nonneg ((n : ℝ)-1)])
  have hl : Real.log (s.card+1 : ℝ) ≤ Real.log 2+(D : ℝ)*(Real.log Cs+2*Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.log (2*(Cs*(n : ℝ)^2)^D) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow,
        Real.log_mul (by positivity) (by positivity),Real.log_pow]; ring
  have hc : 0 ≤ Real.log Cs := Real.log_nonneg hCs
  have hl2 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ))^2 := by nlinarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ Real.log Cs+2*Real.log (n : ℝ) by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hl2 hc,
    mul_le_mul_of_nonneg_left (show 1 ≤ (Real.log (n : ℝ))^2 by nlinarith) h2]

lemma log_alphabet_bound {b D : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hD : (D : ℝ) ≤ L) (hb : (b : ℝ) ≤ L) :
    Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(b : ℝ)^2 ≤
      (Real.log 8+3)*L^2 := by
  have hlog : Real.log ((D : ℝ)+2) ≤ 2*L := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D+2 by positivity)
    linarith
  have hp := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D)
  have hD' := mul_le_mul_of_nonneg_right hD (show 0 ≤ 2*L by linarith)
  have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg b) hb 2
  have hc := mul_le_mul_of_nonneg_left (show 1 ≤ L^2 by nlinarith)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8))
  nlinarith



lemma eventually_pattern_cost {C Cs ε : ℝ} (hC : 0 < C) (hCs : 1 ≤ Cs) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) →
      ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
      (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
      (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
        Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2) →
      (2 : ℝ)^D*Real.log (2*((patternTotal A s D : ℝ)+1)) ≤ ε*(n : ℝ)*Real.log (n : ℝ) := by
  let H := Real.log 8+1+(Real.log 2+Real.log Cs+2)+(Real.log 8+3)
  have hH : 0 < H := by
    dsimp [H]
    linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8),
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  filter_upwards [FinalRates.eventually_dimension_small hC,
    FinalRates.eventually_dimension_power (C := C) (a := 4) (r := 1/2) hC (by norm_num) (by norm_num),
    FinalRates.eventually_firstSize_le_log (c := 1) (by norm_num),
    FinalRates.eventually_log_power_bound 3 (r := 1/2) (by norm_num) (div_pos hε hH),
    FinalRates.log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (1 : ℕ)]
    with n hdim hpow hb hlog hn hn1
  intro D hD α s A hs hA
  have hDL := (hdim D hD).1
  have hbL : (FinalRates.firstSize n : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hc := polynomial_pattern_cost A s D hn
    (show 0 ≤ Real.log 2+Real.log Cs+2 by linarith [Real.log_nonneg hCs,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
    (show 0 ≤ Real.log 8+3 by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]) hDL
    (log_label_count s hn hCs hDL hs)
    (fun j hj => (hA j hj).trans (log_alphabet_bound hn hDL hbL))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)=(n : ℝ) := by
    rw [←Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn1)]
    norm_num
  calc
    _ ≤ (4 : ℝ)^D*H*(Real.log (n : ℝ))^3 := hc
    _ ≤ (n : ℝ)^(1/2 : ℝ)*H*((ε/H)*(n : ℝ)^(1/2 : ℝ)) := by gcongr; exact hpow D hD
    _ = ε*(n : ℝ) := by calc
      _ = ε*((n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(1/2 : ℝ)) := by field_simp
      _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hε.le hn0) hn


end SingleLatticeCovering.Shear

end
end
end

section



noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Shear
open scoped BigOperators



lemma exp_error {n : ℕ} (hn : 2 ≤ n) {cost : ℝ}
    (hcost : cost ≤ (n : ℝ)*Real.log (n : ℝ)) :
    Real.exp (cost-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
      1/(n : ℝ)^(2*n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hemp : cost-(8*(n : ℝ)*Real.log (n : ℝ))/2 ≤ -((2*n : ℕ) : ℝ)*Real.log (n : ℝ) := by
    push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg n) hlog]
  apply (Real.exp_le_exp.mpr hemp).trans_eq
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hn0,one_div]




theorem final_conditions {C k csec Csec κ Cs CR : ℝ}
    (hC : 0 < C) (hk : 0 < k) (hcsec : 0 < csec) (hCsec : 0 ≤ Csec)
    (hκ : 0 < κ) (hCs : 1 ≤ Cs) (hCR : 0 ≤ CR) :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
        D ≤ n ∧ 2 ≤ n-D ∧
        Csec*(Cstar*(n : ℝ)*Real.log (n : ℝ))*Real.exp (-k*(firstSize n : ℝ)^(70/100 : ℝ)) ≤ eta (n-D) ∧
        8*(n : ℝ)*Real.log (n : ℝ)+(2 : ℝ)^D*Real.sqrt ((n-D : ℕ) : ℝ) ≤
          csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ)) ∧
        (1+CR)*(Cs*((n-D : ℕ) : ℝ)^2)^D*Real.exp (-Real.sqrt ((n-D : ℕ) : ℝ)/2)<1 ∧
        ∀ {α : Type*} (s : Finset α) (A : ℕ → Finset ℝ),
          (s.card : ℝ) ≤ (Cs*(n : ℝ)^2)^D →
          (∀ j < D, Real.log ((A j).card+1 : ℝ) ≤
            Real.log 8+(D : ℝ)*Real.log ((D : ℝ)+2)+(firstSize n : ℝ)^2) →
          let Lstar := 2*((patternTotal A s D : ℝ)+1)
          1 ≤ Lstar ∧ (patternTotal A s D : ℝ)<Lstar ∧
          Real.exp ((2 : ℝ)^D*Real.log Lstar-(8*(n : ℝ)*Real.log (n : ℝ))/2) ≤
            1/(n : ℝ)^(2*n) := by
  let Cstar : ℝ := 16/(csec*κ)
  have hstar : 0 < Cstar := div_pos (by norm_num) (mul_pos hcsec hκ)
  have hprod : csec*κ*Cstar=16 := by dsimp [Cstar]; field_simp
  refine ⟨Cstar,hstar,?_⟩
  filter_upwards [eventually_cap_eta (C := C) (H := Csec*Cstar) hC hk (mul_nonneg hCsec hstar.le),
    eventually_discard_bound (C := C) (ε := 8) hC (by norm_num),
    eventually_label_criterion hC hCs hCR,
    eventually_pattern_cost (C := C) (Cs := Cs) (ε := 1) hC hCs (by norm_num),
    eventually_dimension_small hC,eventually_ge_atTop (4 : ℕ)] with n hcap hdiscard hlabel hpat hdim hn
  refine ⟨by omega,?_⟩
  intro D hD
  have hDn := (hcap D hD).1
  have hm : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith [(hdim D hD).2]
  have hmn : n-D ≤ n := Nat.sub_le _ _
  have hmh : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨hDn,by exact_mod_cast hmh,?_,?_,?_,?_⟩
  · convert (hcap D hD).2 using 1 ; ring
  · have hh := hdiscard D (n-D) hD hmn
    have he : csec*κ*(Cstar*(n : ℝ)*Real.log (n : ℝ))=16*(n : ℝ)*Real.log (n : ℝ) := by
      calc
        _ = (csec*κ*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by ring
        _ = _ := by rw [hprod]
    rw [he]; linarith
  · exact hlabel D (n-D) hD hm hmn
  · intro α s A hs hA
    have hQ : 0 ≤ (patternTotal A s D : ℝ) := Nat.cast_nonneg _
    refine ⟨by linarith,by linarith,?_⟩
    exact exp_error (by omega) (by simpa using hpat D hD s A hs hA)


end SingleLatticeCovering.FinalRates

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Horizontal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Horizontal
open MeasureTheory Completion
open scoped ENNReal BigOperators



attribute [instance] FullLattice.discrete FullLattice.full


end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology


lemma sectionRadius_pos {C : ℝ} (hC : 0 < C) (n : ℕ) : 0 < sectionRadius C n := by
  dsimp [sectionRadius]; positivity

lemma radius_sq_bound {C b r : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hr : r ≤ C*(b*Real.log (b+1)+1)) : r ≤ ((C+1)*(b+1))^2 := by
  have hl : Real.log (b+1) ≤ b := by simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < b+1)
  have hinner : b*Real.log (b+1)+1 ≤ (b+1)^2 := by nlinarith [mul_le_mul_of_nonneg_left hl hb]
  calc
    r ≤ C*(b*Real.log (b+1)+1) := hr
    _ ≤ C*(b+1)^2 := mul_le_mul_of_nonneg_left hinner hC
    _ ≤ (C+1)^2*(b+1)^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (sq_nonneg _)
    _ = _ := by ring

lemma eventually_first_polynomial {H r ε : ℝ} (hH : 0 < H) (hr : 0 < r) (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, H*((firstSize n : ℝ)+1)^k ≤ ε*(n : ℝ)^r := by
  filter_upwards [eventually_firstSize_le_log (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_bound k hr (div_pos hε hH)] with n hfirst hlog
  simp only [one_mul] at hfirst
  calc
    _ ≤ H*(Real.log (n : ℝ))^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hfirst k) hH.le
    _ ≤ H*((ε/H)*(n : ℝ)^r) := mul_le_mul_of_nonneg_left hlog hH.le
    _ = _ := by field_simp




lemma eventually_marginal_scales {C α β γ C₀ : ℝ} (hC : 0 < C)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*((firstSize n : ℝ)+1) →
      D ≤ n ∧ 2 ≤ n-D ∧ (D : ℝ) ≤ (n : ℝ)^α ∧
      6*(D : ℝ)*sectionRadius C n < (n : ℝ)^β ∧
      C₀*(n : ℝ)^(-γ) ≤ 1/2 ∧
      sectionRadius C n^2/((n-D : ℕ) : ℝ)^2 ≤ 1 := by
  have _ := hC₀
  have herr : ∀ᶠ n : ℕ in atTop, C₀*(n : ℝ)^(-γ) ≤ 1/2 := by
    have ht : Tendsto (fun n : ℕ => C₀*(n : ℝ)^(-γ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop hγ).comp hn).const_mul C₀
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_first_polynomial hC hα (by norm_num : (0 : ℝ) < 1) 1,
    eventually_first_polynomial (show 0 < 6*C*(C+1) by positivity) hβ (by norm_num : (0 : ℝ) < 1/2) 2,
    eventually_first_polynomial (show 0 < C+1 by linarith) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/2) 1,
    eventually_dimension_small hC,herr,eventually_ge_atTop (4 : ℕ)] with n hDim hRad hSmall hDsmall he hn D hD
  simp only [pow_one,one_mul] at hDim
  simp only [pow_one,Real.rpow_one] at hSmall
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdhalf := (hDsmall D hD).2
  have hDn : D ≤ n := by exact_mod_cast (show (D : ℝ) ≤ n by linarith)
  have hmhalf : (n : ℝ)/2 ≤ ((n-D : ℕ) : ℝ) := by rw [Nat.cast_sub hDn]; linarith
  have hm2 : (2 : ℝ) ≤ ((n-D : ℕ) : ℝ) := by linarith
  refine ⟨hDn,by exact_mod_cast hm2,hD.trans hDim,?_,he,?_⟩
  · have hDR : 6*(D : ℝ)*sectionRadius C n ≤ 6*C*(C+1)*((firstSize n : ℝ)+1)^2 := by
      dsimp [sectionRadius]
      have hh := mul_le_mul_of_nonneg_right hD (show 0 ≤ 6*((C+1)*((firstSize n : ℝ)+1)) by positivity)
      nlinarith
    have hp : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hn0 β
    exact hDR.trans_lt (hRad.trans_lt (by nlinarith))
  · have hRm : sectionRadius C n ≤ ((n-D : ℕ) : ℝ) := by
      dsimp [sectionRadius]
      linarith
    apply (div_le_one (sq_pos_of_pos (by linarith : (0 : ℝ) < ((n-D : ℕ) : ℝ)))).mpr
    exact pow_le_pow_left₀ (sectionRadius_pos hC n).le hRm 2


end SingleLatticeCovering.FinalRates

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal

lemma body_volume_pos {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < (volume K).toReal := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) hK.measure_ne_top
  exact (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma affine_body {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let he : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image he.continuous, hc.affine_image e.toAffineMap,?_⟩
  change (interior (he '' K)).Nonempty
  rw [←he.image_interior]
  exact hi.image he

lemma chain_first_le_dim {B : Block} (c : Chain B) : c.first.b ≤ c.dim := by
  induction c with
  | base B => rfl
  | append c B w ih => exact ih.trans (Nat.le_add_right _ _)


end SingleLatticeCovering.Assembly

end
end

section

noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise
namespace SingleLatticeCovering.FiniteDimensions




theorem maximal_basis {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (h0 : (0 : Fin n → ℝ) ∈ interior K) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ),
      (∀ j, b j ∈ K) ∧ ∀ x ∈ K, ∀ j, |b.repr x j| ≤ 1 := by
  classical
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let v₀ : Fin n → (Fin n → ℝ) := fun j => (r/2) • Pi.single j (1 : ℝ)
  have hv₀ : ∀ j, v₀ j ∈ K := by
    intro j
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    simp only [v₀,norm_smul,Pi.norm_single,Real.norm_eq_abs,abs_one,mul_one,
      abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hdet₀ : (Matrix.of v₀).det = (r/2)^n := by
    have he : Matrix.of v₀ = (r/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [v₀,Pi.single_apply,Matrix.one_apply,Pi.smul_apply,eq_comm]
    rw [he,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]
  have hS : IsCompact {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  have hcont : Continuous (fun v : Fin n → (Fin n → ℝ) => |(Matrix.of v).det|) := by
    fun_prop
  obtain ⟨v,hv,hmax⟩ := hS.exists_isMaxOn ⟨v₀,hv₀⟩ hcont.continuousOn
  have hdet : (Matrix.of v).det ≠ 0 := by
    have h : |(Matrix.of v₀).det| ≤ |(Matrix.of v).det| := hmax hv₀
    rw [hdet₀,abs_of_pos (pow_pos (by positivity : 0 < r/2) _)] at h
    intro hz
    rw [hz,abs_zero] at h
    exact (not_le_of_gt (pow_pos (by positivity : 0 < r/2) _)) h
  let b := basisOfLinearIndependentOfCardEqFinrank' v
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet) (by simp)
  have hb : (b : Fin n → (Fin n → ℝ)) = v := by
    simp [b]
  refine ⟨b,?_,?_⟩
  · intro j
    rw [show b j=v j from congrFun hb j]
    exact hv j
  · intro x hx j
    have hupdate : (Function.update v j x) ∈ {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} := by
      intro k
      by_cases hk : k=j
      · subst k; simpa using hx
      · simpa [hk] using hv k
    have hbound := hmax hupdate
    have hd : (Matrix.of (Function.update v j x)).det = b.repr x j*(Matrix.of v).det := by
      have hs := b.sum_repr x
      have ht := Matrix.det_updateRow_sum (Matrix.of b) j (fun k => b.repr x k)
      change (Matrix.of (Function.update (fun k => b k) j (∑ k, b.repr x k • b k))).det =
        b.repr x j*(Matrix.of b).det at ht
      rw [hs,hb] at ht
      exact ht
    change |(Matrix.of (Function.update v j x)).det| ≤ |(Matrix.of v).det| at hbound
    rw [hd,abs_mul] at hbound
    exact (mul_le_mul_iff_left₀ (abs_pos.mpr hdet)).mp (by simpa [mul_comm] using hbound)


end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise

lemma convex_basis_cube {n : ℕ} (hn : 0 < n) (K : Set (Fin n → ℝ))
    (hconv : Convex ℝ K) (h0 : (0 : Fin n → ℝ) ∈ K)
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (hb : ∀ j, b j ∈ K) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ b.equivFun.symm ⁻¹' K := by
  intro x hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j, x j ≤ 1 := calc
    ∑ j, x j ≤ ∑ _j : Fin n, 1/(n : ℝ) := Finset.sum_le_sum (fun j _ => hx.2 j)
    _ = 1 := by simp [hnr.ne']
  let w : Fin (n+1) → ℝ := Fin.cons (1-∑ j, x j) x
  let z : Fin (n+1) → (Fin n → ℝ) := Fin.cons 0 b
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), 0 ≤ w j := by
    intro j _
    refine Fin.cases ?_ (fun i => ?_) j
    · exact sub_nonneg.mpr hsum
    · exact hx.1 i
  have hw1 : ∑ j, w j = 1 := by simp [w,Fin.sum_univ_succ]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), z j ∈ K := by
    intro j _
    exact Fin.cases h0 hb j
  have hc := hconv.sum_mem hw hw1 hz
  change b.equivFun.symm x ∈ K
  rw [Basis.equivFun_symm_apply]
  simpa only [Fin.sum_univ_succ,w,z,Fin.cons_zero,Fin.cons_succ,smul_zero,zero_add] using hc

lemma integer_cube_cover {n : ℕ} (hn : 0 < n) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ))+
      (contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') : Set (Fin n → ℝ)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let l : Fin n → ℝ := fun j => (⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)
  let q : Fin n → ℝ := fun j => Int.fract ((n : ℝ)*x j)/(n : ℝ)
  have hl : l ∈ contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') := by
    rw [mem_contractLattice]
    convert integer_mem n (fun j => ⌊(n : ℝ)*x j⌋) using 1
    ext j
    simp only [Pi.smul_apply,smul_eq_mul,l]
    field_simp
  refine ⟨q,⟨?_,?_⟩,l,hl,?_⟩
  · intro j
    exact div_nonneg (Int.fract_nonneg _) hnr.le
  · intro j
    exact (div_le_div_iff_of_pos_right hnr).mpr (Int.fract_lt_one _).le
  · ext j
    change Int.fract ((n : ℝ)*x j)/(n : ℝ)+(⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)=x j
    rw [←add_div,Int.fract_add_floor]
    exact mul_div_cancel_left₀ _ hnr.ne'



end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise



theorem finite_dimension_cover {n : ℕ} (hn : 0 < n)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
      IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=univ ∧
      (volume K).toReal / ZLattice.covolume L ≤ (2*(n : ℝ))^n := by
  classical
  obtain ⟨x₀,hx₀⟩ := hinterior
  let t := Homeomorph.addRight x₀
  let K₀ := t ⁻¹' K
  have hK₀ : IsCompact K₀ := t.isCompact_preimage.mpr hK
  have h0 : (0 : Fin n → ℝ) ∈ interior K₀ := by
    rw [←t.preimage_interior]
    change 0+x₀ ∈ interior K
    simpa using hx₀
  have hconv₀ : Convex ℝ K₀ := by
    intro x hx y hy a b ha hb hab
    have hh := hconv hx hy ha hb hab
    change a • (x+x₀)+b • (y+x₀) ∈ K at hh
    change a • x+b • y+x₀ ∈ K
    have he : a • (x+x₀)+b • (y+x₀) = a • x+b • y+x₀ := by
      calc
        _ = (a • x+b • y)+(a+b) • x₀ := by module
        _ = _ := by rw [hab,one_smul]
    rwa [he] at hh
  obtain ⟨b,hb,hbound⟩ := maximal_basis K₀ hK₀ h0
  let e := b.equivFun.symm
  let K' := e ⁻¹' K₀
  have hsmall : Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ K' :=
    convex_basis_cube hn K₀ hconv₀ (interior_subset h0) b hb
  have hlarge : K' ⊆ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := by
    intro x hx
    have hb' := hbound (e x) hx
    have hj (j : Fin n) : |x j| ≤ 1 := by
      have hh : |b.equivFun (e x) j| ≤ 1 := hb' j
      simpa only [e,LinearEquiv.apply_symm_apply] using hh
    exact ⟨fun j => (abs_le.mp (hj j)).1,fun j => (abs_le.mp (hj j)).2⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let L₀ := contractLattice (integerLattice n) (n : ℝ) hnr.ne'
  have hcover : K'+(L₀ : Set (Fin n → ℝ))=univ := by
    apply Set.eq_univ_of_univ_subset
    rw [←integer_cube_cover hn]
    exact Set.add_subset_add_right hsmall
  have hvolume : (volume K').toReal ≤ (2 : ℝ)^n := by
    have hh := ENNReal.toReal_mono (isCompact_Icc.measure_ne_top (μ := volume)) (measure_mono hlarge)
    rw [Real.volume_Icc_pi_toReal (by intro j; norm_num)] at hh
    norm_num at hh
    exact hh
  have hcov : ZLattice.covolume L₀ = (n : ℝ)⁻¹^n := by
    rw [contractLattice_covolume _ _ hnr,integerLattice_covolume,mul_one]
  have hdens : (volume K').toReal / ZLattice.covolume L₀ ≤ (2*(n : ℝ))^n := by
    rw [hcov,inv_pow,div_inv_eq_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right hvolume (pow_nonneg hnr.le _)
  have himage : (fun x => e x+x₀) '' K'=K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm (x-x₀),?_,?_⟩
      · change e (e.symm (x-x₀))+x₀ ∈ K
        simpa using hx
      · simp
  refine ⟨image L₀ e,inferInstance,inferInstance,?_,?_⟩
  · rw [←himage]
    exact affine_image_cover L₀ e x₀ K' hcover
  · rw [←himage,affine_image_density]
    exact hdens


end SingleLatticeCovering.FiniteDimensions


end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise

namespace SingleLatticeCovering.FiniteDimensions
open Filter MeasureTheory
open scoped Pointwise BigOperators




lemma absorb_finitely_many_dimensions
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨C,hC⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  let f : ℕ → ℝ := fun n => (2*(n : ℝ))^n / ((n : ℝ)*Real.log (n : ℝ))
  have hf : ∀ n, 0 ≤ f n := fun n => div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  let S := ∑ n ∈ Finset.range N, f n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => hf n)
  refine ⟨1+|C|+S,by positivity,?_⟩
  intro n hn K hK hc hi
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  by_cases hlarge : N ≤ n
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := hN n hlarge K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    gcongr
    exact le_trans (le_abs_self C) (by linarith)
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := finite_dimension_cover (by omega) K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hfS : f n ≤ S := Finset.single_le_sum (fun i _ => hf i) hnN
    have hff : f n ≤ 1+|C|+S := hfS.trans (by linarith [abs_nonneg C])
    rw [mul_assoc]
    exact (div_le_iff₀ (mul_pos hnr hlog)).mp hff


end SingleLatticeCovering.FiniteDimensions

end
end

section



noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

lemma volume_pos {n : ℕ} {K : Set (E n)} (hi : (interior K).Nonempty) : 0 < volume K :=
  (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma uniform_probability {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) : IsProbabilityMeasure (uniformLaw K) :=
  cond_isProbabilityMeasure_of_finite (ne_of_gt (volume_pos hi)) hK.measure_ne_top

lemma continuous_memLp_uniform {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : E n → F} (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (uniformLaw K) := by
  let := uniform_probability hK hi
  obtain ⟨C,hC⟩ := (hK.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  apply ae_smul_measure (c := (volume K)⁻¹)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem _ hx)

lemma continuous_eq_on_interior {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[uniformLaw K] g) : EqOn f g (interior K) := by
  have h' : f =ᵐ[volume.restrict K] g :=
    (ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hK.measure_ne_top)).mp h
  exact Measure.eqOn_open_of_ae_eq (μ := volume)
    (ae_restrict_of_ae_restrict_of_subset interior_subset h') isOpen_interior
    hf.continuousOn hg.continuousOn



lemma inner_not_constant_on_interior {n : ℕ} {K : Set (E n)}
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) (c : ℝ) :
    ¬EqOn (fun x => ⟪v,x⟫) (fun _ => c) (interior K) := by
  intro h
  obtain ⟨z,hz⟩ := hi
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let t := r/(2*(‖v‖+1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist (z+t • v) z < r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖v‖+1))).mpr
    nlinarith [norm_nonneg v]
  have hz' := h (hball hdist)
  have hz0 := h hz
  simp only [inner_add_right,real_inner_smul_right] at hz'
  have hself : 0 < ⟪v,v⟫ := real_inner_self_pos.mpr hv
  nlinarith



lemma covariance_positive {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) :
    0 < covarianceBilin (uniformLaw K) v v := by
  let := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hf : MemLp (fun x : E n => ⟪v,x⟫) 2 (uniformLaw K) :=
    continuous_memLp_uniform hK hi (by fun_prop) 2
  rw [covarianceBilin_self hμ]
  refine lt_of_le_of_ne (variance_nonneg _ _) ?_
  intro hzero
  have heq := ae_eq_integral_of_variance_eq_zero hf hzero.symm
  exact inner_not_constant_on_interior hi hv _
    (continuous_eq_on_interior hK (by fun_prop) continuous_const heq)





lemma positive_form_normalization {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hs : ∀ x y, B x y=B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ T : E n ≃L[ℝ] E n, ∀ x y, B (T x) (T y)=⟪x,y⟫ := by
  classical
  let Q := B.toBilinForm.toQuadraticMap
  obtain ⟨w,hw,⟨e⟩⟩ : ∃ w : Fin n → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      Q.Equivalent (QuadraticMap.weightedSumSquares ℝ w) := by
    have hdim : Module.finrank ℝ (E n)=n := finrank_euclideanSpace_fin
    have hh := QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q
    rw [hdim] at hh
    exact hh
  have hw1 : ∀ i, w i=1 := by
    intro i
    have hz : e.symm (Pi.single i (1 : ℝ)) ≠ 0 := by
      intro h
      have hh := congrArg e h
      have : (Pi.single i (1 : ℝ) : Fin n → ℝ)=0 := by simp at hh
      have := congrFun this i
      simp at this
    have he := e.symm.map_app (Pi.single i (1 : ℝ))
    have hwp : 0 < w i := by
      have hq : 0 < Q (e.symm (Pi.single i (1 : ℝ))) := hp _ hz
      rw [he] at hq
      simpa [QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using hq
    rcases hw i with h | h | h
    · linarith
    · linarith
    · exact h
  let T : E n ≃L[ℝ] E n :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans e.symm.toLinearEquiv).toContinuousLinearEquiv
  have hdiag : ∀ x : E n, B (T x) (T x)=⟪x,x⟫ := by
    intro x
    have he := e.symm.map_app (WithLp.ofLp x)
    change B (T x) (T x)=_ at he
    rw [he]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [QuadraticMap.weightedSumSquares_apply,hw1,one_smul,star_trivial]
    rfl
  refine ⟨T,fun x y => ?_⟩
  have h := hdiag (x+y)
  simp only [map_add,_root_.add_apply,inner_add_left,inner_add_right] at h
  rw [hdiag x,hdiag y,hs (T y) (T x),real_inner_comm x y] at h
  linarith




lemma adjointEquiv_adjoint {n : ℕ} (T : E n ≃L[ℝ] E n) :
    (adjointEquiv T).toContinuousLinearMap.adjoint=T.toContinuousLinearMap :=
  ContinuousLinearMap.adjoint_adjoint _

end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




lemma map_centeredEquiv {n : ℕ} (μ : Measure (E n)) (A : E n ≃L[ℝ] E n) :
    μ.map (centeredEquiv μ A)=(μ.map (fun x => -(∫ x, x ∂μ)+x)).map A := by
  rw [Measure.map_map A.continuous.measurable (by fun_prop)]
  rfl

lemma memLp_translate {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (c : E n) : MemLp id 2 (μ.map (fun x => c+x)) := by
  have hc : MemLp (fun _ : E n => c) 2 μ := memLp_const c
  have hsum : MemLp (fun x : E n => c+x) 2 μ := hc.add hμ
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr hsum

lemma memLp_centered {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : MemLp id 2 (μ.map (fun x => -(∫ x, x ∂μ)+x)) :=
  memLp_translate hμ _

lemma centeredEquiv_mean {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) :
    (∫ x, x ∂μ.map (centeredEquiv μ A))=0 := by
  have hcent := memLp_centered hμ
  rw [map_centeredEquiv]
  change (∫ x, x ∂(μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap)=0
  rw [A.toContinuousLinearMap.integral_id_map (hcent.integrable (by simp)),
    integral_map (by fun_prop) (by fun_prop)]
  change A (∫ x, -(∫ z, z ∂μ)+x ∂μ)=0
  rw [integral_add (f := fun _ : E n => -(∫ z, z ∂μ)) (g := fun x : E n => x)
    (integrable_const _) (hμ.integrable (by simp))]
  simp

lemma centeredEquiv_covariance {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) (u v : E n) :
    covarianceBilin (μ.map (centeredEquiv μ A)) u v=
      covarianceBilin μ (A.toContinuousLinearMap.adjoint u) (A.toContinuousLinearMap.adjoint v) := by
  rw [map_centeredEquiv]
  change covarianceBilin ((μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap) u v=_
  rw [covarianceBilin_map (memLp_centered hμ) A.toContinuousLinearMap]
  rw [covarianceBilin_map_const_add]



theorem uniform_affine_isotropization {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂(uniformLaw K).map e)=0 ∧
      ∀ u v : E n, covarianceBilin ((uniformLaw K).map e) u v=⟪u,v⟫ := by
  let : IsProbabilityMeasure (uniformLaw K) := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hs : ∀ x y : E n, covarianceBilin (uniformLaw K) x y=
      covarianceBilin (uniformLaw K) y x := fun x y => covarianceBilin_comm x y
  have hp : ∀ x : E n, x ≠ 0 → 0 < covarianceBilin (uniformLaw K) x x :=
    fun x hx => covariance_positive hK hi hx
  obtain ⟨T,hT⟩ := positive_form_normalization (covarianceBilin (uniformLaw K)) hs hp
  refine ⟨centeredEquiv (uniformLaw K) (adjointEquiv T),centeredEquiv_mean hμ _,?_⟩
  intro u v
  rw [centeredEquiv_covariance hμ,adjointEquiv_adjoint]
  exact hT u v



end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




lemma affine_map_volume {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    volume.map e=ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| • volume := by
  have he : (e : E n → E n)=(fun x => x+e 0) ∘ (e.linear.toLinearMap : E n → E n) := by
    funext x
    simpa using e.map_vadd (0 : E n) x
  rw [he,←Measure.map_map (by fun_prop) e.linear.toLinearMap.continuous_of_finiteDimensional.measurable]
  rw [map_linearMap_addHaar_eq_smul_addHaar volume e.linear.isUnit_det'.ne_zero,
    Measure.map_smul,map_add_right_eq_self]

lemma affine_volume_factor_pos {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    0 < ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| := by
  apply ENNReal.ofReal_pos.mpr
  exact abs_pos.mpr (inv_ne_zero e.linear.isUnit_det'.ne_zero)



lemma map_uniformLaw {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) (K : Set (E n)) :
    (uniformLaw K).map e=uniformLaw (e '' K) := by
  let em := affineMeasurableEquiv e
  let c := ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹|
  have hc : c ≠ 0 := ne_of_gt (affine_volume_factor_pos e)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : volume.map em=c • volume := affine_map_volume e
  have hpre : em ⁻¹' (e '' K)=K := by
    change e ⁻¹' (e '' K)=K
    exact Set.preimage_image_eq _ e.injective
  have hval : volume K=c*volume (e '' K) := by
    have h := congrArg (fun μ : Measure (E n) => μ (e '' K)) hmap
    rw [em.map_apply,hpre] at h
    exact h
  have hrestr : (volume.restrict K).map em=c • volume.restrict (e '' K) := by
    have h := em.restrict_map volume (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at h
    exact h.symm
  change ((volume K)⁻¹ • volume.restrict K).map em= _
  rw [Measure.map_smul,hrestr,smul_smul]
  unfold uniformLaw
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(volume (e '' K))⁻¹*c=(c⁻¹*c)*(volume (e '' K))⁻¹ := by ac_rfl
    _ = (volume (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]



theorem isotropic_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂uniformLaw (e '' K))=0 ∧
      ∀ u v : E n, covarianceBilin (uniformLaw (e '' K)) u v=⟪u,v⟫ := by
  obtain ⟨e,hmean,hcov⟩ := uniform_affine_isotropization hK hi
  rw [map_uniformLaw] at hmean hcov
  exact ⟨e,hmean,hcov⟩






lemma uniformPdf_measurable {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K) :
    Measurable (uniformPdf K) := measurable_const.indicator hK

lemma uniformPdf_nonneg {n : ℕ} (K : Set (E n)) (x : E n) : 0 ≤ uniformPdf K x := by
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x

lemma uniformPdf_logConcave {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) : LogConcave (uniformPdf K) := by
  have hvol : volume K ≠ 0 := ne_of_gt (volume_pos hi)
  have hC : 0 < ((volume K)⁻¹).toReal := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr hK.measure_ne_top) (ENNReal.inv_ne_top.mpr hvol)
  refine ⟨uniformPdf_nonneg K,fun x y a b ha hb hab => ?_⟩
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hc hx hy (le_of_lt ha) (le_of_lt hb) hab
      simp only [uniformPdf,Set.indicator_of_mem hx,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
      rw [←Real.rpow_add hC,hab,Real.rpow_one]
    · simp only [uniformPdf,Set.indicator_of_notMem hy,Real.zero_rpow (ne_of_gt hb),mul_zero]
      exact uniformPdf_nonneg K _
  · simp only [uniformPdf,Set.indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact uniformPdf_nonneg K _

lemma uniformLaw_eq_withDensity {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K)
    (hi : (interior K).Nonempty) :
    uniformLaw K=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf K x)) := by
  have hct : (volume K)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ne_of_gt (volume_pos hi))
  have he : (fun x => ENNReal.ofReal (uniformPdf K x))=
      K.indicator (fun _ => (volume K)⁻¹) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [uniformPdf,Set.indicator_of_mem hx]
      exact ENNReal.ofReal_toReal hct
    · simp [uniformPdf,hx]
  rw [he,withDensity_indicator hK,withDensity_const]
  rfl



lemma covariance_isotropy {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hmean : (∫ x, x ∂μ)=0)
    (hcov : ∀ u v : E n, covarianceBilin μ u v=⟪u,v⟫) : IsIsotropic μ := by
  refine ⟨hmean,fun u v => ?_⟩
  have h := hcov u v
  rw [covarianceBilin_apply hμ] at h
  simp only [id_eq] at h
  rw [hmean] at h
  simpa using h




end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

lemma affine_body_properties {n : ℕ} (e : E n ≃ᵃ[ℝ] E n)
    {K : Set (E n)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H : E n ≃ₜ E n :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image H.continuous,hc.affine_image e.toAffineMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H




theorem isotropic_logConcave_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty ∧
      IsProbabilityMeasure (uniformLaw (e '' K)) ∧ MemLp id 2 (uniformLaw (e '' K)) ∧
      IsIsotropic (uniformLaw (e '' K)) ∧
      Measurable (uniformPdf (e '' K)) ∧ LogConcave (uniformPdf (e '' K)) ∧
      uniformLaw (e '' K)=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf (e '' K) x)) := by
  obtain ⟨e,hmean,hcov⟩ := isotropic_affine_body hK hi
  obtain ⟨hK',hc',hi'⟩ := affine_body_properties e hK hc hi
  have hprob := uniform_probability hK' hi'
  let := hprob
  have hmem : MemLp id 2 (uniformLaw (e '' K)) :=
    continuous_memLp_uniform hK' hi' continuous_id 2
  exact ⟨e,hK',hc',hi',hprob,hmem,covariance_isotropy hmem hmean hcov,
    uniformPdf_measurable hK'.measurableSet,uniformPdf_logConcave hK' hc' hi',
    uniformLaw_eq_withDensity hK'.measurableSet hi'⟩



end SingleLatticeCovering.Isotropization

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



lemma map_snd_restrict {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd ((μ.prod ν).restrict K)=ν.withDensity (fun y => μ (fiber K y)) := by
  ext U hU
  rw [Measure.map_apply measurable_snd hU,Measure.restrict_apply (measurable_snd hU),
    Measure.prod_apply_symm ((measurable_snd hU).inter hK),withDensity_apply _ hU,
    ←lintegral_indicator hU]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
    congr 1
    ext x
    simp [fiber,hy]
  · simp only [Set.indicator_of_notMem hy]
    have he : (fun x : E => (x,y)) ⁻¹' (Prod.snd ⁻¹' U ∩ K)=∅ := by ext x; simp [hy]
    rw [he,measure_empty]

lemma measurable_fiber_measure {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ]
    {K : Set (E × F)} (hK : MeasurableSet K) : Measurable (fun y => μ (fiber K y)) :=
  measurable_measure_prodMk_right hK




lemma map_snd_uniform (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=
      ν.withDensity (fun y => ((μ.prod ν) K)⁻¹*μ (fiber K y)) := by
  rw [Measure.map_smul,map_snd_restrict μ ν hK]
  exact (withDensity_smul _ (measurable_fiber_measure μ hK)).symm




end SingleLatticeCovering.Sections

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SharpYoung

lemma densityCDF_transport (f g : PositiveDensity) (x : ℝ) :
    densityCDF g (densityTransport f g x) = densityCDF f x := by
  change ((densityCDFIso g) ((densityCDFIso g).symm (densityCDFIso f x)) : ℝ) = _
  simp

lemma densityTransport_hasDerivAt (f g : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityTransport f g) (f x / g (densityTransport f g x)) x := by
  apply HasDerivAt.of_comp_left (densityTransport f g).continuous.continuousAt
    (densityCDF_hasDerivAt g _) (densityCDF_hasDerivAt f x) (ne_of_gt (g.positive _))
  exact Filter.Eventually.of_forall (densityCDF_transport f g)



end SingleLatticeCovering.SharpYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

noncomputable section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace ComplexConjugate

lemma normalizer_pos (k : ℕ) {b : ℝ} (hb : 0 < b) : 0 < normalizer k b := by
  unfold normalizer
  positivity
lemma density_pos {k : ℕ} {b : ℝ} (hb : 0 < b) (y : E k) : 0 < density b y := by
  unfold density
  exact mul_pos (inv_pos.mpr (normalizer_pos k hb)) (Real.exp_pos _)
lemma continuous_density (k : ℕ) (b : ℝ) : Continuous (density (k := k) b) := by
  unfold density
  fun_prop
lemma integrable_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : E k => Real.exp (-b*‖y‖^2)) volume := by
  have H := integrable_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb 0 (0:E k)
  have H' := H.re
  simpa only [zero_mul,add_zero,←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_neg,
    RCLike.re_to_complex, Complex.exp_ofReal_re] using H'
lemma integral_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    (∫ y : E k, Real.exp (-b*‖y‖^2))=normalizer k b := by
  simpa only [normalizer,finrank_euclideanSpace_fin] using integral_rexp_neg_mul_sq_norm (V := E k) hb
lemma integrable_density {k : ℕ} {b : ℝ} (hb : 0 < b) : Integrable (density (k := k) b) volume :=
  (integrable_kernel hb).const_mul _
lemma integral_density {k : ℕ} {b : ℝ} (hb : 0 < b) : (∫ y : E k, density b y)=1 := by
  unfold density
  rw [integral_const_mul,integral_kernel hb,inv_mul_cancel₀ (ne_of_gt (normalizer_pos k hb))]


end SingleLatticeCovering.GaussianDensity





open MeasureTheory Filter Set
open scoped Topology
noncomputable section



namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung
open scoped ENNReal

lemma weighted_transport_inequality {u v a b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    u ≤ (a+b*(u/v))*(u^a*v^b) := by
  have hgm : (u/v)^b ≤ a+b*(u/v) := by
    simpa only [Real.one_rpow,one_mul,mul_one] using
      Real.geom_mean_le_arith_mean2_weighted ha hb (show (0:ℝ) ≤ 1 by norm_num)
        (div_pos hu hv).le hab
  have he : (u/v)^b*(u^a*v^b)=u := by
    rw [Real.div_rpow hu.le hv.le]
    have hpow : v^b ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
    calc
      u^b/v^b*(u^a*v^b) = u^a*u^b := by field_simp
      _ = u^(a+b) := (Real.rpow_add hu _ _).symm
      _ = u := by rw [hab,Real.rpow_one]
  calc
    u = (u/v)^b*(u^a*v^b) := he.symm
    _ ≤ (a+b*(u/v))*(u^a*v^b) := mul_le_mul_of_nonneg_right hgm (by positivity)




theorem positive_probability_lintegral (f g : PositiveDensity) {h : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hh : ∀ x y, f x ^ a * g y ^ b ≤ h (a*x+b*y)) :
    1 ≤ ∫⁻ z, ENNReal.ofReal (h z) := by
  let T : ℝ → ℝ := densityTransport f g
  let W : ℝ → ℝ := fun x => a*x+b*T x
  let W' : ℝ → ℝ := fun x => a+b*(f x/g (T x))
  have hT : StrictMono T := (densityTransport f g).strictMono
  have hW : StrictMono W := by
    intro x y hxy
    exact add_lt_add (mul_lt_mul_of_pos_left hxy ha)
      (mul_lt_mul_of_pos_left (hT hxy) hb)
  have hd (x : ℝ) : HasDerivAt W (W' x) x := by
    simpa only [W,W',T,id_eq,Pi.add_def,mul_one] using
      ((hasDerivAt_id x).const_mul a).add ((densityTransport_hasDerivAt f g x).const_mul b)
  have hp (x : ℝ) : 0 < W' x := by
    dsimp [W']; exact add_pos ha (mul_pos hb (div_pos (f.positive x) (g.positive _)))
  have hi : (∫⁻ x, ENNReal.ofReal (f x))=1 := by
    rw [←ofReal_integral_eq_lintegral_ofReal f.integrable
      (Filter.Eventually.of_forall fun x => (f.positive x).le),f.integral_one]
    norm_num
  calc
    1 = ∫⁻ x, ENNReal.ofReal (f x) := hi.symm
    _ ≤ ∫⁻ x, ENNReal.ofReal |W' x| *ENNReal.ofReal (h (W x)) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (f x) ≤ ENNReal.ofReal |W' x| * ENNReal.ofReal (h (W x))
      rw [abs_of_pos (hp x),←ENNReal.ofReal_mul (hp x).le]
      apply ENNReal.ofReal_le_ofReal
      exact (weighted_transport_inequality (f.positive x) (g.positive (T x)) ha.le hb.le hab).trans
        (mul_le_mul_of_nonneg_left (hh x (T x)) (hp x).le)
    _ = ∫⁻ z in W '' univ, ENNReal.ofReal (h z) := by
      symm
      simpa using lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun x _ => (hd x).hasDerivWithinAt) hW.injective.injOn (fun z => ENNReal.ofReal (h z))
    _ ≤ ∫⁻ z, ENNReal.ofReal (h z) :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung SingleLatticeCovering.SimplexYoung
open scoped ENNReal



theorem positive_integral {f g h : ℝ → ℝ}
    (fc : Continuous f) (gc : Continuous g) (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x)
    (fi : Integrable f volume) (gi : Integrable g volume) (hi : Integrable h volume)
    (hn : ∀ x, 0 ≤ h x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a*x+b*y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  let F := normalizePositiveDensity f fc fp fi
  let G := normalizePositiveDensity g gc gp gi
  let M := (∫ x, f x)^a*(∫ y, g y)^b
  have hfpos := integral_pos_of_continuous_density fp fi
  have hgpos := integral_pos_of_continuous_density gp gi
  have hM : 0 < M := mul_pos (Real.rpow_pos_of_pos hfpos _) (Real.rpow_pos_of_pos hgpos _)
  have hh : ∀ x y, F x^a*G y^b ≤ (h (a*x+b*y))/M := by
    intro x y
    dsimp [F,G,normalizePositiveDensity,M]
    rw [Real.div_rpow (fp x).le hfpos.le,Real.div_rpow (gp y).le hgpos.le,
      div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hfg x y) hM.le
  have hineq := positive_probability_lintegral F G (h := fun z => h z/M) ha hb hab hh
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.div_const M)
    (Filter.Eventually.of_forall (fun z => div_nonneg (hn z) hM.le)),integral_div] at hineq
  have ht : (1:ℝ) ≤ (∫ z, h z)/M := by
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (integral_nonneg hn) hM.le)).mp (by simpa using hineq)
  have := (le_div_iff₀ hM).mp ht
  simpa only [one_mul] using this


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma gaussianKernel_prod (d : ℕ) (c : ℝ) (x : RV d) :
    gaussianKernel d c x = ∏ i, Real.exp (-c*(x i)^2) := by
  rw [gaussianKernel,Finset.mul_sum,Real.exp_sum]

lemma gaussianKernel_le_one (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (x : RV d) :
    gaussianKernel d c x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma integrable_gaussianKernel (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianKernel d c) volume := by
  have H : Integrable (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) volume :=
    Integrable.fintype_prod (fun _ : Fin d => integrable_exp_neg_mul_sq hc)
  have he : gaussianKernel d c = (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) :=
    funext (gaussianKernel_prod d c)
  rw [he]
  exact H

lemma gaussianKernel_cons (d : ℕ) (c t : ℝ) (y : RV d) :
    gaussianKernel (d+1) c (Fin.cons t y)=Real.exp (-c*t^2)*gaussianKernel d c y := by
  simp only [gaussianKernel,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_add,Real.exp_add]



lemma GaussianBound.integrable {d : ℕ} {f : RV d → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Integrable f volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_gaussianKernel d hc').const_mul A).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma gaussian_slice_dominant {d : ℕ} {f : RV (d+1) → ℝ} {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hbound : ∀ x, |f x| ≤ A*gaussianKernel (d+1) c x)
    (y : RV d) (t : ℝ) : |f (Fin.cons t y)| ≤ A*Real.exp (-c*t^2) := by
  calc
    _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hbound _
    _ = (A*Real.exp (-c*t^2))*gaussianKernel d c y := by rw [gaussianKernel_cons,mul_assoc]
    _ ≤ A*Real.exp (-c*t^2) := mul_le_of_le_one_right (by positivity) (gaussianKernel_le_one d hc y)

lemma GaussianBound.integrable_slice {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (y : RV d) :
    Integrable (fun t : ℝ => f (Fin.cons t y)) volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_exp_neg_mul_sq hc').const_mul A).mono'
    (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)

lemma GaussianBound.continuous_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Continuous (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply continuous_of_dominated
      (bound := fun t : ℝ => A*Real.exp (-c*t^2))
  · intro y
    exact (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)
  · exact (integrable_exp_neg_mul_sq hc').const_mul A
  · exact Filter.Eventually.of_forall (fun t => hc.comp (continuous_const.finCons continuous_id))

lemma marginalOne_positive {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (hp : ∀ x, 0 < f x) (y : RV d) :
    0 < marginalOne f y :=
  SingleLatticeCovering.SimplexYoung.integral_pos_of_continuous_density
    (fun t => hp (Fin.cons t y)) (hf.integrable_slice hc y)

lemma GaussianBound.for_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : GaussianBound (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  have hg : GaussianBound f := ⟨A,c,hA,hc',hb⟩
  refine ⟨A*Real.sqrt (Real.pi/c),c,mul_pos hA (Real.sqrt_pos.mpr (div_pos Real.pi_pos hc')),hc',?_⟩
  intro y
  have hi := hg.integrable_slice hc y
  calc
    |marginalOne f y| ≤ ∫ t, |f (Fin.cons t y)| := by
      simpa only [Real.norm_eq_abs,marginalOne] using norm_integral_le_integral_norm (fun t => f (Fin.cons t y))
    _ ≤ ∫ t, (A*gaussianKernel d c y)*Real.exp (-c*t^2) := by
      apply integral_mono hi.norm ((integrable_exp_neg_mul_sq hc').const_mul _)
      intro t
      calc
        _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hb _
        _ = _ := by rw [gaussianKernel_cons]; ring
    _ = (A*Real.sqrt (Real.pi/c))*gaussianKernel d c y := by
      rw [integral_const_mul,integral_gaussian]
      ring

lemma integral_marginalOne {d : ℕ} {f : RV (d+1) → ℝ} (hi : Integrable f volume) :
    (∫ y, marginalOne f y) = ∫ x, f x := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he := hm.integral_comp' f
  have hj := (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv_zero,Function.comp_def] at he hj
  rw [←he]
  exact (integral_prod_symm (fun p : ℝ × RV d => f (Fin.cons p.1 p.2)) hj).symm


end SingleLatticeCovering.Prekopa


end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_LogConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma integral_RV_zero (f : RV 0 → ℝ) : (∫ x, f x)=f 0 := by
  rw [Measure.volume_pi_eq_dirac (0 : RV 0), integral_dirac]

lemma cons_weighted {d : ℕ} (a b x y : ℝ) (u v : RV d) :
    Fin.cons (a*x+b*y) (a•u+b•v) = a•Fin.cons x u+b•Fin.cons y v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl




theorem gaussian_dominated_integral (d : ℕ) {f g h : RV d → ℝ}
    (fc : Continuous f) (gc : Continuous g) (hc : Continuous h)
    (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x) (hp : ∀ x, 0 < h x)
    (fb : GaussianBound f) (gb : GaussianBound g) (hb : GaussianBound h)
    {a b : ℝ} (ha : 0 < a) (hb' : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a•x+b•y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  induction d with
  | zero =>
    simp only [integral_RV_zero]
    have H := hfg 0 0
    simpa only [smul_zero,add_zero] using H
  | succ d ih =>
    have hm : ∀ y z : RV d,
        (marginalOne f y)^a*(marginalOne g z)^b ≤ marginalOne h (a•y+b•z) := by
      intro y z
      apply positive_integral
        (fc.comp (show Continuous (fun t : ℝ => Fin.cons t y) by fun_prop))
        (gc.comp (show Continuous (fun t : ℝ => Fin.cons t z) by fun_prop))
        (fun t => fp (Fin.cons t y)) (fun t => gp (Fin.cons t z))
        (fb.integrable_slice fc _) (gb.integrable_slice gc _) (hb.integrable_slice hc _)
        (fun t => (hp _).le) ha hb' hab
      intro t u
      simpa only [cons_weighted,Function.comp_def,id_eq] using hfg (Fin.cons t y) (Fin.cons u z)
    have H := ih (fb.continuous_marginalOne fc) (gb.continuous_marginalOne gc)
      (hb.continuous_marginalOne hc) (marginalOne_positive fb fc fp)
      (marginalOne_positive gb gc gp) (marginalOne_positive hb hc hp)
      (fb.for_marginalOne fc) (gb.for_marginalOne gc) (hb.for_marginalOne hc) hm
    simpa only [integral_marginalOne (fb.integrable fc),integral_marginalOne (gb.integrable gc),
      integral_marginalOne (hb.integrable hc)] using H


end SingleLatticeCovering.Prekopa

noncomputable section
namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma sum_sq_le_norm_sq (d : ℕ) (x : RV d) :
    (∑ i, (x i)^2) ≤ (d : ℝ)*‖x‖^2 := by
  calc
    _ ≤ ∑ _ : Fin d, ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm x i
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (x i)) hi 2
    _ = _ := by simp

lemma softIndicator_positive {d : ℕ} (K : Set (RV d)) (t : ℝ) (x : RV d) :
    0 < softIndicator K t x := Real.exp_pos _

lemma continuous_softIndicator {d : ℕ} (K : Set (RV d)) (t : ℝ) :
    Continuous (softIndicator K t) := by
  unfold softIndicator
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).pow 2))

lemma softIndicator_gaussianBound {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) {t : ℝ} (ht : 0 < t) : GaussianBound (softIndicator K t) := by
  obtain ⟨R,hR,hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨Real.exp (t*R^2),t/(2*((d : ℝ)+1)),Real.exp_pos _,by positivity,?_⟩
  intro x
  obtain ⟨u,hu,he⟩ := hK.exists_infDist_eq_dist hne x
  have hn : ‖x‖ ≤ infDist x K+R := by
    calc
      ‖x‖ ≤ ‖x-u‖+‖u‖ := by simpa only [add_comm] using norm_le_insert' x u
      _ ≤ infDist x K+R := by rw [he,dist_eq_norm]; exact add_le_add_right (hb u hu) _
  have hs : ‖x‖^2 ≤ 2*((infDist x K)^2+R^2) := by
    have hn' := pow_le_pow_left₀ (norm_nonneg x) hn 2
    nlinarith [sq_nonneg (infDist x K-R)]
  have hs' : (∑ i, (x i)^2) ≤ 2*((d : ℝ)+1)*((infDist x K)^2+R^2) := by
    calc
      _ ≤ (d : ℝ)*‖x‖^2 := sum_sq_le_norm_sq d x
      _ ≤ (d : ℝ)*(2*((infDist x K)^2+R^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (infDist x K),sq_nonneg R]
  rw [abs_of_pos (softIndicator_positive K t x),softIndicator,gaussianKernel,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*((d : ℝ)+1) := by positivity
  have hm := mul_le_mul_of_nonneg_left hs' (div_nonneg ht.le hd.le)
  field_simp at hm ⊢
  nlinarith

lemma infDist_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    infDist (a•x+b•y) C ≤ a*infDist x A+b*infDist y B := by
  obtain ⟨u,hu,heu⟩ := hA.exists_infDist_eq_dist hneA x
  obtain ⟨v,hv,hev⟩ := hB.exists_infDist_eq_dist hneB y
  calc
    _ ≤ dist (a•x+b•y) (a•u+b•v) := infDist_le_dist_of_mem (hABC u hu v hv)
    _ = ‖a•(x-u)+b•(y-v)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖a•(x-u)‖+‖b•(y-v)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg ha,abs_of_nonneg hb,heu,hev,dist_eq_norm,dist_eq_norm]

lemma softIndicator_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (ht : 0 ≤ t)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    (softIndicator A t x)^a*(softIndicator B t y)^b ≤ softIndicator C t (a•x+b•y) := by
  have H := infDist_weighted hA hB hneA hneB ha hb hABC x y
  have hsq : (infDist (a•x+b•y) C)^2 ≤ a*(infDist x A)^2+b*(infDist y B)^2 := by
    have HH := pow_le_pow_left₀ (infDist_nonneg : 0 ≤ infDist (a•x+b•y) C) H 2
    have hm := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (infDist x A-infDist y B))
    nlinarith [sq_nonneg (a*infDist x A+b*infDist y B),sq_nonneg (infDist x A),sq_nonneg (infDist y B)]
  simp only [softIndicator,←Real.exp_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hsq)]



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma softIndicator_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsClosed K)
    (hne : K.Nonempty) (x : RV d) :
    Tendsto (fun n : ℕ => softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (K.indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : x ∈ K
  · simp only [softIndicator,infDist_zero_of_mem hx,zero_pow (by omega : 2 ≠ 0),
      mul_zero,Real.exp_zero,Set.indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hx]
    have hd : 0 < (infDist x K)^2 := sq_pos_of_pos ((hK.notMem_iff_infDist_pos hne).mp hx)
    have hq : Real.exp (-(infDist x K)^2)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd)
    have H := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(infDist x K)^2)).le hq).mul_const
      (Real.exp (-(infDist x K)^2))
    simp only [zero_mul] at H
    convert H using 1
    ext n
    rw [softIndicator,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring

lemma softIndicator_antitone {d : ℕ} (K : Set (RV d)) (x : RV d) :
    Antitone (fun t : ℝ => softIndicator K t x) := by
  intro t u htu
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg htu) (sq_nonneg _)

lemma softIndicator_integral_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) :
    Tendsto (fun n : ℕ => ∫ x, softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (volume K).toReal) := by
  have H := tendsto_integral_of_dominated_convergence (softIndicator K 1)
    (fun n => (continuous_softIndicator K ((n : ℝ)+1)).aestronglyMeasurable)
    ((softIndicator_gaussianBound hK hne zero_lt_one).integrable (continuous_softIndicator K 1))
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (softIndicator_positive K _ x)]
      exact softIndicator_antitone K x (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ (n : ℝ)+1)))
    (Filter.Eventually.of_forall (softIndicator_tendsto hK.isClosed hne))
  simpa only [integral_indicator hK.measurableSet,integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using H




theorem compact_volume {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) :
    ((volume A).toReal)^a*((volume B).toReal)^b ≤ (volume C).toReal := by
  rcases A.eq_empty_or_nonempty with rfl | hneA
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact ENNReal.toReal_nonneg
  rcases B.eq_empty_or_nonempty with rfl | hneB
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt hb),mul_zero]
    exact ENNReal.toReal_nonneg
  have hneC : C.Nonempty := by
    obtain ⟨u,hu⟩ := hneA
    obtain ⟨v,hv⟩ := hneB
    exact ⟨a•u+b•v,hABC u hu v hv⟩
  have hpoint : ∀ n : ℕ,
      (∫ x, softIndicator A ((n : ℝ)+1) x)^a*
      (∫ x, softIndicator B ((n : ℝ)+1) x)^b ≤ ∫ x, softIndicator C ((n : ℝ)+1) x := by
    intro n
    have hn : 0 < (n : ℝ)+1 := by positivity
    apply gaussian_dominated_integral d (continuous_softIndicator _ _) (continuous_softIndicator _ _)
      (continuous_softIndicator _ _) (softIndicator_positive _ _) (softIndicator_positive _ _)
      (softIndicator_positive _ _) (softIndicator_gaussianBound hA hneA hn)
      (softIndicator_gaussianBound hB hneB hn) (softIndicator_gaussianBound hC hneC hn) ha hb hab
    exact softIndicator_weighted hA hB hneA hneB ha.le hb.le hab hn.le hABC
  exact le_of_tendsto_of_tendsto
    (((Real.continuous_rpow_const ha.le).tendsto _).comp (softIndicator_integral_tendsto hA hneA) |>.mul
      (((Real.continuous_rpow_const hb.le).tendsto _).comp (softIndicator_integral_tendsto hB hneB)))
    (softIndicator_integral_tendsto hC hneC) (Filter.Eventually.of_forall hpoint)


end SingleLatticeCovering.Prekopa




namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators




theorem logConcave_section_volume {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => (volume (fiber K y)).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun x y a b ha hb hab => ?_⟩
  apply compact_volume (fiber_compact hK x) (fiber_compact hK y)
    (fiber_compact hK (a•x+b•y)) ha hb hab
  intro u hu v hv
  have H := hconv hu hv ha.le hb.le hab
  exact H

lemma LogConcave.const_mul {D : ℕ} {f : E D → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun x => c*f x) := by
  refine ⟨fun x => mul_nonneg hc (hf.1 x),fun x y a b ha hb hab => ?_⟩
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul,Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb),le_refl]
  · rw [Real.mul_rpow hc.le (hf.1 x),Real.mul_rpow hc.le (hf.1 y)]
    calc
      c^a*f x^a*(c^b*f y^b) = (c^a*c^b)*(f x^a*f y^b) := by ring
      _ = c*(f x^a*f y^b) := by rw [←Real.rpow_add hc,hab,Real.rpow_one]
      _ ≤ c*f (a•x+b•y) := mul_le_mul_of_nonneg_left (hf.2 x y a b ha hb hab) hc.le



theorem logConcave_canonical_density {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => ((volume K)⁻¹).toReal*(volume (fiber K y)).toReal) :=
  LogConcave.const_mul (logConcave_section_volume hK hconv) ENNReal.toReal_nonneg



end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Marginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory ProbabilityTheory Set Filter Isotropization
open scoped ENNReal RealInnerProductSpace Topology

lemma fourthMomentConstant_pos : 0 < fourthMomentConstant := by
  unfold fourthMomentConstant
  positivity


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma integrable_translated_density {k : ℕ} {b : ℝ} (hb : 0 < b) (w : E k) :
    Integrable (fun y => density b (y-w)) volume := by
  exact ((measurePreserving_sub_right volume w).integrable_comp
    (continuous_density k b).aestronglyMeasurable).mpr (integrable_density hb)

attribute [local irreducible] density normalizer


end SingleLatticeCovering.GaussianDensity

end
end
end
end
end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma normalizedProjection_kernel {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : Isotropization.E k) :
    normalizedProjection μ s r g y=∫ x, density (r^2/2) (y-s•colApply g x) ∂μ := by
  rw [normalizedProjection,smoothedProjection,←integral_const_mul]
  congr 1
  funext x
  unfold density
  congr 2
  ring


end SingleLatticeCovering.GaussianProjection


end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_ProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

lemma normalizer_variance_mono {k : ℕ} {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normalizer k (1/(2*u)) ≤ normalizer k (1/(2*v)) := by
  unfold normalizer
  have he (a : ℝ) : Real.pi/(1/(2*a))=Real.pi*(2*a) := by simp only [one_div,div_inv_eq_mul]
  simp only [he]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

lemma densityFloor_pos (k : ℕ) (R : ℝ) : 0 < densityFloor k R := by
  unfold densityFloor
  exact mul_pos (inv_pos.mpr (normalizer_pos k (by norm_num))) (Real.exp_pos _)

lemma variance_density_floor {k : ℕ} {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    {y : E k} (hy : ‖y‖ ≤ 2*(R+1)) : densityFloor k R ≤ density (1/(2*u)) y := by
  have _ := hR
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hN : normalizer k (1/(2*u)) ≤ normalizer k (1/8) := by
    convert normalizer_variance_mono hu0 hu4 using 1 ; norm_num
  unfold densityFloor density
  apply mul_le_mul (inv_anti₀ (normalizer_pos k hb) hN) _ (Real.exp_pos _).le
    (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hy2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  nlinarith [mul_le_mul_of_nonneg_right hbu (sq_nonneg ‖y‖)]

lemma variance_density_nearby {k : ℕ} {u R δ : ℝ} (hu : 1/4 ≤ u) (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/(100*(R+1))) {y w : E k}
    (hy : ‖y‖ ≤ 2*R) (hw : ‖w-y‖ ≤ δ) :
    (3/4)*density (1/(2*u)) y ≤ density (1/(2*u)) w := by
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hδ1 : δ ≤ 1/100 := by
    apply hδsmall.trans
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hδR : δ*(R+1) ≤ 1/100 := by
    have H := (le_div_iff₀ (by positivity : 0 < 100*(R+1))).mp hδsmall
    nlinarith
  have hwN : ‖w‖ ≤ ‖y‖+δ := by
    have H := norm_add_le (w-y) y
    rw [sub_add_cancel] at H
    linarith
  have hw2 := pow_le_pow_left₀ (norm_nonneg w) hwN 2
  have hdq : δ^2 ≤ δ/100 := by nlinarith
  have hxy : ‖w‖^2-‖y‖^2 ≤ 1/10 := by
    have H := mul_le_mul_of_nonneg_right hy hδ
    nlinarith
  have he : -(1/(2*u))*‖y‖^2-1/4 ≤ -(1/(2*u))*‖w‖^2 := by
    have H := mul_le_mul_of_nonneg_left hxy hb.le
    nlinarith
  have hexp : (3/4)*Real.exp (-(1/(2*u))*‖y‖^2) ≤ Real.exp (-(1/(2*u))*‖w‖^2) := by
    have hl : (3/4:ℝ) ≤ Real.exp (-(1/4:ℝ)) := by linarith [Real.add_one_le_exp (-(1/4:ℝ))]
    calc
      _ ≤ Real.exp (-(1/4:ℝ))*Real.exp (-(1/(2*u))*‖y‖^2) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = Real.exp (-(1/(2*u))*‖y‖^2-1/4) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr he
  unfold density
  nlinarith [mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (normalizer_pos k hb).le)]


end SingleLatticeCovering.GaussianDensity

end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma surjective_of_smoothed_lower {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (A : Isotropization.E n →ₗ[ℝ] Isotropization.E k)
    {b : ℝ} (hb : 0 < b)
    (hlower : ∀ y : Isotropization.E k, ‖y‖=1 →
      (normalizer k b)⁻¹*Real.exp (-b) < ∫ x, density b (y-A x) ∂μ) : Function.Surjective A := by
  by_contra h
  have hr : A.range ≠ ⊤ := fun htop => h (LinearMap.range_eq_top.mp htop)
  have ho : A.rangeᗮ ≠ ⊥ := fun hbot => hr (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  let u := ‖z‖⁻¹ • z
  have hu : ‖u‖=1 := norm_smul_inv_norm hz0
  have huo : u ∈ A.rangeᗮ := A.rangeᗮ.smul_mem _ hz
  have hfar (x : Isotropization.E n) : 1 ≤ ‖u-A x‖^2 := by
    have hh : ⟪u,A x⟫=0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp huo (A x) (LinearMap.mem_range_self _ _)
    rw [norm_sub_sq_real,hu,hh]
    nlinarith [sq_nonneg ‖A x‖]
  have hi : Integrable (fun x => density b (u-A x)) μ := by
    apply (integrable_const ((normalizer k b)⁻¹)).mono' (by
      exact ((continuous_density k b).comp (continuous_const.sub A.continuous_of_finiteDimensional)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (density_pos hb _).le]
      unfold density
      apply mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _)))
  have hp (x : Isotropization.E n) : density b (u-A x) ≤ (normalizer k b)⁻¹*Real.exp (-b) := by
    unfold density
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
    apply Real.exp_le_exp.mpr
    nlinarith [hfar x]
  have H := integral_mono hi (integrable_const ((normalizer k b)⁻¹*Real.exp (-b))) hp
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  exact (not_lt_of_ge H) (hlower u hu)


end SingleLatticeCovering.GaussianProjection

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Desmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.Desmoothing
open Set
open scoped RealInnerProductSpace

lemma convex_escape {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {S : Set E} (hS : Convex ℝ S) (hc : IsClosed S)
    {y : E} (hy : y ∉ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ w : E, ‖w-y‖ ≤ δ ∧ ∀ x ∈ S, δ ≤ ‖w-x‖ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
  · exact ⟨y,by simpa using hδ,by simp⟩
  obtain ⟨L,a,hL,ha⟩ := geometric_hahn_banach_closed_point hS hc hy
  have hLne : L ≠ 0 := by
    intro he
    have hh := (hL x₀ hx₀).trans ha
    simp only [he,zero_apply] at hh
    exact lt_irrefl _ hh
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (InnerProductSpace.toDual ℝ E) he
    apply hLne
    simpa only [v,LinearIsometryEquiv.apply_symm_apply,map_zero] using h
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖=1 := norm_smul_inv_norm hv
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨y+δ•u,?_,?_⟩
  · simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ,hu,mul_one,le_refl]
  · intro x hx
    have hpos : 0 < ⟪u,y-x⟫ := by
      have he : ⟪v,y-x⟫=L y-L x := by
        rw [inner_sub_right]
        simp only [v,InnerProductSpace.toDual_symm_apply]
      change 0 < ⟪‖v‖⁻¹ • v,y-x⟫
      rw [inner_smul_left,conj_trivial,he]
      exact mul_pos (inv_pos.mpr hvp) (sub_pos.mpr ((hL x hx).trans ha))
    have he : ⟪u,y+δ•u-x⟫=⟪u,y-x⟫+δ := by
      rw [show y+δ•u-x=(y-x)+δ•u by abel,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
      ring
    have H := real_inner_le_norm u (y+δ•u-x)
    rw [he,hu,one_mul] at H
    linarith


end SingleLatticeCovering.Desmoothing

end
end

section

namespace SingleLatticeCovering.Desmoothing
open Set MeasureTheory Isotropization GaussianDensity
open scoped ENNReal RealInnerProductSpace Topology

lemma logConcave_superlevel {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 < c) : Convex ℝ {x | c ≤ f x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hy
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa only [hb0,ha1,zero_smul,one_smul,add_zero] using hx
  have H := hf.2 x y a b (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab
  have hprod : c^a*c^b ≤ (f x)^a*(f y)^b :=
    mul_le_mul (Real.rpow_le_rpow hc.le hx ha) (Real.rpow_le_rpow hc.le hy hb)
      (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (hf.1 x) _)
  rw [←Real.rpow_add hc a b,hab,Real.rpow_one] at hprod
  exact hprod.trans H

lemma density_le_peak {k : ℕ} {b : ℝ} (hb : 0 < b) (z : Isotropization.E k) :
    density b z ≤ (normalizer k b)⁻¹ := by
  unfold density
  exact mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖]))

lemma density_le_tail {k : ℕ} {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ)
    {z : Isotropization.E k} (hz : δ ≤ ‖z‖) :
    density b z ≤ (normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  unfold density
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hh := pow_le_pow_left₀ hδ hz 2
  nlinarith

lemma integrable_density_mul {k : ℕ} {f : Isotropization.E k → ℝ} (hi : Integrable f volume)
    {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x => density b (w-x)*f x) volume := by
  apply hi.bdd_mul (c := (normalizer k b)⁻¹) ((continuous_density k b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖density b (w-x)‖ ≤ (normalizer k b)⁻¹
    simpa only [Real.norm_eq_abs,abs_of_nonneg (density_pos hb (w-x)).le] using density_le_peak hb (w-x))

lemma integral_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    (∫ x : Isotropization.E k, density b (w-x))=1 := by
  rw [integral_sub_left_eq_self,integral_density hb]

lemma integrable_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x : Isotropization.E k => density b (w-x)) volume := by
  have he (x : Isotropization.E k) : density b (w-x)=density b (x-w) := by
    unfold density
    rw [norm_sub_rev]
  simp only [he]
  exact integrable_translated_density hb w

lemma convolution_upper_of_far_superlevel {k : ℕ} {f : Isotropization.E k → ℝ}
    (hi : Integrable f volume) (hn : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (w : Isotropization.E k)
    (hfar : ∀ x, c ≤ f x → δ ≤ ‖w-x‖) :
    (∫ x : Isotropization.E k, density b (w-x)*f x) ≤ c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  let q := (normalizer k b)⁻¹*Real.exp (-b*δ^2)
  have hq : 0 ≤ q := mul_nonneg (inv_nonneg.mpr (normalizer_pos k hb).le) (Real.exp_pos _).le
  have hpoint (x : Isotropization.E k) : density b (w-x)*f x ≤ c*density b (w-x)+q*f x := by
    by_cases hx : f x ≤ c
    · have H := mul_le_mul_of_nonneg_left hx (density_pos hb (w-x)).le
      nlinarith [mul_nonneg hq (hn x)]
    · have H := mul_le_mul_of_nonneg_right (density_le_tail hb hδ (hfar x (le_of_not_ge hx))) (hn x)
      change density b (w-x)*f x ≤ c*density b (w-x)+q*f x
      linarith [mul_nonneg hc (density_pos hb (w-x)).le]
  have H := integral_mono (integrable_density_mul hi hb w)
    (((integrable_density_sub_left hb w).const_mul c).add (hi.const_mul q)) hpoint
  change (∫ x, density b (w-x)*f x) ≤ ∫ x, c*density b (w-x)+q*f x at H
  rw [integral_add ((integrable_density_sub_left hb w).const_mul c) (hi.const_mul q),
    integral_const_mul,integral_const_mul,integral_density_sub_left hb w,hmass,mul_one,mul_one] at H
  exact H



theorem logConcave_desmoothing {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    (hus : UpperSemicontinuous f) (hi : Integrable f volume) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 < c) (y : Isotropization.E k)
    (hlower : ∀ w : Isotropization.E k, ‖w-y‖ ≤ δ →
      c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) < ∫ x : Isotropization.E k, density b (w-x)*f x) :
    c ≤ f y := by
  by_contra h
  obtain ⟨w,hw,hfar⟩ := convex_escape (logConcave_superlevel hf hc)
    (hus.isClosed_preimage c) h hδ
  exact (not_lt_of_ge (convolution_upper_of_far_superlevel hi hf.1 hmass hb hδ hc.le w hfar)) (hlower w hw)


end SingleLatticeCovering.Desmoothing

end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal

lemma canonical_nonneg {m D : ℕ} (K : Set ((Fin m → ℝ) × E D)) (y : E D) :
    0 ≤ canonical K y := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma canonical_measurable {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    Measurable (canonical K) :=
  ((measurable_fiber_measure volume hK.measurableSet).ennreal_toReal).const_mul _

lemma canonical_usc {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    UpperSemicontinuous (canonical K) := by
  let C := ((volume K)⁻¹).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  intro y t ht
  by_cases hC0 : C=0
  · have hf : canonical K=fun _ => (0 : ℝ) := by funext z; simp [canonical,←show C=((volume K)⁻¹).toReal from rfl,hC0]
    rw [hf] at ht ⊢
    exact Filter.Eventually.of_forall (fun _ => ht)
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hyt : (volume (fiber K y)).toReal < t/C := (lt_div_iff₀ hCp).mpr (by simpa [canonical,mul_comm,C] using ht)
  have H := upperSemicontinuous_fiber_measure volume hK y (ENNReal.ofReal (t/C))
    ((ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK y).measure_ne_top).mpr hyt)
  filter_upwards [H] with z hz
  have hz' := (ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK z).measure_ne_top).mp hz
  simpa [canonical,C,mul_comm] using (lt_div_iff₀ hCp).mp hz'

lemma canonical_map {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) :
    Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
      volume.withDensity (fun y => ENNReal.ofReal (canonical K y)) := by
  have hct : (volume K)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hK0
  have hf (y : E D) : ENNReal.ofReal (canonical K y)= (volume K)⁻¹*volume (fiber K y) := by
    rw [canonical,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hct,
      ENNReal.ofReal_toReal (fiber_compact hK y).measure_ne_top]
  have H := map_snd_uniform (volume : Measure (Fin m → ℝ)) (volume : Measure (E D)) hK.measurableSet
  change Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
    volume.withDensity (fun y => (volume K)⁻¹*volume (fiber K y)) at H
  simpa only [←hf] using H

lemma canonical_mass {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) : Integrable (canonical K) volume ∧ (∫ y, canonical K y)=1 := by
  have hmap := canonical_map hK hK0
  have H := congrArg (fun μ : Measure (E D) => μ univ) hmap
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,Set.preimage_univ,
    Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,
    ENNReal.inv_mul_cancel hK0 hK.measure_ne_top,withDensity_apply _ MeasurableSet.univ] at H
  simp only [Measure.restrict_univ] at H
  have hm : AEMeasurable (fun y => ENNReal.ofReal (canonical K y)) volume :=
    (canonical_measurable hK).ennreal_ofReal.aemeasurable
  have hi := integrable_toReal_of_lintegral_ne_top hm (H.symm ▸ ENNReal.one_ne_top)
  have he := integral_toReal hm (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (canonical_nonneg K _)] at hi he
  exact ⟨hi,by rw [←H,ENNReal.toReal_one] at he; exact he⟩



end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

lemma map_uniform_coordinates {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    (e : E ≃ₗ[ℝ] F) (K : Set E) :
    Measure.map e ((μ K)⁻¹ • μ.restrict K)=(ν (e '' K))⁻¹ • ν.restrict (e '' K) := by
  let em : E ≃ᵐ F := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let c : ℝ≥0∞ := addHaarScalarFactor (μ.map e) ν
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν).ne'
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hmap : μ.map em=c • ν := isAddLeftInvariant_eq_smul (μ.map e) ν
  have hpre : em ⁻¹' (e '' K)=K := Set.preimage_image_eq _ e.injective
  have hval : μ K=c*ν (e '' K) := by
    have H := congrArg (fun γ : Measure F => γ (e '' K)) hmap
    rw [em.map_apply,hpre] at H
    exact H
  have hrestr : (μ.restrict K).map em=c • ν.restrict (e '' K) := by
    have H := em.restrict_map μ (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at H
    exact H.symm
  change ((μ K)⁻¹ • μ.restrict K).map em=_
  rw [Measure.map_smul,hrestr,smul_smul]
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(ν (e '' K))⁻¹*c=(c⁻¹*c)*(ν (e '' K))⁻¹ := by ac_rfl
    _ = (ν (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal RealInnerProductSpace

lemma linear_body_properties {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H := e.toContinuousLinearEquiv.toHomeomorph
  refine ⟨hK.image H.continuous,hc.linear_image e.toLinearMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H

lemma image_volume_ne_zero {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hi : (interior K).Nonempty) : volume (e '' K) ≠ 0 := by
  have hJ : (interior (e '' K)).Nonempty := by
    change (interior (e.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←e.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image e
  exact ne_of_gt ((isOpen_interior.measure_pos volume hJ).trans_le (measure_mono interior_subset))

lemma projected_uniform_density {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K) :
    μ.map (fun x => (e x).2)=volume.withDensity (fun y => ENNReal.ofReal (canonical (e '' K) y)) := by
  let : IsAddHaarMeasure (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) := by
    change IsAddHaarMeasure ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Isotropization.E D)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  rw [hdef]
  change Measure.map (Prod.snd ∘ e.toContinuousLinearEquiv) _ = _
  rw [←Measure.map_map measurable_snd e.toContinuousLinearEquiv.continuous.measurable]
  change Measure.map Prod.snd (Measure.map e _) = _
  rw [LinearCoordinates.map_uniform_coordinates (volume : Measure (Isotropization.E n))
    (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) e K]
  exact canonical_map hJ (image_volume_ne_zero e hi)

lemma projected_convolution {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (b : ℝ) (y : Isotropization.E D) :
    (∫ x, GaussianDensity.density b (y-(e x).2) ∂μ)=
      ∫ z, GaussianDensity.density b (y-z)*canonical (e '' K) z := by
  have H := integral_map (μ := μ) (φ := fun x => (e x).2)
    (f := fun z => GaussianDensity.density b (y-z))
    ((continuous_snd.comp e.toContinuousLinearEquiv.continuous).measurable.aemeasurable)
    (((GaussianDensity.continuous_density D b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  rw [projected_uniform_density e hK hi μ hdef] at H
  rw [←H]
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  have HH := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (Isotropization.E D)))
    (f := fun z => ENNReal.ofReal (canonical (e '' K) z))
    (g := fun z => GaussianDensity.density b (y-z))
    ((canonical_measurable hJ).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))
  simpa only [ENNReal.toReal_ofReal (canonical_nonneg _ _),smul_eq_mul,mul_comm] using HH


end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open LinearMap Module



theorem exists_coordinates {m D : ℕ}
    (A : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] EuclideanSpace ℝ (Fin D))
    (hA : Function.Surjective A) :
    ∃ e : EuclideanSpace ℝ (Fin (m+D)) ≃ₗ[ℝ] ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)),
      ∀ x, (e x).2=A x := by
  obtain ⟨R,hR⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  have hR' (y : EuclideanSpace ℝ (Fin D)) : A (R y)=y := by
    have H := LinearMap.congr_fun hR y
    simpa only [LinearMap.comp_apply,LinearMap.id_apply] using H
  let p : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] A.ker :=
    { toFun := fun x => ⟨x-R (A x),by simp only [LinearMap.mem_ker,map_sub,hR',sub_self]⟩
      map_add' := by intro x y; ext; simp only [map_add,Submodule.coe_add]; abel_nf
      map_smul' := by intro a x; ext; simp only [map_smul,Submodule.coe_smul,smul_sub,RingHom.id_apply] }
  have hbi : Function.Bijective (p.prod A) := by
    constructor
    · intro x y hxy
      have h1 := congrArg (fun z : A.ker × EuclideanSpace ℝ (Fin D) => (z.1 : EuclideanSpace ℝ (Fin (m+D)))) hxy
      have h2 := congrArg Prod.snd hxy
      change A x=A y at h2
      change x-R (A x)=y-R (A y) at h1
      rw [h2] at h1
      exact sub_left_injective h1
    · rintro ⟨z,y⟩
      refine ⟨(z : EuclideanSpace ℝ (Fin (m+D)))+R y,?_⟩
      have he : A (z+R y)=y := by simp only [map_add,hR',LinearMap.mem_ker.mp z.property,zero_add]
      apply Prod.ext
      · apply Subtype.ext
        change z+R y-R (A (z+R y))=z
        rw [he]
        abel
      · exact he
  let e₀ := LinearEquiv.ofBijective (p.prod A) hbi
  have hker : Module.finrank ℝ A.ker=m := by
    have H := A.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hA,finrank_top,finrank_euclideanSpace_fin,finrank_euclideanSpace_fin] at H
    omega
  let e₁ : A.ker ≃ₗ[ℝ] (Fin m → ℝ) := LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_fin_fun] using hker)
  refine ⟨e₀.trans (e₁.prodCongr (LinearEquiv.refl ℝ _)),fun x => rfl⟩


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial CanonicalDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma localStep_pos {R : ℝ} (hR : 0 ≤ R) : 0 < localStep R := by unfold localStep; positivity
lemma localStep_le_one {R : ℝ} (hR : 0 ≤ R) : localStep R ≤ 1 := by
  unfold localStep
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith



theorem actual_canonical_lower {m k D : ℕ} (hn : 0 < m+D) (hk : 2 ≤ k)
    {K : Set (Isotropization.E (m+D))} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E (m+D))) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε R : ℝ} (hs : s^2*((m+D : ℕ):ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48) (hR : 0 ≤ R)
    (hloss : shellLoss (m+D) k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss (m+D) k s r T ε ≤ 1/8)
    (herr : projectionError (m+D) D s r ≤ densityFloor D R/128)
    (htail : tailError D r R ≤ densityFloor D R/128) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧
      ∃ e : Isotropization.E (m+D) ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D),
        ∀ y : Isotropization.E D, ‖y‖ ≤ 2*R →
          density (1/(2*u)) y/2 ≤ canonical (e '' K) y := by
  obtain ⟨u,hu,hu4,g,hg⟩ := actual_smoothed_lower hn hk hK hc μ hdef hμ hiso hs hr hT hε hε1 hDε hloss hloss8
  have hu0 : 0 < u := by linarith
  have hr0 : r ≠ 0 := by linarith
  have hb : 0 < r^2/2 := by positivity
  have hδ : 0 ≤ localStep R := (localStep_pos hR).le
  have hδ1 := localStep_le_one hR
  have hfloor := densityFloor_pos D R
  let A : Isotropization.E (m+D) →ₗ[ℝ] Isotropization.E D := s • colLinear g
  have hconv (y : Isotropization.E D) :
      normalizedProjection μ s r g y = ∫ x, density (r^2/2) (y-A x) ∂μ := by
    exact normalizedProjection_kernel μ s r g y
  have hsurj : Function.Surjective A := by
    apply surjective_of_smoothed_lower μ A hb
    intro y hy
    have hyd : ‖y‖ ≤ 2*(R+1) := by rw [hy]; linarith
    have hl := variance_density_floor hu hu4 hR hyd
    have ht : (normalizer D (r^2/2))⁻¹*Real.exp (-(r^2/2)) ≤ tailError D r R := by
      unfold tailError
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos D hb).le)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (localStep R),sq_le_sq₀ hδ (by norm_num : (0:ℝ) ≤ 1) |>.mpr hδ1]
    have H := hg y
    rw [hconv] at H
    linarith
  obtain ⟨e,he⟩ := LinearCoordinates.exists_coordinates A hsurj
  obtain ⟨hJ,hJc,hJi⟩ := linear_body_properties e hK hc hi
  have hmass := canonical_mass hJ (image_volume_ne_zero e hi)
  have heconv (w : Isotropization.E D) : normalizedProjection μ s r g w =
      ∫ z, density (r^2/2) (w-z)*canonical (e '' K) z := by
    rw [hconv]
    simp_rw [←he]
    exact projected_convolution e hK hi μ hdef (r^2/2) w
  refine ⟨u,hu,hu4,e,fun y hy => ?_⟩
  apply Desmoothing.logConcave_desmoothing (f := canonical (e '' K)) (logConcave_canonical_density hJ hJc)
    (canonical_usc hJ) hmass.1 hmass.2 hb hδ (half_pos (density_pos (by positivity) y)) y
  intro w hw
  have hl := variance_density_nearby hu hR hδ (show localStep R ≤ 1/(100*(R+1)) from le_rfl) hy hw
  have hy' : ‖y‖ ≤ 2*(R+1) := by linarith
  have hf := variance_density_floor hu hu4 hR hy'
  have H := hg w
  rw [heconv] at H
  change density (1/(2*u)) y/2+tailError D r R < _
  linarith


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

lemma normalizer_scaling (D : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    normalizer D (b/a^2)=a^D*normalizer D b := by
  unfold normalizer
  rw [show Real.pi/(b/a^2)=a^2*(Real.pi/b) by field_simp,
    Real.mul_rpow (sq_nonneg a) (by positivity),←Real.rpow_natCast a 2,
    ←Real.rpow_mul ha.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((D:ℝ)/2)=(D:ℝ) by ring,Real.rpow_natCast]

lemma density_scaling {D : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : E D) :
    a^D*density (b/a^2) (a•y)=density b y := by
  rw [density,density,normalizer_scaling D ha hb,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hpow : a^D ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  have hN := ne_of_gt (normalizer_pos D hb)
  have he : -(b/a^2)*(a*‖y‖)^2=-b*‖y‖^2 := by field_simp
  rw [he,mul_inv_rev]
  field_simp

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Isotropization Sections
open scoped ENNReal

lemma verticalScale_fiber {m D : ℕ} {a : ℝ} (ha : a ≠ 0)
    (J : Set ((Fin m → ℝ) × E D)) (y : E D) :
    fiber (verticalScale m D ha '' J) y=fiber J (a⁻¹•y) := by
  ext x
  change (x,y) ∈ verticalScale m D ha '' J ↔ (x,a⁻¹•y) ∈ J
  change (x,y) ∈ (verticalScale m D ha).toEquiv '' J ↔ (x,a⁻¹•y) ∈ J
  rw [(verticalScale m D ha).toEquiv.image_eq_preimage_symm]
  rfl

lemma verticalScale_volume {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) :
    volume (verticalScale m D (ne_of_gt ha) '' J)=ENNReal.ofReal (a^D)*volume J := by
  let S := verticalScale m D (ne_of_gt ha)
  have hm : Measurable (fun y : E D => a⁻¹•y) := by fun_prop
  have H := Measure.map_prod_map (volume : Measure (Fin m → ℝ)) (volume : Measure (E D))
    measurable_id hm
  rw [Measure.map_id,Measure.map_addHaar_smul _ (inv_ne_zero (ne_of_gt ha)),
    finrank_euclideanSpace_fin,inv_pow,inv_inv,abs_of_pos (pow_pos ha D),Measure.prod_smul_right] at H
  change ENNReal.ofReal (a^D) • (volume : Measure ((Fin m → ℝ) × E D)) = Measure.map S.symm volume at H
  have HJ := congrArg (fun μ : Measure ((Fin m → ℝ) × E D) => μ J) H
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (show Measurable S.symm from S.symm.toContinuousLinearEquiv.continuous.measurable) hJ.measurableSet] at HJ
  have he : S.symm ⁻¹' J=S '' J := by
    change S.toEquiv.symm ⁻¹' J=S.toEquiv '' J
    exact S.toEquiv.image_eq_preimage_symm J |>.symm
  rw [he] at HJ
  exact HJ.symm

lemma canonical_verticalScale {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) (y : E D) :
    canonical (verticalScale m D (ne_of_gt ha) '' J) y=(a^D)⁻¹*canonical J (a⁻¹•y) := by
  rw [canonical,verticalScale_fiber,verticalScale_volume ha hJ,
    ENNReal.toReal_inv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_pos ha D).le,mul_inv_rev]
  unfold canonical
  rw [ENNReal.toReal_inv]
  ring

lemma standardize_lower {m D : ℕ} {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J)
    {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    (hlow : ∀ y : E D, ‖y‖ ≤ 2*R → GaussianDensity.density (1/(2*u)) y/2 ≤ canonical J y) :
    ∃ S : ((Fin m → ℝ) × E D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D),
      ∀ y : E D, ‖y‖ ≤ R → GaussianDensity.density (1/2) y/2 ≤ canonical (S '' J) y := by
  have hu0 : 0 < u := by linarith
  have ha := Real.sqrt_pos.mpr hu0
  have ha0 := ne_of_gt ha
  refine ⟨verticalScale m D (inv_ne_zero ha0),fun y hy => ?_⟩
  have ha2 : Real.sqrt u ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
  have hy' : ‖Real.sqrt u•y‖ ≤ 2*R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hy ha.le).trans (mul_le_mul_of_nonneg_right ha2 hR)
  have H := mul_le_mul_of_nonneg_left (hlow _ hy') (pow_pos ha D).le
  rw [canonical_verticalScale (inv_pos.mpr ha) hJ,inv_inv,inv_pow,inv_inv]
  have hd := GaussianDensity.density_scaling (b := (1:ℝ)/2) ha (by norm_num) y
  rw [Real.sq_sqrt hu0.le,show (1/2:ℝ)/u=1/(2*u) by ring] at hd
  rw [←mul_div_assoc,hd] at H
  exact H


end SingleLatticeCovering.CanonicalDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal

lemma normalizer_inv_bound (D : ℕ) {r : ℝ} (hr : 0 < r) :
    (normalizer D (r^2/2))⁻¹ ≤ r^D := by
  have H := normalizer_scaling D (inv_pos.mpr hr) (by norm_num : (0:ℝ) < 1/2)
  have he : (1/2:ℝ)/(r⁻¹)^2=r^2/2 := by field_simp
  rw [he,inv_pow] at H
  have hN : 1 ≤ normalizer D (1/2) := by
    unfold normalizer
    apply Real.one_le_rpow (by have hp := Real.pi_gt_three; linarith) (by positivity)
  rw [H,mul_inv_rev,inv_inv]
  exact mul_le_of_le_one_left (pow_pos hr D).le ((inv_le_one₀ (normalizer_pos D (by norm_num))).mpr hN)

lemma volume_closedBall_bound (D : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume.real (Metric.closedBall (0:E D) T) ≤ Real.exp (T^2)*normalizer D 1 := by
  have _ := hT
  let B : Set (E D) := Metric.closedBall 0 T
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hkernel := integrable_kernel (k := D) (by norm_num : (0:ℝ) < 1)
  have H := setIntegral_mono_on (integrableOn_const (C := Real.exp (-T^2)) hBc.measure_lt_top.ne)
    hkernel.integrableOn hBc.measurableSet (fun y hy => by
      have hn : ‖y‖ ≤ T := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hy
      change Real.exp (-T^2) ≤ Real.exp (-1*‖y‖^2)
      apply Real.exp_le_exp.mpr
      nlinarith [pow_le_pow_left₀ (norm_nonneg y) hn 2])
  have hle : (∫ y : E D in B, Real.exp (-1*‖y‖^2)) ≤ normalizer D 1 := by
    rw [←integral_kernel (k := D) (by norm_num : (0:ℝ) < 1)]
    exact setIntegral_le_integral hkernel (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
  rw [setIntegral_const,smul_eq_mul] at H
  have Hm := mul_le_mul_of_nonneg_right (H.trans hle) (Real.exp_pos (T^2)).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at Hm
  simpa only [mul_comm] using Hm

lemma normalizer_dimension_mono {D k : ℕ} (hD : D ≤ k) : normalizer D (1/8) ≤ normalizer k (1/8) := by
  unfold normalizer
  apply Real.rpow_le_rpow_of_exponent_le (by have hp := Real.pi_gt_three; linarith)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by norm_num)

lemma densityFloor_dimension_mono {D k : ℕ} (hD : D ≤ k) (R : ℝ) : densityFloor k R ≤ densityFloor D R := by
  unfold densityFloor
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (normalizer_pos D (by norm_num)) (normalizer_dimension_mono hD))
    (Real.exp_pos _).le

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory Set Isotropization GaussianDensity
open scoped ENNReal

lemma root_error_identity {n k : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    projectionError n k (1/Real.sqrt (n:ℝ)) r =
      (normalizer k (r^2/2))⁻¹*r*Real.sqrt (k:ℝ)/Real.sqrt (Real.sqrt (n:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg (n:ℝ))
  have hpos := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn0)
  unfold projectionError
  rw [abs_of_nonneg (by positivity)]
  have hs := Real.sqrt_pos.mpr hn0
  field_simp
  nlinarith only [congrArg (fun z : ℝ => r*z*Real.sqrt (k:ℝ)/(normalizer k (r^2/2))) hsq]

lemma normalization_second {n : ℕ} (hn : 0 < n) : (1/Real.sqrt (n:ℝ))^2*(n:ℝ)=1 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [div_pow,Real.sq_sqrt hn0.le,one_pow,one_div,inv_mul_cancel₀ hn0.ne']

end SingleLatticeCovering.GaussianProjection

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection Asymptotics
open scoped Topology

lemma A_pos : 0 < A := by unfold A; positivity

lemma normalizer_log (D : ℕ) {b : ℝ} (hb : 0 < b) :
    normalizer D b=Real.exp ((D:ℝ)/2*Real.log (Real.pi/b)) := by
  rw [normalizer,Real.rpow_def_of_pos (by positivity),mul_comm]

lemma floor_inv_bound {l : ℕ} (hl : 1 ≤ l) :
    (densityFloor (l^4) (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hlog : Real.log (8*Real.pi) ≤ 2*(A-392) := by
    have := le_abs_self (Real.log (8*Real.pi))
    unfold A
    linarith [abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  have hN := normalizer_pos (l^4) (by norm_num : (0:ℝ) < 1/8)
  rw [densityFloor,mul_inv_rev,inv_inv,←Real.exp_neg,normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  rw [show Real.pi/(1/8:ℝ)=8*Real.pi by ring]

  nlinarith

lemma polynomial_exp_decay {p q : ℕ} (hpq : p < q) {a b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (a*t^p-b*t^q)) atTop (𝓝 0) := by
  have H := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) hpq).const_mul_left a
  have ht : Tendsto (fun t : ℝ => Real.exp (-(b/2)*t^q)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_pow_atTop (by omega : q ≠ 0) : Tendsto (fun t : ℝ => t^q) atTop atTop).const_mul_atTop (half_pos hb)
    simpa only [neg_mul,Function.comp_def] using tendsto_neg_atTop_atBot.comp hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)) ?_ ht
  filter_upwards [H.bound (half_pos hb),eventually_ge_atTop (0:ℝ)] with t h ht
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht q)] at h
  apply Real.exp_le_exp.mpr
  linarith [le_abs_self (a*t^p)]

lemma errBound_tendsto : Tendsto errBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (B*t^20-t^30)) atTop (𝓝 0)
  simpa only [one_mul] using (polynomial_exp_decay (a := B) (p := 20) (q := 30) (by omega) (b := 1) (by norm_num))
lemma tailBound_tendsto : Tendsto tailBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp ((A+10)*t^6-t^16/980000)) atTop (𝓝 0)
  convert (polynomial_exp_decay (a := A+10) (p := 6) (q := 16) (by omega) (b := 1/980000) (by norm_num)) using 1
  ext t
  congr 1
  ring

lemma gaussian_prefactor_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹*(l:ℝ)^10*Real.sqrt (D:ℝ) ≤ Real.exp (22*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hr : 1 ≤ (l:ℝ)^10 := one_le_pow₀ ht
  have hp := normalizer_inv_bound D (pow_pos ht0 10)
  have hpd : ((l:ℝ)^10)^D ≤ ((l:ℝ)^10)^(l^4) := pow_le_pow_right₀ hr hD
  have hs : Real.sqrt (D:ℝ) ≤ (l:ℝ)^2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by simpa only [←pow_mul,Nat.reduceMul] using (show (D:ℝ) ≤ (l:ℝ)^4 by exact_mod_cast hD)⟩
  calc
    _ ≤ (((l:ℝ)^10)^(l^4))*(l:ℝ)^10*(l:ℝ)^2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hp.trans hpd) (by positivity)) hs (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp (((l:ℝ)^4*10+12)*Real.log (l:ℝ)) := by
      rw [show (((l:ℝ)^4*10+12)*Real.log (l:ℝ))=
        (l^4:ℕ)*(10*Real.log (l:ℝ))+10*Real.log (l:ℝ)+2*Real.log (l:ℝ) by push_cast; ring,
        Real.exp_add,Real.exp_add,Real.exp_nat_mul]
      rw [show Real.exp (10*Real.log (l:ℝ))=(l:ℝ)^10 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 10,
        show Real.exp (2*Real.log (l:ℝ))=(l:ℝ)^2 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht4 : 1 ≤ (l:ℝ)^4 := one_le_pow₀ ht
      have hlog := Real.log_le_sub_one_of_pos ht0
      have hh := mul_le_mul_of_nonneg_left (show Real.log (l:ℝ) ≤ l by linarith) (show 0 ≤ (l:ℝ)^4*10+12 by positivity)
      nlinarith [mul_le_mul_of_nonneg_right ht4 ht0.le]

lemma volume_parameter_bound {l : ℕ} (hl : 1 ≤ l) :
    volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤
      Real.exp ((l:ℝ)^20+A*(l:ℝ)^4) := by
  have hlog : Real.log Real.pi ≤ 2*A := by
    unfold A
    linarith [le_abs_self (Real.log Real.pi),abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  apply (volume_closedBall_bound (l^4) (by positivity : 0 ≤ (l:ℝ)^10)).trans
  rw [normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  simp only [div_one]
  have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  nlinarith [show ((l:ℝ)^10)^2=(l:ℝ)^20 by ring]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

lemma powerCoeff_bound {l : ℕ} (hl : 1 ≤ l) :
    22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20 ≤ B*(l:ℝ)^20 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have h5 : (l:ℝ)^5 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have h4 : (l:ℝ)^4 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have hh := mul_le_mul_of_nonneg_left h4 A_pos.le
  dsimp [B]
  nlinarith [pow_nonneg (Nat.cast_nonneg l : (0:ℝ) ≤ l) 20,A_pos]

lemma uniform_error_bound {n l D : ℕ} (hn : 0 < n) (hl : 1 ≤ l) (hD : D ≤ l^4)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n D (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ≤
      densityFloor D (6*(l:ℝ)^2)*errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_div,div_eq_mul_inv, mul_inv_rev]
  calc
    _ ≤ Real.exp (22*(l:ℝ)^5)* Real.exp (A*(l:ℝ)^4)*(Real.exp ((l:ℝ)^30))⁻¹ := by
      have hi := inv_anti₀ (Real.exp_pos ((l:ℝ)^30)) hroot
      have hp := gaussian_prefactor_bound hl hD
      rw [←mul_assoc]
      exact mul_le_mul (mul_le_mul hp hinv (inv_pos.mpr hf).le (Real.exp_pos _).le) hi (inv_pos.mpr hq).le (by positivity)
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^30) := by rw [←Real.exp_neg,←Real.exp_add,←Real.exp_add]; rfl
    _ ≤ errBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have hh := powerCoeff_bound hl
      linarith [pow_nonneg ht.le 20]

lemma uniform_ball_error {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10)*
        volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤ errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_mul_eq_mul_div]
  calc
    _ ≤ (Real.exp (22*(l:ℝ)^5)*Real.exp ((l:ℝ)^20+A*(l:ℝ)^4))/Real.exp ((l:ℝ)^30) := by
      apply div_le_div₀ (by positivity) (by gcongr; exact gaussian_prefactor_bound hl le_rfl; exact volume_parameter_bound hl)
        (Real.exp_pos _) hroot
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20-(l:ℝ)^30) := by
      rw [div_eq_mul_inv,←Real.exp_neg,←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ errBound (l:ℝ) := Real.exp_le_exp.mpr (sub_le_sub_right (powerCoeff_bound hl) _)

lemma kernel_normalizer_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹ ≤ Real.exp (10*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  apply (normalizer_inv_bound D (pow_pos ht0 10)).trans
  apply (pow_le_pow_right₀ (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) hD).trans
  rw [←Real.exp_log (pow_pos (pow_pos ht0 10) (l^4)),Real.log_pow,Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  have hh := mul_le_mul_of_nonneg_left (le_trans (Real.log_le_sub_one_of_pos ht0) (by linarith : (l:ℝ)-1 ≤ l))
    (show 0 ≤ 10*(l:ℝ)^4 by positivity)
  nlinarith

lemma tail_exponent_bound {l : ℕ} (hl : 1 ≤ l) :
    (l:ℝ)^16/980000 ≤ (((l:ℝ)^10)^2/2)*(localStep (6*(l:ℝ)^2))^2 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  unfold localStep
  have hd : 0 < 6*(l:ℝ)^2+1 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ (l:ℝ)^16 by positivity),
    show ((l:ℝ)^10)^2=(l:ℝ)^16*(l:ℝ)^4 by ring]

lemma uniform_tail_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    tailError D ((l:ℝ)^10) (6*(l:ℝ)^2) ≤ densityFloor D (6*(l:ℝ)^2)*tailBound (l:ℝ) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  unfold tailError
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (10*(l:ℝ)^5)*Real.exp (-(l:ℝ)^16/980000)*Real.exp (A*(l:ℝ)^4) := by
      apply mul_le_mul (mul_le_mul (kernel_normalizer_bound hl hD) (Real.exp_le_exp.mpr (by linarith [tail_exponent_bound hl]))
        (Real.exp_pos _).le (Real.exp_pos _).le) hinv (inv_pos.mpr hf).le (by positivity)
    _ = Real.exp (10*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^16/980000) := by
      rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ tailBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have h5 : (l:ℝ)^5 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      have h4 : (l:ℝ)^4 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      nlinarith [mul_le_mul_of_nonneg_left h4 A_pos.le]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

lemma shellRate_tendsto : Tendsto shellRate atTop (𝓝 0) := by
  have H := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/180000) (by norm_num)
  have H' : Tendsto (fun t : ℝ => 800*(t*Real.exp (-(1/180000)*t))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_zero] using H.const_mul 800
  change Tendsto (fun t : ℝ => 800*t*Real.exp (-t^2/180000)) atTop (𝓝 0)
  apply squeeze_zero' ?_ ?_ H'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 ≤ t := by linarith
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith

lemma denRate_tendsto : Tendsto denRate atTop (𝓝 0) := by
  have H : Tendsto (fun t : ℝ => t^2/160000) atTop atTop :=
    (tendsto_pow_atTop (by omega : (2:ℕ) ≠ 0)).atTop_div_const (by norm_num)
  change Tendsto (fun t : ℝ => Real.exp (-t^2/160000)) atTop (𝓝 0)
  simpa only [Function.comp_def,neg_div] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp H)

lemma shellBound_tendsto : Tendsto shellBound atTop (𝓝 0) := by
  have HP : Tendsto (fun t : ℝ => t^16) atTop atTop := tendsto_pow_atTop (by omega)
  have H : Tendsto (fun t : ℝ => 2/t^16) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp HP).const_mul (2:ℝ))
  change Tendsto (fun t : ℝ => 2*(shellRate t+2*(errBound t+2/t^16))) atTop (𝓝 0)
  simpa only [zero_add,add_zero,mul_zero] using
    (shellRate_tendsto.add ((errBound_tendsto.add H).const_mul 2)).const_mul 2

lemma shell_term_bound {l : ℕ} (hl : 2 ≤ l) :
    (4*((l^4-1:ℕ)+1:ℝ)/((l^4-1:ℕ)*(1/(100*(l:ℝ))))*
      Real.exp (-((l^4-1:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/9)) ≤ shellRate (l:ℝ) := by
  have ht : (2:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := by linarith
  have h4 : (2:ℝ) ≤ (l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-2),sq_nonneg ((l:ℝ)-2)]
  have hk : 1 ≤ l^4 := by exact_mod_cast (show (1:ℝ) ≤ (l:ℝ)^4 by linarith)
  have hm : ((l^4-1:ℕ):ℝ)=(l:ℝ)^4-1 := by rw [Nat.cast_sub hk,Nat.cast_pow,Nat.cast_one]
  rw [hm]
  have hp : 4*((l:ℝ)^4-1+1)/(((l:ℝ)^4-1)*(1/(100*(l:ℝ)))) ≤ 800*(l:ℝ) := by
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < (l:ℝ)^4-1) (by positivity))).mpr
    have he : 800*(l:ℝ)*(((l:ℝ)^4-1)*(1/(100*(l:ℝ))))=8*((l:ℝ)^4-1) := by field_simp; ring
    rw [he]
    linarith
  have he : -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9 ≤ -(l:ℝ)^2/180000 := by
    rw [show -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9=-(((l:ℝ)^4-1)/(90000*(l:ℝ)^2)) by field_simp; ring,
      neg_div,neg_le_neg_iff]
    apply (le_div_iff₀ (by positivity : 0 < 90000*(l:ℝ)^2)).mpr
    nlinarith
  exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)

lemma denominator_identity {l : ℕ} (hl : 1 ≤ l) :
    Real.exp (-((l^4:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/16)=denRate (l:ℝ) := by
  have ht0 : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold denRate
  congr 1
  push_cast
  field_simp
  ring

lemma markov_term_bound {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l) :
    ((l^4:ℕ):ℝ)*((1/Real.sqrt (n:ℝ))^2*(n:ℝ)+1/((l:ℝ)^10)^2)/((l:ℝ)^10)^2 ≤ 2/(l:ℝ)^16 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  rw [normalization_second hn,Nat.cast_pow]
  have h1 : 1/((l:ℝ)^10)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (one_le_pow₀ ht))
  calc
    _ ≤ (l:ℝ)^4*2/((l:ℝ)^10)^2 := by gcongr; linarith
    _ = _ := by field_simp

lemma uniform_shell_bound {n l : ℕ} (hn : 0 < n) (hl : 2 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)))
    (hden : denRate (l:ℝ) ≤ 1/2) :
    shellLoss n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ((l:ℝ)^10) (1/(100*(l:ℝ))) ≤ shellBound (l:ℝ) := by
  have hl1 : 1 ≤ l := by omega
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold shellLoss shellError
  rw [denominator_identity hl1]
  have hd : 0 < 1-denRate (l:ℝ) := by linarith
  apply (div_le_iff₀ hd).mpr
  have H := shell_term_bound hl
  have HE := uniform_ball_error hn hl1 hroot
  have HM := markov_term_bound hn hl1
  have hh : 0 ≤ shellRate (l:ℝ)+2*(errBound (l:ℝ)+2/(l:ℝ)^16) := by
    dsimp [shellRate,errBound]; positivity
  dsimp [shellBound]
  nlinarith

lemma uniform_numeric_conditions : ∀ᶠ l : ℕ in atTop,
    2 ≤ l ∧ denRate (l:ℝ) ≤ 1/2 ∧ errBound (l:ℝ) ≤ 1/128 ∧ tailBound (l:ℝ) ≤ 1/128 ∧
    shellBound (l:ℝ) < 1/(4*Prekopa.fourthMomentConstant) ∧ shellBound (l:ℝ) ≤ 1/8 := by
  have hfourth : 0 < Prekopa.fourthMomentConstant := Prekopa.fourthMomentConstant_pos
  have hnat : Tendsto (fun l : ℕ => (l:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (denRate_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)),
    (errBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (tailBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (shellBound_tendsto.comp hnat).eventually (eventually_lt_nhds (by positivity : (0:ℝ) < 1/(4*Prekopa.fourthMomentConstant))),
    (shellBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/8))]
    with l h1 h2 h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6⟩

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter Set GaussianDensity GaussianProjection CanonicalDensity
open scoped Topology ENNReal




theorem eventually_local_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (E (m+D)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : E (m+D) ≃ᵃ[ℝ] ((Fin m → ℝ) × E D),
          ∀ y : E D, ‖y‖ ≤ 6*(l:ℝ)^2 → density (1/2) y/2 ≤ canonical (e '' K) y := by
  filter_upwards [uniform_numeric_conditions] with l hl
  obtain ⟨hl2,hden,herr,htail,hloss,hloss8⟩ := hl
  have hl1 : 1 ≤ l := by omega
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl1
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hl4 : l ≤ l^4 := Nat.le_self_pow (by omega) l
  have hk : 2 ≤ l^4 := hl2.trans hl4
  intro m D hD hn hroot K hK hc hi
  have hDk : D ≤ l^4 := hD.trans hl4
  obtain ⟨g,hJ,hJc,hJi,hprob,hmem,hiso,_,_,_⟩ := Isotropization.isotropic_logConcave_affine_body hK hc hi
  let := hprob
  have hε : (0:ℝ) < 1/(100*(l:ℝ)) := by positivity
  have hε1 : (1:ℝ)/(100*(l:ℝ)) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hDε : (D:ℝ)*(1/(100*(l:ℝ))) ≤ 1/48 := by
    have hd : (D:ℝ) ≤ l := by exact_mod_cast hD
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hShell := uniform_shell_bound hn hl2 hroot hden
  have hErr := uniform_error_bound hn hl1 hDk hroot
  have hTail := uniform_tail_bound hl1 hDk
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  obtain ⟨u,hu,hu4,e,he⟩ := actual_canonical_lower hn hk hJ hJc hJi
    (Isotropization.uniformLaw (g '' K)) rfl hmem hiso (normalization_second hn)
    (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) (pow_pos ht0 10) hε hε1 hDε
    (show 0 ≤ 6*(l:ℝ)^2 by positivity) (hShell.trans_lt hloss) (hShell.trans hloss8)
    (hErr.trans (by nlinarith [mul_le_mul_of_nonneg_left herr hf.le]))
    (hTail.trans (by nlinarith [mul_le_mul_of_nonneg_left htail hf.le]))
  have hcomp : IsCompact (e '' (g '' K)) := hJ.image e.toContinuousLinearEquiv.continuous
  obtain ⟨S,hS⟩ := standardize_lower hcomp hu hu4 (show 0 ≤ 6*(l:ℝ)^2 by positivity) he
  refine ⟨g.trans (e.trans S).toAffineEquiv,fun y hy => ?_⟩
  have himage : (g.trans (e.trans S).toAffineEquiv) '' K=S '' (e '' (g '' K)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [himage]
  exact hS y hy


end SingleLatticeCovering.GaussianNumerics

end




end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

lemma sectionRadius_le_localScale (C : ℝ) (n : ℕ) :
    sectionRadius C n ≤ (localScale C n : ℝ) := by
  have H := Nat.le_ceil (sectionRadius C n)
  dsimp [localScale]
  push_cast
  linarith

lemma dimension_le_localScale {C : ℝ} (hC : 0 < C) {n D : ℕ}
    (hD : (D:ℝ) ≤ C*((firstSize n:ℝ)+1)) : D ≤ localScale C n := by
  have _ := hC
  have hc := sectionRadius_le_localScale C n
  have hh : (D:ℝ) ≤ (localScale C n:ℝ) := by
    dsimp [sectionRadius] at hc
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity]
  exact_mod_cast hh

lemma localScale_tendsto {C : ℝ} (hC : 0 < C) : Tendsto (localScale C) atTop atTop := by
  apply tendsto_atTop_mono _ firstSize_tendsto
  intro n
  have H := sectionRadius_le_localScale C n
  dsimp [sectionRadius] at H
  exact_mod_cast (show (firstSize n:ℝ) ≤ (localScale C n:ℝ) by
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity])

lemma eventually_localScale_root {C : ℝ} (hC : 0 < C) : ∀ᶠ n : ℕ in atTop,
    Real.exp ((localScale C n:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := by
  let H : ℝ := 3*(C+2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : (fun n : ℕ => (Real.log (Real.log (n:ℝ)))^60) =o[atTop]
      (fun n => Real.log (n:ℝ)) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((60:ℕ):ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto log_nat_atTop
  filter_upwards [hsmall.bound (by positivity : 0 < 1/(4*H^30)),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℕ)] with n hbound hs hn
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ Real.log (Real.log (n:ℝ)) := le_trans zero_le_one hs
  have hs2 : 1 ≤ (Real.log (Real.log (n:ℝ)))^2 := one_le_pow₀ hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n:ℝ))))
  change (firstSize n:ℝ) < (Real.log (Real.log (n:ℝ)))^2+1 at hceil
  have hlceil := Nat.ceil_lt_add_one (sectionRadius_pos hC n).le
  have hl : (localScale C n:ℝ) ≤ H*(Real.log (Real.log (n:ℝ)))^2 := by
    dsimp [localScale,sectionRadius]
    push_cast
    dsimp [sectionRadius] at hlceil
    have hh := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ C+1 by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (show 0 ≤ 2*C+5 by linarith) (sub_nonneg.mpr hs2)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs0 _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hbound
  have hpow : (localScale C n:ℝ)^30 ≤ H^30*(Real.log (Real.log (n:ℝ)))^60 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (localScale C n)) hl 30
    simpa only [mul_pow,←pow_mul] using hh
  have hexp : 4*(localScale C n:ℝ)^30 ≤ Real.log (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 4*H^30)
    have he : (4*H^30)*(1/(4*H^30)*Real.log (n:ℝ))=Real.log (n:ℝ) := by field_simp
    rw [he] at hh
    nlinarith
  have hlog : Real.log (Real.sqrt (Real.sqrt (n:ℝ)))=Real.log (n:ℝ)/4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt hnp.le]
    ring
  rw [←Real.exp_log (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnp))]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  linarith


end SingleLatticeCovering.FinalRates



namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory MeasureTheory.Measure Set Filter Topology GaussianDensity CanonicalDensity Sections
open scoped ENNReal

lemma normalizer_half (D : ℕ) : normalizer D (1/2)=(Real.sqrt (2*Real.pi))^D := by
  unfold normalizer
  rw [show Real.pi/(1/2)=2*Real.pi by ring,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  ring

lemma density_half_gaussian {D : ℕ} (y : E D) :
    GaussianDensity.density (1/2) y=Sections.gaussian (E D) y := by
  unfold GaussianDensity.density Sections.gaussian
  rw [normalizer_half,finrank_euclideanSpace_fin,zpow_neg,zpow_natCast]
  congr 1
  congr 1
  ring


theorem eventually_local_coordinate_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (Fin (m+D) → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
          ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ 6*(l:ℝ)^2 →
            (volume (e '' K)).toReal*Folded.gamma y/2 ≤
              (volume (coordinateFiber (e '' K) y)).toReal := by
  filter_upwards [eventually_local_position] with l hl
  intro m D hD hn hroot K hK hc hi
  let A : (Fin (m+D) → ℝ) ≃ₗ[ℝ] E (m+D) := (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).symm
  have hAK : IsCompact (A '' K) := hK.image A.toContinuousLinearEquiv.continuous
  have hAc : Convex ℝ (A '' K) := hc.linear_image A.toLinearMap
  have hAi : (interior (A '' K)).Nonempty := by
    change (interior (A.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←A.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image _
  obtain ⟨g,hg⟩ := hl m D hD hn hroot (A '' K) hAK hAc hAi
  let J := g '' (A '' K)
  have hJ : IsCompact J := hAK.image g.toAffineMap.continuous_of_finiteDimensional
  let G : E (m+D) ≃ₜ ((Fin m → ℝ) × E D) :=
    { toEquiv := g.toEquiv
      continuous_toFun := g.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := g.symm.toAffineMap.continuous_of_finiteDimensional }
  have hJi : (interior J).Nonempty := by
    change (interior (G '' (A '' K))).Nonempty
    rw [←G.image_interior]
    exact hAi.image G
  have hJ0 : 0 < (volume J).toReal := by
    apply ENNReal.toReal_pos (ne_of_gt ?_) hJ.measure_ne_top
    exact (isOpen_interior.measure_pos volume hJi).trans_le (measure_mono interior_subset)
  let e := A.toAffineEquiv.trans (g.trans (flatten m D).toAffineEquiv)
  have he : e '' K=flatten m D '' J := by
    dsimp [e,J]
    rw [Set.image_image,Set.image_image]
    rfl
  refine ⟨e,fun y hy => ?_⟩
  rw [he,flatten_volume m D hJ]
  have hf : coordinateFiber (flatten m D '' J) y=Sections.fiber J (WithLp.toLp 2 y) := by
    have H := flatten_fiber (flatten m D '' J) (WithLp.toLp 2 y)
    have hc : (flatten m D).symm '' ((flatten m D) '' J)=J := by
      simp only [Set.image_image,LinearEquiv.symm_apply_apply,Set.image_id']
    rw [hc] at H
    exact H.symm
  rw [hf]
  have H := hg (WithLp.toLp 2 y) hy
  rw [density_half_gaussian,gaussian_toLp] at H
  change Folded.gamma y/2 ≤ canonical J (WithLp.toLp 2 y) at H
  rw [canonical,ENNReal.toReal_inv] at H
  have HH := mul_le_mul_of_nonneg_left H hJ0.le
  rw [←mul_assoc,mul_inv_cancel₀ hJ0.ne',one_mul] at HH
  simpa only [mul_div_assoc] using HH


end SingleLatticeCovering.GaussianNumerics




end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unconditional eventual covering bound, using the actual prime-congruence
and local affine Gaussian-position producers. Conditional intermediate interfaces
retain their stated hypotheses and are not used as unproved assumptions here. -/

noncomputable section

namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal




theorem eventual_single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨cutoff,hcut,C,k,κ,hC,hk,hκ,hvertical⟩ := vertical_patterns_alphabets
  let CT : ℝ := 301
  have hCT : 0 ≤ CT := by norm_num [CT]
  have hCTeq : 1+CT=302 := by norm_num [CT]
  obtain ⟨Cstar,hstar,hconditions⟩ := FinalRates.final_conditions hC hk
    (show 0 < Real.exp (-1)/8 by positivity) (show 0 ≤ Real.exp 1/8 by positivity)
    hκ (show (1 : ℝ) ≤ 3 by norm_num) hCT
  refine ⟨Real.exp 1*Cstar,by positivity,?_⟩
  filter_upwards [hconditions,FinalRates.eventually_marginal_scales hC (by norm_num : (0:ℝ) < 1)
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 0),
    FinalRates.firstSize_tendsto.eventually (eventually_ge_atTop cutoff),
    (FinalRates.localScale_tendsto hC).eventually GaussianNumerics.eventually_local_coordinate_position,
    FinalRates.eventually_localScale_root hC,
      FinalRates.eventually_dimension_small hC,eventually_ge_atTop (540 : ℕ)]
      with n hn hscale hfirst hgaussian hroot hdim hn540
  obtain ⟨B,c,hcb,hcs,hDim,hRad,hAlphabet,hPattern⟩ := hvertical (FinalRates.firstSize n) hfirst
  have hDdim : (c.fullDim : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) := by
    simpa [Chain.fullDim,Nat.cast_add] using hDim
  obtain ⟨hDn,hm,hcap,hload,hcrit,hcount⟩ := hn.2 c.fullDim hDdim
  have hm270 : 270 ≤ n-c.fullDim := by
    have hd := (hdim c.fullDim hDdim).2
    have hnR : (540 : ℝ) ≤ n := by exact_mod_cast hn540
    have hh : (270 : ℝ) ≤ ((n-c.fullDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hDn]
      linarith
    exact_mod_cast hh
  rw [hCTeq] at hcrit
  obtain ⟨_,_,_,_,_,hSmall⟩ := hscale c.fullDim hDdim
  have hD : 0 < c.fullDim := by
    have hfirstdim := chain_first_le_dim c
    rw [hcb] at hfirstdim
    dsimp [Chain.fullDim]
    omega
  let m := n-c.fullDim
  have hmn : m+c.fullDim=n := Nat.sub_add_cancel hDn
  have hmnle : m ≤ n := Nat.sub_le _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let ρ := Cstar*(n : ℝ)*Real.log (n : ℝ)
  let ε := Real.exp (-k*(FinalRates.firstSize n : ℝ)^(70/100 : ℝ))
  let R := FinalRates.sectionRadius C n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2 :=
    FinalRates.radius_sq_bound hC.le (Nat.cast_nonneg _) hRad
  have step : coversAtBound (m+c.fullDim) ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ)) := by
    intro K hK hc hi
    obtain ⟨e,he⟩ := hgaussian m c.fullDim (FinalRates.dimension_le_localScale hC hDdim)
      (by omega : 0 < m+c.fullDim) (by simpa only [hmn] using hroot) K hK hc hi
    obtain ⟨heK,hec,hei⟩ := affine_body e hK hc hi
    have heV := body_volume_pos heK hei
    have hg : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
        (volume (e '' K)).toReal*gamma y/2 ≤ (volume (coordinateFiber (e '' K) y)).toReal := by
      intro y hy
      apply he y
      apply hy.trans
      calc
        6*(c.fullDim:ℝ)*R ≤ 6*(FinalRates.localScale C n:ℝ)*(FinalRates.localScale C n:ℝ) := by
          gcongr
          · exact (FinalRates.sectionRadius_pos hC n).le
          · exact_mod_cast FinalRates.dimension_le_localScale hC hDdim
          · exact FinalRates.sectionRadius_le_localScale C n
        _ = 6*(FinalRates.localScale C n:ℝ)^2 := by ring
    obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := sections_and_circuits_cover c hm270 hD (e '' K) heK hec heV
      (FinalRates.sectionRadius_pos hC n) hrad hSmall hg κ ρ ε (Real.sqrt (m : ℝ))
      (8*(n : ℝ)*Real.log (n : ℝ)) hρ (Real.sqrt_nonneg _) (by positivity)
      (by
        intro y
        obtain ⟨P,hPn,hPb,hPl,hPt,hPw⟩ := hPattern y
        exact ⟨P,hPn,hPb,hPl,hPw⟩)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hload) hcap hcrit (by
        intro δ s hs
        have hs' : (s.card : ℝ) ≤ (3*(n : ℝ)^2)^c.fullDim := hs.trans (by
          gcongr)
        have ha : ∀ j < c.fullDim, Real.log ((c.alphabetSeq j).card+1 : ℝ) ≤
            Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2 := by
          intro j hj
          simpa only [c.alphabetSeq_fin ⟨j,hj⟩] using hAlphabet ⟨j,hj⟩
        simpa only [Nat.sub_add_cancel hDn] using hcount s c.alphabetSeq hs' ha)
    let := hd
    let := hfull
    have hb : (volume (e '' K)).toReal/ZLattice.covolume Λ volume ≤
        (Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by
      convert hbound using 1 ; dsimp [ρ] ; ring
    exact pull_back_cover e K Λ hcover hb
  change coversAtBound n ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ))
  simpa only [hmn] using step


end SingleLatticeCovering.Assembly


end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform, unconditional single-lattice covering bound in every dimension at least two.
The eventual bound uses the proved analytic and geometric producers; finite-dimensional
absorption supplies one absolute constant for all dimensions. -/

noncomputable section

namespace SingleLatticeCovering
open MeasureTheory
open scoped Pointwise











theorem single_lattice_covering_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨C,hC,h⟩ := Assembly.eventual_single_lattice_covering
  obtain ⟨C',hC',h'⟩ := FiniteDimensions.absorb_finitely_many_dimensions ⟨C,h⟩
  exact ⟨C',hC',fun n hn K hK => h' n hn K hK.1 hK.2.1 hK.2.2⟩


end SingleLatticeCovering



end

end OAI
end

theorem solution : type_of% @OAI.SingleLatticeCovering.single_lattice_covering_oai := @OAI.SingleLatticeCovering.single_lattice_covering_oai
