-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:35:24.07838+00:00
-- url     : https://prove2.me/submissions/00fdc2a8-49ba-4e2e-8479-c818002ab9a5

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_bulkDeviationAt_integral_tendsto
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_averaged_increment_good
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_omittedBulkDeviation_integral_tendsto

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma gaussianCoordinatePrefix_measurePreserving (n : ℕ) :
    MeasurePreserving (gaussianCoordinatePrefix n) countableGaussianLaw
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  refine ⟨by unfold gaussianCoordinatePrefix; fun_prop,?_⟩
  change Measure.map (fun g : ℕ → ℝ => fun i : Fin n => g i.val)
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)=_
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

variable {S : Type*}

lemma finiteGaussian_exp_integrable (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    Integrable (fun g : Fin n → ℝ => Real.exp (t*∑ i, g i*a i))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := Integrable.fintype_prod (fun i : Fin n =>
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t*a i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext g
  rw [Finset.mul_sum,Real.exp_sum]
  congr 1
  ext i
  congr 1
  ring

lemma finiteGaussian_exp_integral (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (∫ g : Fin n → ℝ, Real.exp (t*∑ i, g i*a i)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Real.exp (t^2*(∑ i, a i^2)/2) := by
  have he : (fun g : Fin n → ℝ => Real.exp (t*∑ i, g i*a i))=
      fun g => ∏ i, Real.exp ((t*a i)*g i) := by
    funext g
    rw [Finset.mul_sum,Real.exp_sum]
    congr 1
    ext i
    congr 1
    ring
  rw [he,integral_fintype_prod_eq_prod (fun i : Fin n => fun x => Real.exp ((t*a i)*x))]
  have hi (i : Fin n) : (∫ x, Real.exp ((t*a i)*x) ∂gaussianReal 0 1)=
      Real.exp ((t*a i)^2/2) := by
    have hh := mgf_gaussianReal (X := fun x : ℝ => x) (p := gaussianReal 0 1)
      (μ := 0) (v := 1) (by simp) (t*a i)
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using hh
  simp_rw [hi]
  rw [← Real.exp_sum,Finset.mul_sum,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gaussianPrefixField_exp_integrable (v : ℕ → S → ℝ) (n : ℕ) (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*gaussianPrefixField v n g x)) countableGaussianLaw := by
  exact (gaussianCoordinatePrefix_measurePreserving n).integrable_comp_of_integrable
    (finiteGaussian_exp_integrable n (fun i => v i.val x) t)

lemma gaussianPrefixField_exp_integral (v : ℕ → S → ℝ) (n : ℕ) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*gaussianPrefixField v n g x) ∂countableGaussianLaw)=
      Real.exp (t^2*(∑ i : Fin n, v i.val x^2)/2) := by
  rw [← finiteGaussian_exp_integral n (fun i => v i.val x) t]
  have hm := gaussianCoordinatePrefix_measurePreserving n
  conv_rhs => rw [← hm.map_eq]
  rw [integral_map hm.measurable.aemeasurable (by
    rw [hm.map_eq]
    exact (finiteGaussian_exp_integrable n (fun i => v i.val x) t).aestronglyMeasurable)]
  rfl

lemma countableGaussianField_exp_integrable (v : ℕ → S → ℝ) (L : S → ℕ) (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*countableGaussianField v L g x)) countableGaussianLaw :=
  gaussianPrefixField_exp_integrable v (L x) x t

lemma countableGaussianField_exp_integral (v : ℕ → S → ℝ) (L : S → ℕ) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianField v L g x) ∂countableGaussianLaw)=
      Real.exp (t^2*(∑ i : Fin (L x), v i.val x^2)/2) :=
  gaussianPrefixField_exp_integral v (L x) x t

lemma maskedGaussianCoefficient_measurable [MeasurableSpace S] {v : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hL : Measurable L) (i : ℕ) :
    Measurable (maskedGaussianCoefficient v L i) :=
  (hv i).piecewise (measurableSet_lt measurable_const hL) measurable_const

lemma sum_range_cutoff (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, if i < m then a i else 0)=∑ i ∈ Finset.range (min n m), a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      by_cases h : n < m
      · have hn : min n m=n := min_eq_left (by omega)
        have hn' : min (n+1) m=n+1 := min_eq_left (by omega)
        rw [hn,hn',ite_eq_left h,Finset.sum_range_succ]
      · have hn : min n m=m := min_eq_right (by omega)
        have hn' : min (n+1) m=m := min_eq_right (by omega)
        rw [hn,hn',ite_eq_right h,add_zero]

lemma truncatedCountableGaussianField_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (n : ℕ) (g : ℕ → ℝ) (x : S) :
    truncatedCountableGaussianField v L n g x=gaussianPrefixField v (min n (L x)) g x := by
  unfold truncatedCountableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun i => g i * maskedGaussianCoefficient v L i x) n,
    Fin.sum_univ_eq_sum_range (fun i => g i * v i x) (min n (L x))]
  have he (i : ℕ) : g i*maskedGaussianCoefficient v L i x=
      if i<L x then g i*v i x else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_range_cutoff _ n (L x)

lemma truncatedCountableGaussianField_eventually_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (x : S) : ∀ᶠ n in atTop, ∀ g,
      truncatedCountableGaussianField v L n g x=countableGaussianField v L g x := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn g
  rw [truncatedCountableGaussianField_eq,min_eq_right hn]
  rfl

lemma gaussianCoefficient_prefix_sq_le (v : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) (x : S) :
    (∑ i : Fin (min n (L x)), v i.val x^2) ≤ ∑ i : Fin (L x), v i.val x^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => v i x ^ 2) (min n (L x)),
    Fin.sum_univ_eq_sum_range (fun i => v i x ^ 2) (L x)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (min_le_right n (L x))) (fun _ _ _ => sq_nonneg _)

lemma countableGaussianField_exp_integral_le (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianField v L g x) ∂countableGaussianLaw) ≤
      Real.exp (t^2*D/2) := by
  rw [countableGaussianField_exp_integral]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hD x) (sq_nonneg t)) (by norm_num))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLogIntensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma standardGaussian_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! hd using 1
  · funext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    norm_num
    ring

lemma standardGaussian_density_mul_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma standardGaussian_integrationByParts {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : Measurable F')
    {C D : ℝ} (hb : ∀ x, |F x| ≤ C) (hb' : ∀ x, |F' x| ≤ D) :
    ∫ x, x * F x ∂gaussianReal 0 1 = ∫ x, F' x ∂gaussianReal 0 1 := by
  have hfm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have h1 : Integrable (fun x => gaussianPDFReal 0 1 x * F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb' x)
  have h2 : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * F x) := by
    have hh := standardGaussian_density_mul_integrable.neg.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    simpa only [neg_mul,Pi.neg_apply] using hh
  have h3 : Integrable (fun x => gaussianPDFReal 0 1 x * F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_deriv x) (fun x _ => hF x) h1 h2 h3
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  rw [he]
  simp only [neg_mul,integral_neg,neg_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_integral_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltIntegral μ v F)
      (∫ x, Real.exp (t * v x) * v x * F x ∂μ) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t 1) (bound := fun _ => Real.exp ((|t|+1)*C) * C * D)
    (F' := fun u x => Real.exp (u * v x) * v x * F x) (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hv.const_mul u |>.exp.mul hF).aestronglyMeasurable)
    (tilt_integrable μ hv hF hC hD hvC hFD t)
    (by fun_prop) (ae_of_all _ fun x u hu => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · have hu' : |u| ≤ |t|+1 := by
      have hh : |u-t| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
      calc
        |u| = |(u-t)+t| := by congr 1; ring
        _ ≤ |u-t|+|t| := abs_add_le _ _
        _ ≤ |t|+1 := by linarith
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (u * v x) ≤ Real.exp ((|t|+1)*C) := by
      apply Real.exp_le_exp.mpr
      apply (le_abs_self (u * v x)).trans
      rw [abs_mul]
      exact mul_le_mul hu' (hvC x) (abs_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul hexp (hvC x) (abs_nonneg _) (Real.exp_pos _).le)
      (hFD x) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hC)
  · convert! (((hasDerivAt_id u).mul_const (v x)).exp.mul_const (F x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

lemma tilt_partition_deriv {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    HasDerivAt (tiltPartition μ v) (tiltIntegral μ v v t) t := by
  have hd := tilt_integral_deriv μ (F := fun _ => 1) hv measurable_const hC
    (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) * 1 ∂μ)
    (∫ x, Real.exp (t*v x) * v x * 1 ∂μ) t at hd
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) ∂μ)
    (∫ x, Real.exp (t * v x) * v x ∂μ) t
  simpa only [mul_one] using hd

lemma tilt_mean_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltMean μ v F)
      (tiltMean μ v (fun x => v x * F x) t - tiltMean μ v F t * tiltMean μ v v t) t := by
  have hp := (tilt_partition_pos μ hv hC hvC t).ne'
  have hd := (tilt_integral_deriv μ hv hF hC hD hvC hFD t).div
    (tilt_partition_deriv μ hv hC hvC t) hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [tiltMean,tiltIntegral,mul_assoc]
  field_simp

lemma tilt_mean_bound {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    |tiltMean μ v F t| ≤ D := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi := tilt_integrable μ hv hF hC hD hvC hFD t
  have hiExp : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltMean,abs_div,abs_of_pos hp,div_le_iff₀ hp]
  calc
    |tiltIntegral μ v F t| ≤ ∫ x, |Real.exp (t * v x) * F x| ∂μ := by
      simpa only [tiltIntegral,Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.exp (t * v x) * F x)
    _ ≤ ∫ x, Real.exp (t * v x) * D ∂μ := by
      apply integral_mono_ae hi.norm (hiExp.mul_const D)
      exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hFD x) (Real.exp_pos _).le
    _ = D * tiltPartition μ v t := by rw [integral_mul_const]; exact mul_comm _ _

lemma tilt_mean_continuous {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    Continuous (tiltMean μ v F) :=
  continuous_iff_continuousAt.mpr fun t => (tilt_mean_deriv μ hv hF hC hD hvC hFD t).continuousAt

lemma gaussian_tilt_integrationByParts {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    (∫ t, t * tiltMean μ v F t ∂gaussianReal 0 1) =
      ∫ t, tiltMean μ v (fun x => v x * F x) t -
        tiltMean μ v F t * tiltMean μ v v t ∂gaussianReal 0 1 := by
  have hvF : ∀ x, |v x * F x| ≤ C * D := fun x => by
    rw [abs_mul]; exact mul_le_mul (hvC x) (hFD x) (abs_nonneg _) hC
  apply standardGaussian_integrationByParts
    (fun t => tilt_mean_deriv μ hv hF hC hD hvC hFD t)
    ((tilt_mean_continuous μ hv (hv.mul hF) hC (mul_nonneg hC hD) hvC hvF).measurable.sub
      ((tilt_mean_continuous μ hv hF hC hD hvC hFD).measurable.mul
        (tilt_mean_continuous μ hv hv hC hC hvC hvC).measurable))
    (fun t => tilt_mean_bound μ hv hF hC hD hvC hFD t)
    (D := 2*C*D)
  intro t
  calc
    |tiltMean μ v (fun x => v x * F x) t - tiltMean μ v F t * tiltMean μ v v t| ≤
        |tiltMean μ v (fun x => v x * F x) t| + |tiltMean μ v F t * tiltMean μ v v t| := abs_sub _ _
    _ ≤ C*D + D*C := add_le_add (tilt_mean_bound μ hv (hv.mul hF) hC (mul_nonneg hC hD) hvC hvF t)
      (by
        rw [abs_mul]
        exact mul_le_mul (tilt_mean_bound μ hv hF hC hD hvC hFD t)
          (tilt_mean_bound μ hv hv hC hC hvC hvC t) (abs_nonneg _) hD)
    _ = 2*C*D := by ring

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

lemma replicaPotential_bound {S : Type*} {v : S → ℝ} {C : ℝ}
    (hv : ∀ x, |v x| ≤ C) (n : ℕ) (x : Fin n → S) :
    |replicaPotential v n x| ≤ n*C := by
  calc
    |∑ i, v (x i)| ≤ ∑ i, |v (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, C := Finset.sum_le_sum (fun i _ => hv (x i))
    _ = n*C := by simp

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean {Ω : Type*} [MeasurableSpace Ω]
    {v : Ω → S → ℝ} {F : S → ℝ} (hv : Measurable (Function.uncurry v))
    (hF : Measurable F) : Measurable (fun g => tiltMean μ (v g) F 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hv.exp.mul (hF.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable).div
      hv.exp.stronglyMeasurable.integral_prod_right'.measurable

omit [IsProbabilityMeasure μ] in
lemma tilt_mean_mulObservable {v F : S → ℝ} (c t : ℝ) :
    tiltMean μ v (fun x => c*F x) t = c * tiltMean μ v F t := by
  unfold tiltMean tiltIntegral
  simp_rw [show ∀ x, Real.exp (t*v x)*(c*F x) = c*(Real.exp (t*v x)*F x) by intro; ring]
  rw [integral_const_mul]
  ring

end GaussianField

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianFieldAlgebra
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*}

lemma gaussianTailCoefficient_measurable [MeasurableSpace S] {w : ℕ → S → ℝ}
    (hw : ∀ i, Measurable (w i)) (n i : ℕ) :
    Measurable (gaussianTailCoefficient w n i) := by
  unfold gaussianTailCoefficient
  split_ifs <;> fun_prop

lemma countableGaussianField_add (v w : ℕ → S → ℝ) (L : S → ℕ) (g : ℕ → ℝ) (x : S) :
    countableGaussianField (fun i x => v i x+w i x) L g x =
      countableGaussianField v L g x+countableGaussianField w L g x := by
  simp only [countableGaussianField,gaussianPrefixField,mul_add,Finset.sum_add_distrib]

lemma countableGaussianField_smul (a : ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (x : S) :
    countableGaussianField (fun i x => a*v i x) L g x = a*countableGaussianField v L g x := by
  simp only [countableGaussianField,gaussianPrefixField,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma countableGaussianField_tail (w : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ)
    (g : ℕ → ℝ) (x : S) :
    countableGaussianField (gaussianTailCoefficient w n) L g x =
      countableGaussianField w L g x-truncatedCountableGaussianField w L n g x := by
  rw [truncatedCountableGaussianField_eq]
  unfold countableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun i => g i*gaussianTailCoefficient w n i x) (L x),
    Fin.sum_univ_eq_sum_range (fun i => g i*w i x) (L x),
    Fin.sum_univ_eq_sum_range (fun i => g i*w i x) (min n (L x))]
  have he (i : ℕ) : g i*gaussianTailCoefficient w n i x =
      g i*w i x-(if i<n then g i*w i x else 0) := by
    unfold gaussianTailCoefficient
    by_cases h : i<n
    · rw [ite_eq_right (by omega),ite_eq_left h]
      ring
    · rw [ite_eq_left (by omega),ite_eq_right h]
      ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,sum_range_cutoff,min_comm]

lemma gaussianTailCoefficient_sq_le (w : ℕ → S → ℝ) (n i : ℕ) (x : S) :
    gaussianTailCoefficient w n i x^2 ≤ w i x^2 := by
  unfold gaussianTailCoefficient
  split_ifs <;> simp [sq_nonneg]

lemma gaussianCombinedCoefficient_sq_bound (v w : ℕ → S → ℝ) (L : S → ℕ)
    {D E : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (a b : ℝ) (n : ℕ) (x : S) :
    (∑ i : Fin (L x), (a*v i.val x+b*gaussianTailCoefficient w n i.val x)^2) ≤
      2*a^2*D+2*b^2*E := by
  calc
    _ ≤ ∑ i : Fin (L x), (2*a^2*v i.val x^2+2*b^2*w i.val x^2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := gaussianTailCoefficient_sq_le w n i.val x
      have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*b^2)
      nlinarith [sq_nonneg (a*v i.val x-b*gaussianTailCoefficient w n i.val x)]
    _ = 2*a^2*(∑ i : Fin (L x), v i.val x^2)+
        2*b^2*(∑ i : Fin (L x), w i.val x^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hD x) (by positivity))
      (mul_le_mul_of_nonneg_left (hE x) (by positivity))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

lemma exp_integral_le_of_integrable {H : S → ℝ} (hi : Integrable H μ)
    (he : Integrable (fun x => Real.exp (H x)) μ) :
    Real.exp (∫ x, H x ∂μ) ≤ ∫ x, Real.exp (H x) ∂μ := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => mem_univ _) hi he

lemma inverse_partition_power_le {H : S → ℝ} (hi : Integrable H μ)
    (he : Integrable (fun x => Real.exp (H x)) μ) (k : ℕ)
    (hk : Integrable (fun x => Real.exp (-(k:ℝ)*H x)) μ) :
    (tiltPartition μ H 1)⁻¹^k ≤ ∫ x, Real.exp (-(k:ℝ)*H x) ∂μ := by
  have h1 : Real.exp (∫ x, H x ∂μ) ≤ tiltPartition μ H 1 := by
    simpa only [tiltPartition,one_mul] using exp_integral_le_of_integrable μ hi he
  have h2 : (tiltPartition μ H 1)⁻¹ ≤ (Real.exp (∫ x, H x ∂μ))⁻¹ :=
    inv_anti₀ (Real.exp_pos _) h1
  calc
    _ ≤ ((Real.exp (∫ x, H x ∂μ))⁻¹)^k :=
      pow_le_pow_left₀ (inv_nonneg.mpr (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he)).le) h2 k
    _ = Real.exp (-(k:ℝ)*(∫ x, H x ∂μ)) := by
      rw [← Real.exp_neg,← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (∫ x, -(k:ℝ)*H x ∂μ) := by rw [integral_const_mul]
    _ ≤ _ := exp_integral_le_of_integrable μ (hi.const_mul _) hk

end

lemma abs_le_exp_add_exp_neg (a : ℝ) : |a| ≤ Real.exp a+Real.exp (-a) := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    linarith [Real.add_one_le_exp a,Real.exp_pos (-a)]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    linarith [Real.add_one_le_exp (-a),Real.exp_pos a]

lemma abs_pow_mul_exp_le (h y : ℝ) (k : ℕ) :
    |y|^k*Real.exp h ≤ (k.factorial:ℝ)*(Real.exp (h+y)+Real.exp (h-y)) := by
  have hk : (0:ℝ)<k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : |y|^k ≤ (k.factorial:ℝ)*Real.exp |y| := by
    have hh := Real.pow_div_factorial_le_exp |y| (abs_nonneg y) k
    exact (div_le_iff₀ hk).mp hh |>.trans_eq (mul_comm _ _)
  have h2 : Real.exp |y| ≤ Real.exp y+Real.exp (-y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ ((k.factorial:ℝ)*(Real.exp y+Real.exp (-y)))*Real.exp h :=
      mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 hk.le)) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,add_mul,← Real.exp_add,← Real.exp_add]
      congr 1
      congr 1 <;> congr 1 <;> ring

lemma integrable_of_exp_pos_neg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {H : X → ℝ} (hm : Measurable H)
    (hp : Integrable (fun x => Real.exp (H x)) μ)
    (hn : Integrable (fun x => Real.exp (-H x)) μ) : Integrable H μ := by
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_le_exp_add_exp_neg (H x)

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_mgf_identity {H Y : S → ℝ} (hH : Measurable H) (a : ℝ) :
    mgf Y (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) a =
      tiltPartition μ (fun x => H x+a*Y x) 1 := by
  rw [mgf,integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltPartition,one_mul,Real.exp_add]

omit [IsProbabilityMeasure μ] in
lemma coupling_expSet {H Y : S → ℝ} (hH : Measurable H) (_hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    integrableExpSet Y (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = univ := by
  ext a
  simp only [mem_univ,iff_true,integrableExpSet,mem_ofPred_eq]
  apply (integrable_withDensity_iff_integrable_smul' hH.exp.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,Real.exp_add] using he a

lemma coupling_log_hasDerivAt {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    HasDerivAt (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1))
      (tiltMean μ (fun x => H x+a*Y x) Y 1) a := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hm : a ∈ interior (integrableExpSet Y ρ) := by
    rw [coupling_expSet μ hH hY he,interior_univ]
    trivial
  have hp : 0 < mgf Y ρ a := by
    rw [coupling_mgf_identity μ hH]
    exact tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he a)
  have hd := (hasDerivAt_mgf hm).log hp.ne'
  have hf : (fun b => Real.log (mgf Y ρ b)) =
      (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    rw [coupling_mgf_identity μ hH]
  rw [hf] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [coupling_mgf_identity μ hH]
  unfold tiltMean tiltIntegral
  congr 1
  change _ = ∫ x, Y x*Real.exp (a*Y x) ∂ρ
  rw [integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,one_mul,Real.exp_add]
  ring

lemma coupling_log_second_derivative {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    iteratedDeriv 2 (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) a =
      tiltMean μ (fun x => H x+a*Y x)
        (fun x => (Y x-tiltMean μ (fun x => H x+a*Y x) Y 1)^2) 1 := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hm : a ∈ interior (integrableExpSet Y ρ) := by
    rw [coupling_expSet μ hH hY he,interior_univ]
    trivial
  have hf : cgf Y ρ = (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    exact congrArg Real.log (coupling_mgf_identity μ hH b)
  have hd : deriv (cgf Y ρ) a = tiltMean μ (fun x => H x+a*Y x) Y 1 := by
    rw [hf]
    exact (coupling_log_hasDerivAt μ hH hY he a).deriv
  rw [← hf,iteratedDeriv_two_cgf_eq_integral hm,hd,coupling_mgf_identity μ hH]
  unfold tiltMean tiltIntegral
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hH.exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,one_mul,Real.exp_add]
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] in
lemma vectorEnergy_bound {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (x : E) (s : S) : |W s + V s x| ≤ K+C*‖x‖ := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hW s)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_integrable (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    Integrable (fun s => Real.exp (W s + V s x)) ρ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (K+C*‖x‖)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound hW hV x s))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_pos (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    0 < vectorPartition ρ W V x := by
  apply integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
    (vectorPartition_integrable ρ hWm hVm hW hV x) |>.mpr
  simp [Function.support,Real.exp_ne_zero]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_FiniteTerminal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial

open scoped ContDiff

lemma canonicalRadialMass_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    canonicalRadialMass n b A = ENNReal.ofReal (∫ x in A, canonicalRadialDensity n b x) := by
  rw [canonicalRadialMass,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb).integrableOn
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le)).symm

lemma canonicalRadial_mass_le {n : ℕ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    canonicalRadialMass n a A ≤ ENNReal.ofReal (Real.exp c * b ^ (-((n+1 : ℕ) : ℝ)/2)) := by
  rw [canonicalRadialMass_apply ha hA]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x in A, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_mono_on (canonicalRadialDensity_integrable n ha).integrableOn
        ((canonicalRadialDensity_integrable n hb).const_mul _).integrableOn hA
      intro x hx
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ ∫ x, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_le_integral ((canonicalRadialDensity_integrable n hb).const_mul _)
      exact Eventually.of_forall fun x => (mul_pos (Real.exp_pos c) (canonicalRadialDensity_pos n b x)).le
    _ = _ := by rw [integral_const_mul,canonicalRadialDensity_integral n hb]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NormSquareBand
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma canonicalRadial_upper_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    canonicalRadialMass n 1 {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1+ε := by linarith
  have hb : 0 ≤ 1-(1+ε)⁻¹ := by
    apply sub_nonneg.mpr
    exact (inv_le_one₀ hd).mpr (by linarith)
  have hid : (1-(1+ε)⁻¹)*(1+ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1+ε)⁻¹)
    (A := {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2})
    (c := -((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : (1-(1+ε)⁻¹)*(((n+1 : ℕ) : ℝ)*(1+ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*((1-(1+ε)⁻¹)*(1+ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

lemma canonicalRadial_lower_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)} ≤
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1-ε := sub_pos.mpr hε1
  have hb : 0 ≤ (1-ε)⁻¹-1 := by
    apply sub_nonneg.mpr
    exact (one_le_inv₀ hd).mpr (by linarith)
  have hid : ((1-ε)⁻¹-1)*(1-ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1-ε)⁻¹)
    (A := {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)})
    (c := ((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : ((1-ε)⁻¹-1)*(((n+1 : ℕ) : ℝ)*(1-ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*(((1-ε)⁻¹-1)*(1-ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

lemma normSquareBand_measurable (n : ℕ) (ε : ℝ) : MeasurableSet (normSquareBand n ε) :=
  (measurableSet_le measurable_const (continuous_norm.pow 2).measurable).inter
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)

lemma canonicalRadial_band_compl_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 (normSquareBand n ε)ᶜ ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ)))+
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  calc
    _ ≤ canonicalRadialMass n 1
        ({x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ∪ {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)}) :=
      measure_mono (by
        intro x hx
        change ¬ (_ ∧ _) at hx
        rcases not_and_or.mp hx with h | h
        · exact Or.inr (le_of_not_ge h)
        · exact Or.inl (le_of_not_ge h))
    _ ≤ _ := (measure_union_le _ _).trans
      (add_le_add (canonicalRadial_upper_tail n hε) (canonicalRadial_lower_tail n hε hε1))

lemma exp_neg_mul_nat_succ_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

lemma canonicalRadial_band_eventually_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε) := by
  have hu : 0 < (ε-Real.log (1+ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1+ε) (by linarith : 1+ε ≠ 1)
    linarith
  have hl : 0 < (-ε-Real.log (1-ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1-ε) (by linarith : 1-ε ≠ 1)
    linarith
  have ht := (exp_neg_mul_nat_succ_tendsto hu).add (exp_neg_mul_nat_succ_tendsto hl)
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))+
      Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ)) < 1/2 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)+0 < 1/2))
  filter_upwards [hev] with n hn
  have h := canonicalRadial_band_compl_le n hε hε1
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  change (canonicalRadialMass n 1).real (normSquareBand n ε)ᶜ ≤ _ at h'
  rw [measureReal_compl (normSquareBand_measurable n ε), probReal_univ] at h'
  linarith

lemma canonicalRadialMass_real_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    (canonicalRadialMass n b).real A = ∫ x in A, canonicalRadialDensity n b x := by
  rw [Measure.real,canonicalRadialMass_apply hb hA,ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => (canonicalRadialDensity_pos n b x).le

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

lemma finiteGaussianRow_field {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (g : ℕ → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), g i.val*finiteGaussianRow key a i.val) =
      ∑ k, g (key k)*a k :=
  finiteGaussianRow_sum hk a (fun i x => g i*x) (fun _ => mul_zero _)

lemma finiteGaussianRow_norm {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), finiteGaussianRow key a i.val^2) = ∑ k, a k^2 :=
  finiteGaussianRow_sum hk a (fun _ x => x^2) (fun _ => by norm_num)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma perturbationWeight_eq (j : ℕ) : (2:ℝ)^(-((j+1:ℕ):ℤ))=(1/2:ℝ)^(j+1) := by
  simp only [zpow_neg,zpow_natCast,one_div,inv_pow]

lemma half_power_sum_le_one (N : ℕ) : (∑ j : Fin N, (1/2:ℝ)^(j.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (1/2:ℝ)^(j+1)) N]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [sum_geometric_two_le N]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBoltzmann
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma integrable_prod_of_nonneg_uniform_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [SFinite ν] {F : X×Y → ℝ} {C : ℝ}
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hi : ∀ x, Integrable (fun y => F (x,y)) ν)
    (hb : ∀ x, (∫ y, F (x,y) ∂ν) ≤ C) : Integrable F (μ.prod ν) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  apply (integrable_const C).mono' hF.aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_of_nonneg (hpos _)]
    rw [abs_of_nonneg (integral_nonneg fun y => hpos (x,y))]
    exact hb x

end
variable {S : Type*} [MeasurableSpace S]

lemma countableGaussianHamiltonian_measurable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianHamiltonian W v L)) :=
  (hW.comp measurable_snd).add (countableGaussianField_measurable hv hL)

variable (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L)
variable {A D : ℝ} (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)

omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integrable (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*countableGaussianHamiltonian W v L g x)) countableGaussianLaw := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add]
  exact (countableGaussianField_exp_integrable v L x t).const_mul _

include hA hD in
omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integral_bound (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw) ≤
      Real.exp (|t| * A+t^2*D/2) := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add,integral_const_mul]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t))
  · exact countableGaussianField_exp_integral_le v L hD x t
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · exact (Real.exp_pos _).le

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_exp_joint_integrable (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1))
      (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap).const_mul t).exp
    (fun _ => (Real.exp_pos _).le)
    (fun x => countableGaussianHamiltonian_exp_integrable x t)
  exact fun x => countableGaussianHamiltonian_exp_integral_bound hA hD x t

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_joint_integrable :
    Integrable (fun p : S×(ℕ → ℝ) => countableGaussianHamiltonian W v L p.2 p.1)
      (μ.prod countableGaussianLaw) := by
  apply integrable_of_exp_pos_neg _ ((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap)
  · simpa only [one_mul,Function.comp_def,Function.uncurry,Prod.swap] using countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1
  · simpa only [neg_one_mul,Function.comp_def,Function.uncurry,Prod.swap] using countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD (-1)

include hW hv hL in
lemma gaussianHamiltonianPartition_measurable :
    Measurable (fun g => tiltPartition μ (countableGaussianHamiltonian W v L g) 1) := by
  simpa only [tiltPartition,one_mul,Function.uncurry_apply_pair] using
    (countableGaussianHamiltonian_measurable hW hv hL).exp.stronglyMeasurable.integral_prod_right'.measurable

include hW hv hL hA hD in
lemma gaussianHamiltonianPartition_pos_ae :
    ∀ᵐ g ∂countableGaussianLaw, 0 < tiltPartition μ (countableGaussianHamiltonian W v L g) 1 := by
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae] with g hg
  exact tilt_partition_pos_of_integrable μ hg

include hW hv hL hA hD in
lemma gaussianHamiltonianPartition_inverse_power_integrable (k : ℕ) :
    Integrable (fun g => (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^k)
      countableGaussianLaw := by
  have hh := countableGaussianHamiltonian_joint_integrable μ hW hv hL hA hD
  have h1 := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1
  have hk := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD (-(k:ℝ))
  refine hk.integral_prod_right.mono'
    ((gaussianHamiltonianPartition_measurable μ hW hv hL).inv.pow_const k).aestronglyMeasurable ?_
  filter_upwards [hh.prod_left_ae,h1.prod_left_ae,hk.prod_left_ae,
    gaussianHamiltonianPartition_pos_ae μ hW hv hL hA hD] with g hgi hg1 hgk hgp
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hgp.le) k)]
  exact inverse_partition_power_le μ hgi (by simpa only [one_mul] using hg1) k hgk

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_sq_prefix (v : ℕ → S → ℝ) (L : S → ℕ) (n : ℕ) (x : S) :
    (∑ i : Fin n, maskedGaussianCoefficient v L i.val x^2) =
      ∑ i : Fin (min n (L x)), v i.val x^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient v L i x^2) n,
    Fin.sum_univ_eq_sum_range (fun i => v i x^2) (min n (L x))]
  have he (i : ℕ) : maskedGaussianCoefficient v L i x^2 = if i<L x then v i x^2 else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp
  simp_rw [he]
  exact sum_range_cutoff _ n (L x)

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_sq_bound (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (n : ℕ) (x : S) :
    (∑ i : Fin n, maskedGaussianCoefficient v L i.val x^2) ≤ D := by
  rw [maskedGaussianCoefficient_sq_prefix]
  exact (gaussianCoefficient_prefix_sq_le v L n x).trans (hD x)

lemma gaussianPrefixCovariance_measurable {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i)) (hL : Measurable L) (n : ℕ) :
    Measurable (Function.uncurry (gaussianPrefixCovariance v w L n)) := by
  unfold gaussianPrefixCovariance Function.uncurry
  exact Finset.measurable_sum _ fun i _ =>
    ((maskedGaussianCoefficient_measurable hw hL i.val).comp measurable_fst).mul
      ((maskedGaussianCoefficient_measurable hv hL i.val).comp measurable_snd)

lemma countableGaussianCovariance_measurable {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianCovariance v w L)) := by
  have hm : Measurable (fun p : ℕ×(S×S) => gaussianPrefixCovariance v w L p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_right
    exact gaussianPrefixCovariance_measurable hv hw hL
  exact hm.comp ((hL.comp measurable_fst).prodMk measurable_id)

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_bound (v w : ℕ → S → ℝ) (L : S → ℕ)
    {D E : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E) (n : ℕ) (x y : S) :
    |gaussianPrefixCovariance v w L n x y| ≤ (D+E)/2 := by
  have hi (i : Fin n) : |maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y| ≤
      (maskedGaussianCoefficient w L i.val x^2+maskedGaussianCoefficient v L i.val y^2)/2 := by
    rw [abs_mul]
    nlinarith [sq_abs (maskedGaussianCoefficient w L i.val x),
      sq_abs (maskedGaussianCoefficient v L i.val y),
      sq_nonneg (|maskedGaussianCoefficient w L i.val x|-|maskedGaussianCoefficient v L i.val y|)]
  calc
    _ ≤ ∑ i : Fin n, |maskedGaussianCoefficient w L i.val x*maskedGaussianCoefficient v L i.val y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, (maskedGaussianCoefficient w L i.val x^2+maskedGaussianCoefficient v L i.val y^2)/2 :=
      Finset.sum_le_sum fun i _ => hi i
    _ ≤ _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      linarith [maskedGaussianCoefficient_sq_bound v L hD n y,maskedGaussianCoefficient_sq_bound w L hE n x]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_GibbsReplicaMean
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replicaMean_measurable {Ω : Type*} [MeasurableSpace Ω] {H : Ω → S → ℝ}
    {n : ℕ} {G : (Fin n → S) → ℝ} (hH : Measurable (Function.uncurry H))
    (hG : Measurable G) : Measurable (fun ω => gibbsReplicaMean μ (H ω) n G) := by
  apply measurable_tiltMean _ _ hG
  change Measurable (fun p : Ω×(Fin n → S) => ∑ i, H p.1 (p.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

omit [IsProbabilityMeasure μ] in
lemma replicaMean_const_mul {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ} (c : ℝ) :
    gibbsReplicaMean μ H n (fun x => c*G x) = c*gibbsReplicaMean μ H n G :=
  tilt_mean_mulObservable _ c 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_VarianceProdMemLp
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_bound {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    |vectorLogPartition ρ W V x| ≤ K+C*‖x‖ := by
  have hh := abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (show Integrable (fun _ : S => Real.exp 0) ρ by simp)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (show 0 < ∫ _ : S, Real.exp 0 ∂ρ by simp)
    (c := K+C*‖x‖) (fun s => by simpa using vectorEnergy_bound hW hV x s)
  simpa [vectorLogPartition,vectorPartition] using hh

end

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean_param {Ω : Type*} [MeasurableSpace Ω] {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => tiltMean μ (H ω) (Y ω) 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hH.exp.mul hY).stronglyMeasurable.integral_prod_right'.measurable).div
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LocalMaxSecondDerivNonpos
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_log_partition_bound {H : S → ℝ} (hH : Measurable H)
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) :
    |Real.log (tiltPartition μ H 1)| ≤ A := by
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hi : Integrable (fun x => Real.exp (H x)) μ := by
    simpa only [one_mul,mul_one] using tilt_integrable μ (F := fun _ => 1) hH measurable_const hA (by norm_num : (0:ℝ) ≤ 1) hHA (fun _ => by norm_num) 1
  have hlo : Real.exp (-A) ≤ tiltPartition μ H 1 := by
    calc
      _ = ∫ _ : S, Real.exp (-A) ∂μ := by simp
      _ ≤ _ := by simpa only [tiltPartition,one_mul] using integral_mono (integrable_const _) hi (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).1)
  have hhi : tiltPartition μ H 1 ≤ Real.exp A := by
    calc
      _ ≤ ∫ _ : S, Real.exp A ∂μ := by simpa only [tiltPartition,one_mul] using integral_mono hi (integrable_const _) (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).2)
      _ = _ := by simp
  exact abs_le.mpr ⟨by simpa using Real.log_le_log (Real.exp_pos (-A)) hlo,by simpa using Real.log_le_log hp hhi⟩

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltMeanCenteredAbsSq
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma tiltMean_nonneg {H F : S → ℝ} (hF : ∀ x, 0 ≤ F x) (t : ℝ) : 0 ≤ tiltMean μ H F t := by
  exact div_nonneg (integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (hF x))
    (integral_nonneg fun _ => (Real.exp_pos _).le)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingAffine
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma coupling_log_contDiff {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    ContDiff ℝ 2 (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hf : cgf Y ρ = (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    exact congrArg Real.log (coupling_mgf_identity μ hH b)
  rw [← hf,contDiff_iff_contDiffAt]
  intro a
  apply AnalyticAt.contDiffAt
  apply analyticAt_cgf
  rw [coupling_expSet μ hH hY he,interior_univ]
  trivial

lemma coupling_log_convex {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    ConvexOn ℝ univ (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
  have hs := coupling_log_contDiff μ hH hY he
  apply convexOn_of_deriv2_nonneg' convex_univ
    (hs.differentiable (by norm_num)).differentiableOn
    ( (ContDiff.deriv' (n := 1) hs).differentiable (by norm_num)).differentiableOn
  intro a _
  rw [← iteratedDeriv_eq_iterate,coupling_log_second_derivative μ hH hY he]
  exact tiltMean_nonneg μ (fun _ => sq_nonneg _) 1

lemma convex_derivative_local_bound {F D : ℝ → ℝ}
    (hc : ConvexOn ℝ univ F) (hd : ∀ x, HasDerivAt F (D x) x) (u v : ℝ)
    (hv : v ∈ Ioo (u-1) (u+1)) :
    |D v| ≤ |F (u-2)|+|F (u-1)|+|F (u+1)|+|F (u+2)| := by
  have hmono : Monotone D := by
    intro x y hxy
    simpa only [(hd x).deriv,(hd y).deriv] using
      hc.monotoneOn_deriv (fun x _ => (hd x).differentiableAt) (mem_univ x) (mem_univ y) hxy
  have hl := hc.slope_le_of_hasDerivAt (mem_univ (u-2)) (mem_univ (u-1))
    (by linarith : u-2 < u-1) (hd (u-1))
  have hr := hc.le_slope_of_hasDerivAt (mem_univ (u+1)) (mem_univ (u+2))
    (by linarith : u+1 < u+2) (hd (u+1))
  have hl' : F (u-1)-F (u-2) ≤ D v := by
    have hh : (u-1)-(u-2) = (1:ℝ) := by ring
    simp only [slope,hh,inv_one,one_smul] at hl
    exact hl.trans (hmono hv.1.le)
  have hr' : D v ≤ F (u+2)-F (u+1) := by
    have hh : (u+2)-(u+1) = (1:ℝ) := by ring
    simp only [slope,hh,inv_one,one_smul] at hr
    exact (hmono hv.2.le).trans hr
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (F (u-1)),le_abs_self (F (u-2)),abs_nonneg (F (u+1)),abs_nonneg (F (u+2))]
  · linarith [le_abs_self (F (u+2)),neg_abs_le (F (u+1)),abs_nonneg (F (u-1)),abs_nonneg (F (u-2))]

lemma annealed_convex_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F D : ℝ → Ω → ℝ} (hF : ∀ t, AEStronglyMeasurable (F t) P)
    (hD : ∀ t, AEStronglyMeasurable (D t) P) (hi : ∀ t, Integrable (F t) P)
    (hc : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun t => F t ω) ∧ ∀ t, HasDerivAt (fun t => F t ω) (D t ω) t)
    (u : ℝ) :
    Integrable (D u) P ∧ HasDerivAt (fun t => ∫ ω, F t ω ∂P) (∫ ω, D u ω ∂P) u := by
  let B : Ω → ℝ := fun ω => |F (u-2) ω|+|F (u-1) ω|+|F (u+1) ω|+|F (u+2) ω|
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : u-1 < u) (by linarith : u < u+1))
    (Eventually.of_forall hF) (hi u) (hD u)
  · filter_upwards [hc] with ω hω t ht
    rw [Real.norm_eq_abs]
    exact convex_derivative_local_bound hω.1 hω.2 u t ht
  · exact (((hi (u-2)).abs.add (hi (u-1)).abs).add (hi (u+1)).abs).add (hi (u+2)).abs
  · filter_upwards [hc] with ω hω t _
    exact hω.2 t

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_GaussianHamiltonianCoordinates
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma countableGaussianField_update (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (i : ℕ) (t : ℝ) (x : S) :
    countableGaussianField v L (Function.update g i t) x =
      countableGaussianField v L (Function.update g i 0) x+t*maskedGaussianCoefficient v L i x := by
  unfold countableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun j => Function.update g i t j*v j x) (L x),
    Fin.sum_univ_eq_sum_range (fun j => Function.update g i 0 j*v j x) (L x)]
  have he (j : ℕ) : Function.update g i t j*v j x =
      Function.update g i 0 j*v j x+if j=i then t*v i x else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self,ite_true,zero_mul,zero_add]
    · simp only [Function.update_of_ne hj,ite_eq_right hj,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range,maskedGaussianCoefficient]
  split_ifs <;> simp

omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_update (W : S → ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (i : ℕ) (t : ℝ) (x : S) :
    countableGaussianHamiltonian W v L (Function.update g i t) x =
      countableGaussianHamiltonian W v L (Function.update g i 0) x+t*maskedGaussianCoefficient v L i x := by
  unfold countableGaussianHamiltonian
  conv_lhs => rw [countableGaussianField_update]
  ring

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_bound (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (i : ℕ) (x : S) :
    |maskedGaussianCoefficient v L i x| ≤ Real.sqrt D := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · apply Real.abs_le_sqrt
    exact (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (v j.val x))
      (Finset.mem_univ (⟨i,hi⟩ : Fin (L x)))).trans (hD x)
  · simpa only [abs_zero] using Real.sqrt_nonneg D

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_mean_twice_of_integrable {v w F : S → ℝ} (hw : Measurable w)
    {s : ℝ} (hi : Integrable (fun x => Real.exp (s*w x)) μ) (t : ℝ) :
    tiltMean (tiltLaw μ w s) v F t = tiltMean μ (fun x => s*w x+t*v x) F 1 := by
  let := tilt_law_probability_of_integrable μ hi
  have hp := (tilt_partition_pos_of_integrable μ hi).ne'
  unfold tiltMean tiltIntegral tiltPartition
  rw [tilt_law_integral_of_integrable μ hw hi,tilt_law_integral_of_integrable μ hw hi]
  simp only [tiltMean,tiltIntegral,one_mul,Real.exp_add]
  have he (x : S) : Real.exp (s*w x) * (Real.exp (t*v x)*F x) =
      Real.exp (s*w x) * Real.exp (t*v x) * F x := by ring
  simp_rw [he]
  change ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) * F x ∂μ) / tiltPartition μ w s) /
    ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) ∂μ) / tiltPartition μ w s) = _
  rw [div_div_div_cancel_right₀ hp]

lemma tiltMean_bound_general {H F : S → ℝ} (hH : Measurable H) (hF : Measurable F)
    {t C : ℝ} (hC : 0 ≤ C) (hFC : ∀ x, |F x| ≤ C) :
    |tiltMean μ H F t| ≤ C := by
  by_cases hi : Integrable (fun x => Real.exp (t*H x)) μ
  · exact tiltMean_bound_of_integrable μ hH hF hi hFC
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,abs_zero]
    exact hC

lemma replica_exp_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    Integrable (fun x : Fin n → S => Real.exp (t*replicaPotential H n x))
      (Measure.pi fun _ : Fin n => μ) := by
  simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  exact Integrable.fintype_prod (fun _ => hi)

omit [IsProbabilityMeasure μ] in
lemma tilt_law_apply_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ H t s = (ENNReal.ofReal (tiltPartition μ H t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * H x) ∂μ) := by
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi_of_integrable {H : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ H t) := by
  let := tilt_law_probability_of_integrable μ hi
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply_of_integrable _ (replica_exp_integrable μ hi n) (MeasurableSet.univ_pi hs),
    replica_partition μ hH n,ENNReal.ofReal_pow (tilt_partition_pos_of_integrable μ hi).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential H n x) =
      ∏ i, Real.exp (t * H (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * H x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply_of_integrable μ hi (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma gibbsReplicaMean_integral_of_integrable {H : S → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (G : (Fin n → S) → ℝ) :
    gibbsReplicaMean μ H n G = ∫ x, G x ∂Measure.pi (fun _ : Fin n => tiltLaw μ H 1) := by
  rw [← tilt_law_pi_of_integrable μ hH (by simpa only [one_mul] using hi),
    tilt_law_integral_of_integrable _ (replicaPotential_measurable hH n)
      (replica_exp_integrable μ (by simpa only [one_mul] using hi) n)]
  rfl

lemma gibbsReplicaMean_coordinate_of_integrable {H F : S → ℝ}
    (hH : Measurable H) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (j : Fin n) :
    gibbsReplicaMean μ H n (fun x => F (x j)) = tiltMean μ H F 1 := by
  have heI : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ heI
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi,
    ← tilt_law_integral_of_integrable μ hH heI]
  have he := measurePreserving_eval (fun _ : Fin n => tiltLaw μ H 1) j
  conv_rhs => rw [← he.map_eq,integral_map he.measurable.aemeasurable hF.aestronglyMeasurable]

lemma gibbsReplicaMean_sum_of_integrable {ι : Type*} (s : Finset ι)
    {H : S → ℝ} {n : ℕ} {G : ι → (Fin n → S) → ℝ}
    (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (hG : ∀ i ∈ s, Measurable (G i)) {D : ι → ℝ}
    (hGD : ∀ i ∈ s, ∀ x, |G i x| ≤ D i) :
    gibbsReplicaMean μ H n (fun x => ∑ i ∈ s, G i x) =
      ∑ i ∈ s, gibbsReplicaMean μ H n (G i) := by
  let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H x)) μ)
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  exact integral_finsetSum s fun i hi => Integrable.of_bound (hG i hi).aestronglyMeasurable
    (D i) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGD i hi x)

lemma gibbsReplicaMean_potential_of_integrable {H F : S → ℝ}
    (hH : Measurable H) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {D : ℝ} (hFD : ∀ x, |F x| ≤ D) (n : ℕ) :
    gibbsReplicaMean μ H n (replicaPotential F n) = n*tiltMean μ H F 1 := by
  change gibbsReplicaMean μ H n (fun x => ∑ i, F (x i)) = _
  rw [gibbsReplicaMean_sum_of_integrable μ Finset.univ (G := fun i (x : Fin n → S) => F (x i)) hH hi
    (fun i _ => hF.comp (measurable_pi_apply i)) (fun i _ x => hFD (x i))]
  simp_rw [gibbsReplicaMean_coordinate_of_integrable μ hH hF hi]
  simp

lemma gibbsReplicaMean_product_of_integrable {H F : S → ℝ} {n : ℕ}
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hG : Measurable G)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {D B : ℝ}
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) :
    gibbsReplicaMean μ H (n+1) (fun x => F (x 0)*G (fun j => x j.succ)) =
      tiltMean μ H F 1*gibbsReplicaMean μ H n G := by
  have heI : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ heI
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  rw [← tilt_law_integral_of_integrable μ hH heI]
  let ν := tiltLaw μ H 1
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0)*G (fun j => x j.succ))]
  change (∫ p : S×(Fin n → S), F ((Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) 0)*
    G (fun j => (Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) j.succ)
      ∂ν.prod (Measure.pi fun _ => ν)) = _
  simp only [Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable D
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD x)
  have hGi : Integrable G (Measure.pi fun _ : Fin n => ν) := Integrable.of_bound
    hG.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGB x)
  rw [integral_prod _ (hFi.mul_prod hGi)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableGaussianResampling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma resampleGaussianCoordinate_measurable (i : ℕ) :
    Measurable (resampleGaussianCoordinate i) := by
  unfold resampleGaussianCoordinate
  fun_prop

lemma resampleGaussianCoordinate_measurePreserving (i : ℕ) :
    MeasurePreserving (resampleGaussianCoordinate i)
      ((gaussianReal 0 1).prod countableGaussianLaw) countableGaussianLaw := by
  refine ⟨resampleGaussianCoordinate_measurable i,?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (resampleGaussianCoordinate_measurable i)
    (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
  classical
  by_cases hi : i ∈ s
  · have he : (resampleGaussianCoordinate i) ⁻¹' Set.pi s t =
        t i ×ˢ Set.pi (s.erase i) t := by
      ext p
      simp only [mem_preimage,mem_prod,Set.mem_pi,Finset.mem_coe,resampleGaussianCoordinate]
      constructor
      · intro hp
        refine ⟨?_,fun j hj => ?_⟩
        · simpa only [Function.update_self] using hp i hi
        · simpa only [Function.update_of_ne (Finset.mem_erase.mp hj).1] using
            hp j (Finset.mem_of_mem_erase hj)
      · rintro ⟨hp,hq⟩ j hj
        by_cases he : j=i
        · subst j
          simpa only [Function.update_self] using hp
        · simpa only [Function.update_of_ne he] using hq j (Finset.mem_erase.mpr ⟨he,hj⟩)
    rw [he,Measure.prod_prod,countableGaussianLaw,Measure.infinitePi_pi _ (fun j _ => ht j)]
    exact Finset.mul_prod_erase s (fun j => gaussianReal 0 1 (t j)) hi
  · have he : (resampleGaussianCoordinate i) ⁻¹' Set.pi s t =
        Set.univ ×ˢ Set.pi s t := by
      ext p
      simp only [mem_preimage,mem_prod,true_and,mem_univ,Set.mem_pi,Finset.mem_coe,resampleGaussianCoordinate]
      constructor <;> intro hp j hj
      · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hp j hj
      · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using hp j hj
    rw [he,Measure.prod_prod,measure_univ,one_mul,countableGaussianLaw,
      Measure.infinitePi_pi _ (fun j _ => ht j)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableGaussianIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma countableGaussian_affine_zero_exp_integrable (i : ℕ)
    {H : (ℕ → ℝ) → S → ℝ} {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hvC : ∀ x, |v x| ≤ C)
    (haff : ∀ g t x, H (Function.update g i t) x = H (Function.update g i 0) x+t*v x)
    (hi : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ) :
    ∀ᵐ g ∂countableGaussianLaw,
      Integrable (fun x => Real.exp (H (Function.update g i 0) x)) μ := by
  have hp := (resampleGaussianCoordinate_measurePreserving i).quasiMeasurePreserving.ae hi
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with g hg
  obtain ⟨t,ht⟩ := hg.exists
  change Integrable (fun x => Real.exp (H (Function.update g i t) x)) μ at ht
  have hb (x) : ‖Real.exp (-t*v x)‖ ≤ Real.exp (|t| * C) := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      rw [abs_mul,abs_neg]
      exact mul_le_mul_of_nonneg_left (hvC x) (abs_nonneg t))
  have hh := ht.mul_bdd ((hv.const_mul (-t)).exp.aestronglyMeasurable)
    (ae_of_all _ hb)
  apply hh.congr
  exact ae_of_all _ fun x => by
    dsimp only
    rw [← Real.exp_add,haff]
    congr 1
    ring

lemma countableGaussian_coordinate_tilt_ibp (i : ℕ)
    {H : (ℕ → ℝ) → S → ℝ} {v F : S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D)
    (haff : ∀ g t x, H (Function.update g i t) x = H (Function.update g i 0) x+t*v x)
    (hi0 : ∀ᵐ g ∂countableGaussianLaw,
      Integrable (fun x => Real.exp (H (Function.update g i 0) x)) μ) :
    (∫ g, g i*tiltMean μ (H g) F 1 ∂countableGaussianLaw) =
      ∫ g, tiltMean μ (H g) (fun x => v x*F x) 1-
        tiltMean μ (H g) F 1*tiltMean μ (H g) v 1 ∂countableGaussianLaw := by
  let R (g : ℕ → ℝ) := tiltMean μ (H g) (fun x => v x*F x) 1-
    tiltMean μ (H g) F 1*tiltMean μ (H g) v 1
  have hm (K : S → ℝ) (hK : Measurable K) := measurable_tiltMean μ hH hK
  have hHg (g) : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  have hb (K : S → ℝ) (hK : Measurable K) {B : ℝ} (hB : 0 ≤ B)
      (hKB : ∀ x, |K x| ≤ B) (g) : |tiltMean μ (H g) K 1| ≤ B :=
    tiltMean_bound_general μ (hHg g) hK hB hKB
  have hvF (x : S) : |v x*F x| ≤ C*D := by
    rw [abs_mul]
    exact mul_le_mul (hvC x) (hFD x) (abs_nonneg _) hC
  have hRm : Measurable R := (hm _ (hv.mul hF)).sub ((hm _ hF).mul (hm _ hv))
  have hRb (g) : |R g| ≤ 2*C*D := by
    calc
      _ ≤ |tiltMean μ (H g) (fun x => v x*F x) 1|+
          |tiltMean μ (H g) F 1*tiltMean μ (H g) v 1| := abs_sub _ _
      _ ≤ C*D+D*C := add_le_add (hb _ (hv.mul hF) (mul_nonneg hC hD) hvF g) (by
        rw [abs_mul]
        exact mul_le_mul (hb _ hF hD hFD g) (hb _ hv hC hvC g) (abs_nonneg _) hD)
      _ = _ := by ring
  let e := resampleGaussianCoordinate i
  have he := resampleGaussianCoordinate_measurePreserving i
  have intmap (K : (ℕ → ℝ) → ℝ) (hK : Measurable K) :
      (∫ p, K (e p) ∂(gaussianReal 0 1).prod countableGaussianLaw) = ∫ g, K g ∂countableGaussianLaw := by
    simpa only [he.map_eq] using
      (integral_map (μ := (gaussianReal 0 1).prod countableGaussianLaw) he.measurable.aemeasurable hK.aestronglyMeasurable).symm
  have hmF : Measurable (fun p : ℝ×(ℕ → ℝ) => tiltMean μ (H (e p)) F 1) :=
    (hm _ hF).comp he.measurable
  have hiF : Integrable (fun p : ℝ×(ℕ → ℝ) => p.1*tiltMean μ (H (e p)) F 1)
      ((gaussianReal 0 1).prod countableGaussianLaw) := by
    apply ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst countableGaussianLaw |>.mul_bdd
      hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb _ hF hD hFD (e p)
  have hiR : Integrable (fun p => R (e p)) ((gaussianReal 0 1).prod countableGaussianLaw) :=
    Integrable.of_bound (hRm.comp he.measurable).aestronglyMeasurable (2*C*D)
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hRb (e p))
  change (∫ g, g i*tiltMean μ (H g) F 1 ∂countableGaussianLaw) = ∫ g, R g ∂countableGaussianLaw
  rw [← intmap (fun g => g i*tiltMean μ (H g) F 1) ((measurable_pi_apply i).mul (hm _ hF)),← intmap _ hRm]
  simp only [e,resampleGaussianCoordinate,Function.update_self]
  change (∫ p, p.1*tiltMean μ (H (e p)) F 1 ∂(gaussianReal 0 1).prod countableGaussianLaw) =
    ∫ p, R (e p) ∂(gaussianReal 0 1).prod countableGaussianLaw
  rw [integral_prod_symm _ hiF,integral_prod_symm _ hiR]
  apply integral_congr_ae
  filter_upwards [hi0] with g hg
  let w : S → ℝ := H (Function.update g i 0)
  have hwm : Measurable w := hHg _
  have hwI : Integrable (fun x => Real.exp (1*w x)) μ := by simpa only [one_mul] using hg
  let := tilt_law_probability_of_integrable μ hwI
  have heK (K : S → ℝ) (u : ℝ) : tiltMean (tiltLaw μ w 1) v K u =
      tiltMean μ (H (Function.update g i u)) K 1 := by
    rw [tilt_mean_twice_of_integrable μ hwm hwI u]
    congr 2
    funext x
    simp only [one_mul]
    exact (haff g u x).symm
  have hh := gaussian_tilt_integrationByParts (tiltLaw μ w 1) hv hF hC hD hvC hFD
  simp_rw [heK] at hh
  exact hh

lemma countableGaussian_coordinate_tilt_ibp_of_exp_integrable (i : ℕ)
    {H : (ℕ → ℝ) → S → ℝ} {v F : S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D)
    (haff : ∀ g t x, H (Function.update g i t) x = H (Function.update g i 0) x+t*v x)
    (hi : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ) :
    (∫ g, g i*tiltMean μ (H g) F 1 ∂countableGaussianLaw) =
      ∫ g, tiltMean μ (H g) (fun x => v x*F x) 1-
        tiltMean μ (H g) F 1*tiltMean μ (H g) v 1 ∂countableGaussianLaw :=
  countableGaussian_coordinate_tilt_ibp μ i hH hv hF hC hD hvC hFD haff
    (countableGaussian_affine_zero_exp_integrable μ i hv hvC haff hi)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_CountableGaussianReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma countableGaussian_replica_coordinate_ibp (i n : ℕ)
    {H : (ℕ → ℝ) → S → ℝ} {v : S → ℝ} {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hv : Measurable v) (hG : Measurable G)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hGD : ∀ x, |G x| ≤ D)
    (haff : ∀ g t x, H (Function.update g i t) x = H (Function.update g i 0) x+t*v x)
    (hi : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ) :
    (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
      ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential v n x*G x)-
        n*gibbsReplicaMean μ (H g) (n+1) (fun x => v (x 0)*G (fun l => x l.succ))
        ∂countableGaussianLaw := by
  let Hr (g : ℕ → ℝ) := replicaPotential (H g) n
  have hHr : Measurable (Function.uncurry Hr) := by
    change Measurable (fun p : (ℕ → ℝ)×(Fin n → S) => ∑ l, H p.1 (p.2 l))
    exact Finset.measurable_sum _ fun l _ => hH.comp
      (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hvr := replicaPotential_measurable hv n
  have hir : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (Hr g x))
      (Measure.pi fun _ : Fin n => μ) := by
    filter_upwards [hi] with g hg
    simpa only [one_mul] using replica_exp_integrable μ (by simpa only [one_mul] using hg :
      Integrable (fun x => Real.exp (1*H g x)) μ) n
  have haffr (g : ℕ → ℝ) (t : ℝ) (x : Fin n → S) :
      Hr (Function.update g i t) x = Hr (Function.update g i 0) x+t*replicaPotential v n x := by
    calc
      _ = ∑ l, (H (Function.update g i 0) (x l)+t*v (x l)) :=
        Finset.sum_congr rfl (fun l _ => haff g t (x l))
      _ = _ := by simp only [Hr,replicaPotential,Finset.sum_add_distrib,Finset.mul_sum]
  have hh := countableGaussian_coordinate_tilt_ibp_of_exp_integrable
    (Measure.pi fun _ : Fin n => μ) i hHr hvr hG (mul_nonneg (Nat.cast_nonneg n) hC) hD
    (replicaPotential_bound hvC n) hGD haffr hir
  change (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential v n x*G x)-
      gibbsReplicaMean μ (H g) n G*gibbsReplicaMean μ (H g) n (replicaPotential v n)
      ∂countableGaussianLaw at hh
  refine hh.trans ?_
  apply integral_congr_ae
  filter_upwards [hi] with g hg
  have hHg : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  rw [gibbsReplicaMean_potential_of_integrable μ hHg hv hg hvC,
    gibbsReplicaMean_product_of_integrable μ hHg hv hG hg hvC hGD]
  ring

lemma gaussianHamiltonian_replica_coordinate_ibp (i n : ℕ)
    {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ j, Measurable (v j)) (hL : Measurable L) (hG : Measurable G)
    {A D B : ℝ} (hA : ∀ x, |W x| ≤ A)
    (hD : ∀ x, (∑ j : Fin (L x), v j.val x^2) ≤ D)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    let a := maskedGaussianCoefficient v L i
    (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
      ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential a n x*G x)-
        n*gibbsReplicaMean μ (H g) (n+1) (fun x => a (x 0)*G (fun l => x l.succ))
        ∂countableGaussianLaw := by
  dsimp only
  apply countableGaussian_replica_coordinate_ibp μ i n
    (countableGaussianHamiltonian_measurable hW hv hL)
    (maskedGaussianCoefficient_measurable hv hL i) hG (Real.sqrt_nonneg D) hB
    (maskedGaussianCoefficient_bound v L hD i) hGB
    (fun g t x => countableGaussianHamiltonian_update W v L g i t x)
  simpa only [one_mul] using
    (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae

lemma integrable_tiltLaw_of_weighted {H F : S → ℝ} (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hF : Integrable (fun x => Real.exp (H x)*F x) μ) : Integrable F (tiltLaw μ H 1) := by
  have hp := tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he :
    Integrable (fun x => Real.exp (1*H x)) μ)
  unfold tiltLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
  apply (integrable_withDensity_iff_integrable_smul' (hH.const_mul 1).exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [one_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hF

lemma replicaMean_varying_measurable {Ω : Type*} [MeasurableSpace Ω] {H : Ω → S → ℝ}
    {n : ℕ} {F : Ω → (Fin n → S) → ℝ} (hH : Measurable (Function.uncurry H))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun g => gibbsReplicaMean μ (H g) n (F g)) := by
  have hr : Measurable (fun p : Ω×(Fin n → S) => Real.exp (replicaPotential (H p.1) n p.2)) := by
    apply Measurable.exp
    exact Finset.measurable_sum _ fun i _ => hH.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  let ρ := Measure.pi fun _ : Fin n => μ
  have hn : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x)*F g x ∂ρ) :=
    (hr.mul hF).stronglyMeasurable.integral_prod_right'.measurable
  have hd : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x) ∂ρ) :=
    hr.stronglyMeasurable.integral_prod_right'.measurable
  unfold gibbsReplicaMean tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  convert hn.div hd using 1
  all_goals try with_reducible_and_instances rfl

lemma replicaMean_energy_bound {H F : S → ℝ} {n : ℕ} (j : Fin n)
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hFint : Integrable (fun x => Real.exp (H x)*F x) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    |gibbsReplicaMean μ H n (fun x => F (x j)*G x)| ≤ B*tiltMean μ H (fun x => |F x|) 1 := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  let θ := tiltLaw μ H 1
  let ρ := Measure.pi fun _ : Fin n => θ
  have hFi : Integrable F θ := integrable_tiltLaw_of_weighted μ hH he hFint
  have hcoord : Integrable (fun x : Fin n → S => F (x j)) ρ :=
    (measurePreserving_eval (fun _ : Fin n => θ) j).integrable_comp_of_integrable hFi
  have hprod : Integrable (fun x : Fin n → S => F (x j)*G x) ρ := by
    apply (hcoord.abs.const_mul B).mono' ((hF.comp (measurable_pi_apply j)).mul hG).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |F (x j)*G x| ≤ B*|F (x j)|
      rw [abs_mul,mul_comm |F (x j)|]
      exact mul_le_mul (hGB x) le_rfl (abs_nonneg _) hB
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  calc
    _ ≤ ∫ x : Fin n → S, |F (x j)*G x| ∂ρ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ρ) (fun x : Fin n → S => F (x j)*G x)
    _ ≤ ∫ x : Fin n → S, B*|F (x j)| ∂ρ := by
      apply integral_mono hprod.abs (hcoord.abs.const_mul B)
      intro x
      change |F (x j)*G x| ≤ B*|F (x j)|
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hGB x) (abs_nonneg (F (x j)))]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      rw [← gibbsReplicaMean_coordinate_of_integrable μ hH hF.abs he n j,
        gibbsReplicaMean_integral_of_integrable μ hH he]

lemma replicaMean_energy_sub {H F Q : S → ℝ} {n : ℕ} (j : Fin n)
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hQ : Measurable Q) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hFint : Integrable (fun x => Real.exp (H x)*F x) μ)
    (hQint : Integrable (fun x => Real.exp (H x)*Q x) μ)
    {B : ℝ} (hGB : ∀ x, |G x| ≤ B) :
    gibbsReplicaMean μ H n (fun x => (F (x j)-Q (x j))*G x) =
      gibbsReplicaMean μ H n (fun x => F (x j)*G x)-gibbsReplicaMean μ H n (fun x => Q (x j)*G x) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  let θ := tiltLaw μ H 1
  let ρ := Measure.pi fun _ : Fin n => θ
  have him (f : S → ℝ) (hf : Measurable f) (hfi : Integrable (fun x => Real.exp (H x)*f x) μ) :
      Integrable (fun x : Fin n → S => f (x j)*G x) ρ := by
    have hc := (measurePreserving_eval (fun _ : Fin n => θ) j).integrable_comp_of_integrable
      (integrable_tiltLaw_of_weighted μ hH he hfi)
    apply (hc.abs.const_mul B).mono' ((hf.comp (measurable_pi_apply j)).mul hG).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |f (x j)*G x| ≤ B*|f (x j)|
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hGB x) (abs_nonneg (f (x j)))]
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH he,sub_mul]
  exact integral_sub (him F hF hFint) (him Q hQ hQint)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_AnnealedReplicaConvergence
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {H : Ω → S → ℝ} (hH : Measurable (Function.uncurry H))

include hH in
lemma annealedReplica_bounded_integrable {r : ℕ} {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Integrable (fun g => gibbsReplicaMean μ (H g) r G) ν := by
  apply Integrable.of_bound (replicaMean_varying_measurable μ (F := fun _ => G) hH (hG.comp measurable_snd)).aestronglyMeasurable B
  exact ae_of_all _ fun g => by
    simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin r => μ) (H := replicaPotential (H g) r)
      (replicaPotential_measurable (hH.comp (measurable_const.prodMk measurable_id)) r) hG hB hGB

include hH in
lemma annealedReplica_bounded_tendsto {r : ℕ} {F : ℕ → (Fin r → S) → ℝ} {G : (Fin r → S) → ℝ}
    (hF : ∀ n, Measurable (F n)) (_ : Measurable G) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ n x, |F n x| ≤ B) (hlim : ∀ x, Tendsto (fun n => F n x) atTop (nhds (G x)))
    (he : ∀ᵐ g ∂ν, Integrable (fun x => Real.exp (H g x)) μ) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (H g) r (F n) ∂ν) atTop
      (nhds (∫ g, gibbsReplicaMean μ (H g) r G ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => B)
    (fun n => (replicaMean_varying_measurable μ (F := fun _ => F n) hH ((hF n).comp measurable_snd)).aestronglyMeasurable)
    (integrable_const B)
  · intro n
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin r => μ) (H := replicaPotential (H g) r)
        (replicaPotential_measurable (hH.comp (measurable_const.prodMk measurable_id)) r) (hF n) hB (hFB n)
  · filter_upwards [he] with g hg
    have hh : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
    let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hg :
      Integrable (fun x => Real.exp (1*H g x)) μ)
    simp_rw [gibbsReplicaMean_integral_of_integrable μ hh hg]
    exact tendsto_integral_of_dominated_convergence (fun _ : Fin r → S => B)
      (fun n => (hF n).aestronglyMeasurable) (integrable_const B)
      (fun n => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFB n x)
      (ae_of_all _ hlim)

end
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma gaussianReplica_prefix_ibp (m n : ℕ) (j : Fin n)
    {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) (hG : Measurable G) {A D E B : ℝ}
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    (∫ g, gibbsReplicaMean μ (H g) n (fun x => truncatedCountableGaussianField w L m g (x j)*G x)
      ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, gaussianPrefixCovariance v w L m (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*gaussianPrefixCovariance v w L m (x j.succ) (x 0)) ∂countableGaussianLaw := by
  dsimp only
  let H := countableGaussianHamiltonian W v L
  let a := maskedGaussianCoefficient v L
  let b := maskedGaussianCoefficient w L
  let C := Real.sqrt D
  let Q := Real.sqrt E
  have hmH : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have hmHg (g) : Measurable (H g) := hmH.comp (measurable_const.prodMk measurable_id)
  have hma (i) : Measurable (a i) := maskedGaussianCoefficient_measurable hv hL i
  have hmb (i) : Measurable (b i) := maskedGaussianCoefficient_measurable hw hL i
  have ha (i x) : |a i x| ≤ C := maskedGaussianCoefficient_bound v L hD i x
  have hb (i x) : |b i x| ≤ Q := maskedGaussianCoefficient_bound w L hE i x
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ := by
    simpa only [one_mul] using (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  let F (i : Fin m) (x : Fin n → S) := b i.val (x j)*G x
  let U (i : Fin m) (x : Fin n → S) := replicaPotential (a i.val) n x*F i x
  let V (i : Fin m) (x : Fin (n+1) → S) := a i.val (x 0)*(b i.val (x j.succ)*G (fun l => x l.succ))
  have hFm (i) : Measurable (F i) := ((hmb i.val).comp (measurable_pi_apply j)).mul hG
  have hUm (i) : Measurable (U i) := (replicaPotential_measurable (hma i.val) n).mul (hFm i)
  have hVm (i) : Measurable (V i) := by
    exact ((hma i.val).comp (measurable_pi_apply 0)).mul
      (((hmb i.val).comp (measurable_pi_apply j.succ)).mul
        (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)))
  have hFB (i x) : |F i x| ≤ Q*B := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hb _ _) (hGB _) (abs_nonneg _) hQ)
  have hUB (i x) : |U i x| ≤ (n:ℝ)*C*Q*B := by
    dsimp only [U]
    rw [abs_mul]
    calc
      _ ≤ ((n:ℝ)*C)*(Q*B) := mul_le_mul (replicaPotential_bound (ha i.val) n x) (hFB i x)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hC)
      _ = _ := by ring
  have hVB (i x) : |V i x| ≤ C*Q*B := by
    dsimp only [V]
    rw [abs_mul]
    calc
      _ ≤ C*(Q*B) := mul_le_mul (ha _ _) (hFB i (fun l => x l.succ)) (abs_nonneg _) hC
      _ = _ := by ring
  have hUi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i)) countableGaussianLaw :=
    annealedReplica_bounded_integrable μ countableGaussianLaw hmH (hUm i) (by positivity) (hUB i)
  have hVi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i)) countableGaussianLaw :=
    annealedReplica_bounded_integrable μ countableGaussianLaw hmH (hVm i) (by positivity) (hVB i)
  have hFi (i : Fin m) : Integrable (fun g => g i.val*gibbsReplicaMean μ (H g) n (F i)) countableGaussianLaw := by
    have hg : Integrable (fun g : ℕ → ℝ => g i.val) countableGaussianLaw :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i.val).integrable_comp_of_integrable
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    apply hg.mul_bdd (replicaMean_measurable μ hmH (hFm i)).aestronglyMeasurable
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general _
        (replicaPotential_measurable (hmHg g) n) (hFm i) (mul_nonneg hQ hB) (hFB i)
  have hleft : ∀ᵐ g ∂countableGaussianLaw,
      gibbsReplicaMean μ (H g) n (fun x => truncatedCountableGaussianField w L m g (x j)*G x) =
        ∑ i : Fin m, g i.val*gibbsReplicaMean μ (H g) n (F i) := by
    filter_upwards [he] with g hg
    rw [show (fun x => truncatedCountableGaussianField w L m g (x j)*G x) =
      fun x => ∑ i : Fin m, g i.val*F i x by
        funext x
        simp only [truncatedCountableGaussianField,gaussianPrefixField,Finset.sum_mul,F,b]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    rw [gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg
      (fun i _ => (hFm i).const_mul (g i.val)) (D := fun i => |g i.val| *(Q*B))
      (fun i _ x => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hFB i x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hright : ∀ᵐ g ∂countableGaussianLaw,
      (∑ i : Fin m, (gibbsReplicaMean μ (H g) n (U i)-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) (V i))) =
      gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, gaussianPrefixCovariance v w L m (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*gaussianPrefixCovariance v w L m (x j.succ) (x 0)) := by
    filter_upwards [he] with g hg
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,
      ← gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg (fun i _ => hUm i) (fun i _ => hUB i),
      ← gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg (fun i _ => hVm i) (fun i _ => hVB i)]
    congr 1
    · congr 1
      funext x
      dsimp [U,F,replicaPotential,gaussianPrefixCovariance,a,b]
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring
    · congr 1
      congr 1
      funext x
      simp only [V,gaussianPrefixCovariance,Finset.mul_sum,a,b]
      apply Finset.sum_congr rfl
      intro i _
      ring
  calc
    _ = ∫ g, ∑ i : Fin m, g i.val*gibbsReplicaMean μ (H g) n (F i) ∂countableGaussianLaw :=
      integral_congr_ae hleft
    _ = ∑ i : Fin m, ∫ g, g i.val*gibbsReplicaMean μ (H g) n (F i) ∂countableGaussianLaw :=
      integral_finsetSum _ (fun i _ => hFi i)
    _ = ∑ i : Fin m, ∫ g, gibbsReplicaMean μ (H g) n (U i)-
        n*gibbsReplicaMean μ (H g) (n+1) (V i) ∂countableGaussianLaw := by
      apply Finset.sum_congr rfl
      intro i _
      exact gaussianHamiltonian_replica_coordinate_ibp μ i.val n hW hv hL (hFm i) hA hD
        (mul_nonneg hQ hB) (hFB i)
    _ = ∫ g, ∑ i : Fin m, (gibbsReplicaMean μ (H g) n (U i)-
        n*gibbsReplicaMean μ (H g) (n+1) (V i)) ∂countableGaussianLaw :=
      (integral_finsetSum _ (fun i _ => (hUi i).sub ((hVi i).const_mul n))).symm
    _ = _ := integral_congr_ae hright

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianEnergyMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)

omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_combine (t b : ℝ) (n : ℕ) (g : ℕ → ℝ) (x : S) :
    t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x =
      countableGaussianHamiltonian (fun x => t*W x)
        (fun i x => t*v i x+b*gaussianTailCoefficient w n i x) L g x := by
  rw [countableGaussianHamiltonian,countableGaussianHamiltonian,countableGaussianField_add,
    countableGaussianField_smul,countableGaussianField_smul]
  ring

omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_exp_integrable (t b : ℝ) (n : ℕ) (x : S) :
    Integrable (fun g => Real.exp (t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x)) countableGaussianLaw := by
  simp_rw [gaussianHamiltonian_energy_combine]
  simpa only [one_mul] using countableGaussianHamiltonian_exp_integrable
    (W := fun x => t*W x) (v := fun i x => t*v i x+b*gaussianTailCoefficient w n i x) (L := L) x 1

include hA hD hE in
omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_exp_bound (t b : ℝ) (n : ℕ) (x : S) :
    (∫ g, Real.exp (t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x) ∂countableGaussianLaw) ≤
      Real.exp (|t| *A+t^2*D+b^2*E) := by
  simp_rw [gaussianHamiltonian_energy_combine]
  have ha (x : S) : |t*W x| ≤ |t| *A := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t)
  have h := countableGaussianHamiltonian_exp_integral_bound
    (v := fun i x => t*v i x+b*gaussianTailCoefficient w n i x) (L := L) ha
    (gaussianCombinedCoefficient_sq_bound v w L hD hE t b n) x 1
  convert h using 1 <;> simp only [one_mul,abs_one,one_pow]
  congr 1
  ring

include hW hv hw hL

lemma gaussianEnergy_weighted_moment_integrable (n k : ℕ) (t : ℝ) (x : S) :
    Integrable (fun g => |countableGaussianField (gaussianTailCoefficient w n) L g x|^k*
      Real.exp (t*countableGaussianHamiltonian W v L g x)) countableGaussianLaw := by
  have hp := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t 1 n x
  have hn := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t (-1) n x
  apply ((hp.add hn).const_mul (k.factorial:ℝ)).mono'
  · exact (((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_id.prodMk measurable_const)).abs.pow_const k |>.mul
      (((countableGaussianHamiltonian_measurable hW hv hL).comp
      (measurable_id.prodMk measurable_const)).const_mul t).exp).aestronglyMeasurable
  · exact ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (by positivity)]
      simpa only [one_mul,neg_one_mul,add_neg_cancel,sub_eq_add_neg,Pi.add_apply] using
        abs_pow_mul_exp_le (t*countableGaussianHamiltonian W v L g x)
          (countableGaussianField (gaussianTailCoefficient w n) L g x) k

include hA hD hE in
lemma gaussianEnergy_weighted_moment_bound (n k : ℕ) (t : ℝ) (x : S) :
    (∫ g, |countableGaussianField (gaussianTailCoefficient w n) L g x|^k*
      Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw) ≤
      2*(k.factorial:ℝ)*Real.exp (|t| *A+t^2*D+E) := by
  have hp := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t 1 n x
  have hn := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t (-1) n x
  calc
    _ ≤ ∫ g, (k.factorial:ℝ)*(Real.exp (t*countableGaussianHamiltonian W v L g x+
        1*countableGaussianField (gaussianTailCoefficient w n) L g x)+
        Real.exp (t*countableGaussianHamiltonian W v L g x+
        (-1)*countableGaussianField (gaussianTailCoefficient w n) L g x)) ∂countableGaussianLaw := by
      apply integral_mono (gaussianEnergy_weighted_moment_integrable hW hv hw hL n k t x)
        ((hp.add hn).const_mul _)
      intro g
      simpa only [one_mul,neg_one_mul,sub_eq_add_neg,Pi.add_apply] using abs_pow_mul_exp_le
        (t*countableGaussianHamiltonian W v L g x)
        (countableGaussianField (gaussianTailCoefficient w n) L g x) k
    _ ≤ _ := by
      rw [integral_const_mul,integral_add hp hn]
      have hp' := gaussianHamiltonian_energy_exp_bound hA hD hE t 1 n x
      have hn' := gaussianHamiltonian_energy_exp_bound hA hD hE t (-1) n x
      norm_num only [one_pow,neg_one_sq,one_mul] at hp' hn'
      have hh := mul_le_mul_of_nonneg_left (add_le_add hp' hn') (Nat.cast_nonneg k.factorial : (0:ℝ) ≤ _)
      simp only [one_mul] at *
      nlinarith

variable (μ : Measure S) [IsProbabilityMeasure μ]

include hA hD hE in
lemma gaussianEnergy_weighted_moment_joint_integrable (n k : ℕ) (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => |countableGaussianField (gaussianTailCoefficient w n) L p.2 p.1|^k*
      Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1)) (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    ((((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp measurable_swap).abs.pow_const k).mul
      (((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap).const_mul t).exp)
    (fun p => mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)
    (gaussianEnergy_weighted_moment_integrable hW hv hw hL n k t)
  exact gaussianEnergy_weighted_moment_bound hW hv hw hL hA hD hE n k t

include hA hD hE in
lemma gaussianEnergy_tail_weighted_L2 (t : ℝ) :
    Tendsto (fun n => ∫ p : S×(ℕ → ℝ),
      (countableGaussianField w L p.2 p.1-truncatedCountableGaussianField w L n p.2 p.1)^2*
        Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1) ∂(μ.prod countableGaussianLaw))
      atTop (nhds 0) := by
  have hm (n : ℕ) := gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 t
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ : S => (0:ℝ))
    (fun _ : S => 2*((2:ℕ).factorial:ℝ)*Real.exp (|t| *A+t^2*D+E))
    (fun n => (hm n).integral_prod_left.aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all μ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => by positivity))]
      exact gaussianEnergy_weighted_moment_bound hW hv hw hL hA hD hE n 2 t x)
    (ae_of_all μ fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [truncatedCountableGaussianField_eventually_eq w L x] with n hn
      simp only [countableGaussianField_tail,hn,sub_self,abs_zero,zero_pow (by omega : (2:ℕ)≠0),zero_mul,integral_zero])
  have he (n : ℕ) : (∫ p : S×(ℕ → ℝ),
      (countableGaussianField w L p.2 p.1-truncatedCountableGaussianField w L n p.2 p.1)^2*
        Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1) ∂(μ.prod countableGaussianLaw)) =
      ∫ x, ∫ g, |countableGaussianField (gaussianTailCoefficient w n) L g x|^2*
        Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw ∂μ := by
    simpa only [countableGaussianField_tail,sq_abs] using integral_prod _ (hm n)
  simp_rw [he]
  simpa only [integral_zero] using ht

end

lemma integral_mul_le_sqrt_integrals {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {a b : X → ℝ} (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ)
    (ha0 : ∀ᵐ x ∂ρ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂ρ, 0 ≤ b x)
    (hai : Integrable (fun x => a x^2) ρ) (hbi : Integrable (fun x => b x^2) ρ) :
    (∫ x, a x*b x ∂ρ) ≤ Real.sqrt (∫ x, a x^2 ∂ρ)*Real.sqrt (∫ x, b x^2 ∂ρ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two ha0 hb0
    (by simpa using (memLp_two_iff_integrable_sq ha).mpr hai)
    (by simpa using (memLp_two_iff_integrable_sq hb).mpr hbi)
  simpa only [← Real.sqrt_eq_rpow,Real.rpow_two] using h

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) (ν : Measure Ω) [IsProbabilityMeasure μ] [SFinite ν]
variable {H F : Ω → S → ℝ} (hH : Measurable (Function.uncurry H))
variable (hF : Measurable (Function.uncurry F))
variable (hZ : Integrable (fun g => (tiltPartition μ (H g) 1)⁻¹^2) ν)
variable (hI : Integrable (fun p : S×Ω => F p.2 p.1^2*Real.exp (2*H p.2 p.1)) (μ.prod ν))

include hH in
lemma tiltPartition_joint_measurable : Measurable (fun g => tiltPartition μ (H g) 1) := by
  simpa only [tiltPartition,one_mul,Function.uncurry_apply_pair] using
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

include hH hF hZ hI in
lemma weighted_gibbs_L1_integrable :
    Integrable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹*
      (|F p.2 p.1| *Real.exp (H p.2 p.1))) (μ.prod ν) := by
  have ha : AEStronglyMeasurable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹) (μ.prod ν) :=
    ((tiltPartition_joint_measurable μ hH).comp measurable_snd).inv.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun p : S×Ω => |F p.2 p.1| *Real.exp (H p.2 p.1)) (μ.prod ν) :=
    (((hF.comp measurable_swap).abs).mul (hH.comp measurable_swap).exp).aestronglyMeasurable
  have hai : Integrable (fun p : S×Ω => ((tiltPartition μ (H p.2) 1)⁻¹)^2) (μ.prod ν) :=
    measurePreserving_snd.integrable_comp_of_integrable hZ
  have hbi : Integrable (fun p : S×Ω => (|F p.2 p.1| *Real.exp (H p.2 p.1))^2) (μ.prod ν) := by
    simpa only [mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hI
  exact (memLp_two_iff_integrable_sq ha).mpr hai |>.integrable_mul
    ((memLp_two_iff_integrable_sq hb).mpr hbi)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma tiltMean_abs_eq_weighted_integral (g : Ω) :
    tiltMean μ (H g) (fun x => |F g x|) 1 =
      ∫ x, (tiltPartition μ (H g) 1)⁻¹*(|F g x| *Real.exp (H g x)) ∂μ := by
  simp only [tiltMean,tiltIntegral,one_mul,integral_const_mul]
  rw [div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun _ => mul_comm _ _

include hH hF hZ hI in
lemma tiltMean_abs_annealed_integrable :
    Integrable (fun g => tiltMean μ (H g) (fun x => |F g x|) 1) ν := by
  simp_rw [tiltMean_abs_eq_weighted_integral μ]
  exact (weighted_gibbs_L1_integrable μ ν hH hF hZ hI).integral_prod_right

include hH hF hZ hI in
lemma tiltMean_abs_annealed_L2_bound :
    (∫ g, tiltMean μ (H g) (fun x => |F g x|) 1 ∂ν) ≤
      Real.sqrt (∫ g, (tiltPartition μ (H g) 1)⁻¹^2 ∂ν)*
      Real.sqrt (∫ p : S×Ω, F p.2 p.1^2*Real.exp (2*H p.2 p.1) ∂(μ.prod ν)) := by
  have ha : AEStronglyMeasurable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹) (μ.prod ν) :=
    ((tiltPartition_joint_measurable μ hH).comp measurable_snd).inv.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun p : S×Ω => |F p.2 p.1| *Real.exp (H p.2 p.1)) (μ.prod ν) :=
    (((hF.comp measurable_swap).abs).mul (hH.comp measurable_swap).exp).aestronglyMeasurable
  have hai : Integrable (fun p : S×Ω => ((tiltPartition μ (H p.2) 1)⁻¹)^2) (μ.prod ν) :=
    measurePreserving_snd.integrable_comp_of_integrable hZ
  have hbi : Integrable (fun p : S×Ω => (|F p.2 p.1| *Real.exp (H p.2 p.1))^2) (μ.prod ν) := by
    simpa only [mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hI
  have ha0 : ∀ p : S×Ω, 0 ≤ (tiltPartition μ (H p.2) 1)⁻¹ := by
    intro p
    exact inv_nonneg.mpr (integral_nonneg (fun _ => (Real.exp_pos _).le))
  have hh := integral_mul_le_sqrt_integrals (μ.prod ν) ha hb (ae_of_all _ ha0)
    (ae_of_all _ fun _ => by positivity) hai hbi
  rw [integral_prod _ (weighted_gibbs_L1_integrable μ ν hH hF hZ hI),
    integral_integral_swap (weighted_gibbs_L1_integrable μ ν hH hF hZ hI)] at hh
  simp_rw [← tiltMean_abs_eq_weighted_integral μ] at hh
  have he : (∫ p : S×Ω, (tiltPartition μ (H p.2) 1)⁻¹^2 ∂(μ.prod ν)) =
      ∫ g, (tiltPartition μ (H g) 1)⁻¹^2 ∂ν := by
    rw [integral_prod _ hai]
    simp only [integral_const,probReal_univ,one_smul]
  simpa only [he,mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hh

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianGibbsEnergy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
omit [MeasurableSpace S] in
lemma gaussianTailCoefficient_zero (w : ℕ → S → ℝ) : gaussianTailCoefficient w 0=w := by
  funext i x
  simp [gaussianTailCoefficient]

include hW hv hw hL hA hD hE

lemma gaussianEnergy_tail_tilt_integrable (n : ℕ) :
    Integrable (fun g => tiltMean μ (countableGaussianHamiltonian W v L g)
      (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1) countableGaussianLaw := by
  apply tiltMean_abs_annealed_integrable μ countableGaussianLaw
    (countableGaussianHamiltonian_measurable hW hv hL)
    (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL)
    (gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 2)
  simpa only [sq_abs] using gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 2

lemma gaussianEnergy_tail_tilt_tendsto :
    Tendsto (fun n => ∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
      (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1 ∂countableGaussianLaw)
      atTop (nhds 0) := by
  have hlim := (gaussianEnergy_tail_weighted_L2 hW hv hw hL hA hD hE μ 2).sqrt.const_mul
    (Real.sqrt (∫ g, (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^2 ∂countableGaussianLaw))
  simp only [Real.sqrt_zero,mul_zero] at hlim
  apply squeeze_zero (fun n => integral_nonneg fun g => ?_) (fun n => ?_) hlim
  · unfold tiltMean tiltIntegral tiltPartition
    exact div_nonneg (integral_nonneg (fun _ => by positivity)) (integral_nonneg (fun _ => by positivity))
  · have h := tiltMean_abs_annealed_L2_bound μ countableGaussianLaw
      (countableGaussianHamiltonian_measurable hW hv hL)
      (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL)
      (gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 2)
      (by simpa only [sq_abs] using gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 2)
    simpa only [countableGaussianField_tail] using h

lemma gaussianEnergy_tail_weighted_integrable_ae (n : ℕ) :
    ∀ᵐ g ∂countableGaussianLaw,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian W v L g x)*
        countableGaussianField (gaussianTailCoefficient w n) L g x) μ := by
  filter_upwards [(gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 1 1).prod_left_ae] with g hg
  apply hg.mono'
  · exact (((countableGaussianHamiltonian_measurable hW hv hL).comp
      (measurable_const.prodMk measurable_id)).exp.mul
      ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simp only [Real.norm_eq_abs,abs_mul,Real.abs_exp,pow_one,one_mul]; exact le_of_eq (mul_comm _ _)

lemma gaussianEnergy_tail_replica_integrable {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) (n : ℕ) :
    Integrable (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x)) countableGaussianLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ)×(Fin r → S) =>
      countableGaussianField (gaussianTailCoefficient w n) L p.1 (p.2 j)*G p.2) :=
    ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))).mul (hG.comp measurable_snd)
  apply ((gaussianEnergy_tail_tilt_integrable μ hW hv hw hL hA hD hE n).const_mul B).mono'
    (replicaMean_varying_measurable μ (countableGaussianHamiltonian_measurable hW hv hL) hm).aestronglyMeasurable
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
    gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hf
  simpa only [Real.norm_eq_abs] using replicaMean_energy_bound μ j (H := countableGaussianHamiltonian W v L g)
    (F := countableGaussianField (gaussianTailCoefficient w n) L g)
    ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
    ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id)) hG (by simpa only [one_mul] using hg) hf hB hGB

lemma gaussianEnergy_tail_replica_tendsto {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x) ∂countableGaussianLaw)
      atTop (nhds 0) := by
  have ht := (gaussianEnergy_tail_tilt_tendsto μ hW hv hw hL hA hD hE).const_mul B
  simp only [mul_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_) ht
  calc
    _ ≤ ∫ g, |gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x)| ∂countableGaussianLaw := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := countableGaussianLaw)
        (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
          (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x))
    _ ≤ B*(∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
        (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1 ∂countableGaussianLaw) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB n).abs
        ((gaussianEnergy_tail_tilt_integrable μ hW hv hw hL hA hD hE n).const_mul B)
      filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
        gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hf
      exact replicaMean_energy_bound μ j (H := countableGaussianHamiltonian W v L g)
        (F := countableGaussianField (gaussianTailCoefficient w n) L g)
        ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
        ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
          (measurable_const.prodMk measurable_id)) hG (by simpa only [one_mul] using hg) hf hB hGB

lemma gaussianEnergy_replica_integrable {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Integrable (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField w L g (x j)*G x)) countableGaussianLaw := by
  simpa only [gaussianTailCoefficient_zero] using
    gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB 0

lemma gaussianEnergy_replica_prefix_tendsto {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => truncatedCountableGaussianField w L n g (x j)*G x) ∂countableGaussianLaw) atTop
      (nhds (∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw)) := by
  have hc : Tendsto (fun _ : ℕ => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw) atTop
      (nhds (∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw)) := tendsto_const_nhds
  have ht := hc.sub (gaussianEnergy_tail_replica_tendsto μ hW hv hw hL hA hD hE j hG hB hGB)
  simp only [sub_zero] at ht
  apply ht.congr
  intro n
  rw [← integral_sub (gaussianEnergy_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB)
    (gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB n)]
  apply integral_congr_ae
  have hf := gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE 0
  simp only [gaussianTailCoefficient_zero] at hf
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
    hf,gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hfg hqg
  have hh : Measurable (countableGaussianHamiltonian W v L g) :=
    (countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id)
  have hff : Measurable (countableGaussianField w L g) :=
    (countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)
  have hq : Measurable (countableGaussianField (gaussianTailCoefficient w n) L g) :=
    (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id)
  have heq := replicaMean_energy_sub μ j hh hff hq hG (by simpa only [one_mul] using hg) hfg hqg hGB
  simpa only [countableGaussianField_tail,sub_sub_cancel] using heq.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableGaussianFullIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma countableGaussian_replica_full_ibp (n : ℕ) (j : Fin n)
    {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) (hG : Measurable G) {A D E B : ℝ}
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    (∫ g, gibbsReplicaMean μ (H g) n (fun x => countableGaussianField w L g (x j)*G x)
      ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, countableGaussianCovariance v w L (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*countableGaussianCovariance v w L (x j.succ) (x 0)) ∂countableGaussianLaw := by
  dsimp only
  let H := countableGaussianHamiltonian W v L
  let C := |(D+E)/2|
  have hC : 0 ≤ C := abs_nonneg _
  have hHm : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ := by
    simpa only [one_mul] using (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  let K := gaussianPrefixCovariance v w L
  let KFull := countableGaussianCovariance v w L
  have hKm (m) : Measurable (Function.uncurry (K m)) := gaussianPrefixCovariance_measurable hv hw hL m
  have hKFullm : Measurable (Function.uncurry KFull) := countableGaussianCovariance_measurable hv hw hL
  have hKb (m x y) : |K m x y| ≤ C := (gaussianPrefixCovariance_bound v w L hD hE m x y).trans (le_abs_self _)
  have hKFullb (x y) : |KFull x y| ≤ C := hKb (L x) x y
  have hKt (x y) : Tendsto (fun m => K m x y) atTop (nhds (KFull x y)) :=
    tendsto_const_nhds.congr' ((gaussianPrefixCovariance_eventually_eq v w L x y).mono fun _ h => h.symm)
  let U (m) (x : Fin n → S) := G x*∑ l, K m (x j) (x l)
  let UFull (x : Fin n → S) := G x*∑ l, KFull (x j) (x l)
  let V (m) (x : Fin (n+1) → S) := G (fun l => x l.succ)*K m (x j.succ) (x 0)
  let VFull (x : Fin (n+1) → S) := G (fun l => x l.succ)*KFull (x j.succ) (x 0)
  have hPair (a b : Fin n) : Measurable (fun x : Fin n → S => (x a,x b)) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  have hUm (m) : Measurable (U m) := hG.mul
    (Finset.measurable_sum Finset.univ fun (l : Fin n) _ => (hKm m).comp (hPair j l))
  have hUFullm : Measurable UFull := hG.mul
    (Finset.measurable_sum Finset.univ fun (l : Fin n) _ => hKFullm.comp (hPair j l))
  have hPairS : Measurable (fun x : Fin (n+1) → S => (x j.succ,x 0)) :=
    (measurable_pi_apply j.succ).prodMk (measurable_pi_apply 0)
  have hVm (m) : Measurable (V m) :=
    (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)).mul
      ((hKm m).comp hPairS)
  have hVFullm : Measurable VFull :=
    (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)).mul
      (hKFullm.comp hPairS)
  have hsum (k : S → S → ℝ) (hk : ∀ x y, |k x y| ≤ C) (x : Fin n → S) :
      |G x*∑ l, k (x j) (x l)| ≤ B*((n:ℝ)*C) := by
    rw [abs_mul]
    apply mul_le_mul (hGB x) _ (abs_nonneg _) hB
    calc
      _ ≤ ∑ l : Fin n, |k (x j) (x l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, C := Finset.sum_le_sum fun l _ => hk _ _
      _ = _ := by simp
  have hUB (m x) : |U m x| ≤ B*((n:ℝ)*C) := hsum (K m) (hKb m) x
  have hUFullB (x) : |UFull x| ≤ B*((n:ℝ)*C) := hsum KFull hKFullb x
  have hVB (m x) : |V m x| ≤ B*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hGB _) (hKb m _ _) (abs_nonneg _) hB)
  have hVFullB (x) : |VFull x| ≤ B*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hGB _) (hKFullb _ _) (abs_nonneg _) hB)
  have hUt (x) : Tendsto (fun m => U m x) atTop (nhds (UFull x)) :=
    (tendsto_finsetSum _ (fun index _ => hKt (x j) (x index))).const_mul (G x)
  have hVt (x) : Tendsto (fun m => V m x) atTop (nhds (VFull x)) :=
    (hKt (x j.succ) (x 0)).const_mul (G (fun l => x l.succ))
  have hUi (m) := annealedReplica_bounded_integrable μ countableGaussianLaw hHm (hUm m) (by positivity) (hUB m)
  have hVi (m) := annealedReplica_bounded_integrable μ countableGaussianLaw hHm (hVm m) (by positivity) (hVB m)
  have hUFulli := annealedReplica_bounded_integrable μ countableGaussianLaw hHm hUFullm (by positivity) hUFullB
  have hVFulli := annealedReplica_bounded_integrable μ countableGaussianLaw hHm hVFullm (by positivity) hVFullB
  have hUL := annealedReplica_bounded_tendsto μ countableGaussianLaw hHm hUm hUFullm (by positivity) hUB hUt he
  have hVL := annealedReplica_bounded_tendsto μ countableGaussianLaw hHm hVm hVFullm (by positivity) hVB hVt he
  have hR := hUL.sub (hVL.const_mul (n:ℝ))
  have hL' := gaussianEnergy_replica_prefix_tendsto μ hW hv hw hL hA hD hE j hG hB hGB
  have heq (m) : (∫ g, gibbsReplicaMean μ (H g) n
      (fun x => truncatedCountableGaussianField w L m g (x j)*G x) ∂countableGaussianLaw) =
      (∫ g, gibbsReplicaMean μ (H g) n (U m) ∂countableGaussianLaw)-
        (n:ℝ)*(∫ g, gibbsReplicaMean μ (H g) (n+1) (V m) ∂countableGaussianLaw) := by
    rw [gaussianReplica_prefix_ibp μ m n j hW hv hw hL hG hA hD hE hB hGB]
    exact (integral_sub (hUi m) ((hVi m).const_mul n)).trans (by rw [integral_const_mul])
  have hlim := tendsto_nhds_unique hL' (hR.congr (fun m => (heq m).symm))
  exact hlim.trans ((integral_sub hUFulli (hVFulli.const_mul n)).trans (by rw [integral_const_mul])).symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernel_replicaMean_measurable {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G)) :
    Measurable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) := by
  change Measurable (fun a => tiltMean (kernelReplica κ n a) (replicaPotential (H a) n) (G a) 1)
  apply kernel_tiltMean_measurable (kernelReplica κ n) (H := fun a => replicaPotential (H a) n) _ hG
  change Measurable (fun a : A × (Fin n → S) => ∑ i, H a.1 (a.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma normalizedPatternEnergy_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) (x : NormalizedSpin (n+1)) :
    normalizedPatternEnergy (n+1) (patternCount α (n+1)) (β • φ) g x=
      β*hamiltonian α φ (n+1) g (Real.sqrt (n+1:ℕ) • x.val) := by
  have hn : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have he (a : Fin (patternCount α (n+1))) :
      patternField g a (Real.sqrt (n+1:ℕ) • x.val) = ∑ i, g a i*x.val i := by
    unfold patternField
    simp only [PiLp.smul_apply,smul_eq_mul]
    have hs : (∑ i, g a i*(Real.sqrt (n+1:ℕ)*x.val i)) =
        (∑ i, g a i*x.val i)*Real.sqrt (n+1:ℕ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs,mul_div_cancel_right₀ _ hn]
  simp only [normalizedPatternEnergy,BoundedContinuousFunction.coe_smul,smul_eq_mul,
    hamiltonian,he,Finset.mul_sum]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulkLogPartition_eq (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) :
    bulkLogPartition n M f v a g =
      Real.log (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1) := by
  simp only [bulkLogPartition, vectorLogPartition, vectorPartition, tiltPartition, one_mul, bulkHamiltonian,
    innerSL_apply_apply]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkConcentration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeatureBound_sq (N : ℕ) (v : ℕ→ℝ) :
    bulkFeatureBound N v^2 = ∑ p, bulkAmplitude N v p^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma bulkFeatureBound_sq_le (N : ℕ) (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ p, |v (p+1)|≤C) : bulkFeatureBound N v^2 ≤ C^2*bulkScale N^2 := by
  rw [bulkFeatureBound_sq]
  have hi (p : Fin N) : bulkAmplitude N v p^2 ≤ C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := by
    let w : ℝ := (1/2:ℝ)^(p.val+1)
    have hw0 : 0≤w := pow_nonneg (by norm_num) _
    have hw1 : w≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv2 : v (p.val+1)^2 ≤ C^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v (p.val+1))) hC).2 (hv p.val)
    unfold bulkAmplitude
    rw [perturbationWeight_eq]
    change (bulkScale N*w*v (p.val+1))^2 ≤ _
    calc
      _ ≤ bulkScale N^2*w^2*C^2 := by
        rw [mul_pow,mul_pow]; exact mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ ≤ C^2*bulkScale N^2*w := by
        nlinarith [mul_le_mul_of_nonneg_left (show w^2≤w by nlinarith) (mul_nonneg (sq_nonneg C) (sq_nonneg (bulkScale N)))]
  calc
    _ ≤ ∑ p : Fin N, C^2*bulkScale N^2*(1/2:ℝ)^(p.val+1) := Finset.sum_le_sum fun p _ => hi p
    _ = C^2*bulkScale N^2*(∑ p : Fin N, (1/2:ℝ)^(p.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*bulkScale N^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (by positivity)
    _ = _ := mul_one _

lemma bulkLogPartition_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) := by
  simp_rw [bulkLogPartition_eq]
  change Measurable (fun a : BulkDisorder (n+1) M => Real.log (∫ x,
    Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x) ∂unitSphereLaw (n+1)))
  simp only [one_mul]
  exact (bulkHamiltonian_continuous (n+1) M f v).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma bulkLogPartition_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    |bulkLogPartition n M f v a.1 a.2| ≤ M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖ := by
  apply vectorLogPartition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (normalizedPatternEnergy_bound (n+1) M f a.1)
  intro x
  simp only [Function.comp_apply,innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl]

lemma bulkLogPartition_memLp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    MemLp (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) 2
      (bulkDisorderLaw (n+1) M) := by
  have hi : MemLp (id : BulkMark (n+1) → BulkMark (n+1)) 2 (stdGaussian (BulkMark (n+1))) :=
    IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)
  have hn : MemLp (fun g : BulkMark (n+1) => ‖g‖) 2 (stdGaussian (BulkMark (n+1))) := hi.norm
  have hc : MemLp (fun _ : BulkMark (n+1) => (M:ℝ)*‖f‖) 2 (stdGaussian (BulkMark (n+1))) := memLp_const _
  have hg : MemLp (fun g : BulkMark (n+1) => M*‖f‖+bulkFeatureBound (n+1) v*‖g‖) 2
      (stdGaussian (BulkMark (n+1))) := hc.add (hn.const_mul (bulkFeatureBound (n+1) v))
  apply (hg.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulkLogPartition_measurable n M f v).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkLogPartition_bound n M f v a

lemma bulkDirection_continuous (N : ℕ) (p : Fin N) : Continuous (bulkDirection N p) :=
  enrichedFeature_continuous _ _ _ _ _

lemma bulkDirection_norm (N : ℕ) (p : Fin N) (x : NormalizedSpin N) : ‖bulkDirection N p x‖=1 := by
  rw [bulkDirection,enrichedFeature_norm]
  have he : (∑ j : Fin N, (Pi.single (M := fun _ : Fin N => ℝ) p (1:ℝ) j)^2)=1 := by
    classical
    simp [Pi.single_apply]
  rw [he]
  norm_num

lemma bulkY_bound (N : ℕ) (p : Fin N) (g : BulkMark N) (x : NormalizedSpin N) : |bulkY N p g x|≤‖g‖ := by
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [bulkDirection_norm,one_mul])

lemma bulkY_measurable (N : ℕ) (p : Fin N) : Measurable (Function.uncurry (bulkY N p)) :=
  ((bulkDirection_continuous N p).measurable.comp measurable_snd).inner measurable_fst

lemma bulkAmplitude_update (N : ℕ) (v : ℕ→ℝ) (p j : Fin N) (u : ℝ) :
    bulkAmplitude N (Function.update v (p.val+1) u) j=
      bulkAmplitude N (Function.update v (p.val+1) 0) j+u*bulkCoefficient N p*Pi.single (M := fun _ : Fin N => ℝ) p 1 j := by
  classical
  by_cases hj : j=p
  · subst j; simp [bulkAmplitude,bulkCoefficient]; ring
  · have h : j.val+1≠p.val+1 := fun h => hj (Fin.ext (Nat.add_right_cancel h))
    simp [bulkAmplitude,Function.update_of_ne h,Pi.single_eq_of_ne hj]

lemma bulkFeature_update (N : ℕ) (v : ℕ→ℝ) (p : Fin N) (u : ℝ) (x : NormalizedSpin N) :
    bulkFeature N (Function.update v (p.val+1) u) x=
      bulkFeature N (Function.update v (p.val+1) 0) x+(u*bulkCoefficient N p) • bulkDirection N p x := by
  ext i
  cases i with
  | inl i => simp [bulkFeature,bulkDirection,enrichedFeature]
  | inr j =>
    change bulkAmplitude N (Function.update v (p.val+1) u) j.1*spinTensorFeature N _ x j.2 =
      bulkAmplitude N (Function.update v (p.val+1) 0) j.1*spinTensorFeature N _ x j.2 +
      (u*bulkCoefficient N p)*(Pi.single (M := fun _ : Fin N => ℝ) p 1 j.1*spinTensorFeature N _ x j.2)
    rw [bulkAmplitude_update]
    ring

lemma bulkHamiltonian_update (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin N) (u : ℝ)
    (a : BulkDisorder N M) (x : NormalizedSpin N) :
    bulkHamiltonian N M f (Function.update v (p.val+1) u) a.1 a.2 x =
      bulkHamiltonian N M f (Function.update v (p.val+1) 0) a.1 a.2 x+u*(bulkCoefficient N p*bulkY N p a.2 x) := by
  simp only [bulkHamiltonian]
  rw [bulkFeature_update N v p u x]
  simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_trivial,bulkY]
  ring

lemma bulkCoefficient_pos (n : ℕ) (p : Fin (n+1)) : 0<bulkCoefficient (n+1) p := by
  unfold bulkCoefficient bulkScale
  rw [perturbationWeight_eq]
  positivity

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_GaussianPressureDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x|≤A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E)

include hW hv hw hL hA hD hE

lemma annealedGaussianTiltMean_ibp :
    (∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
      (countableGaussianField w L g) 1 ∂countableGaussianLaw) =
    ∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
        (fun x => countableGaussianCovariance v w L x x) 1 -
      gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
        (fun x => countableGaussianCovariance v w L (x 1) (x 0)) ∂countableGaussianLaw := by
  have hH := countableGaussianHamiltonian_measurable hW hv hL
  have hY := countableGaussianField_measurable hw hL
  have hK := countableGaussianCovariance_measurable hv hw hL
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable
      (fun x => Real.exp (countableGaussianHamiltonian W v L g x)) μ := by
    simpa only [one_mul] using
      (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  have hb := countableGaussian_replica_full_ibp μ 1 (0 : Fin 1) hW hv hw hL
    (G := fun _ => 1) measurable_const hA hD hE (B := 1) (by norm_num) (by simp)
  simp only [mul_one,one_mul,Fin.sum_univ_one,Nat.cast_one] at hb
  calc
    _ = ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 1
      (fun x => countableGaussianField w L g (x 0)) ∂countableGaussianLaw := by
      apply integral_congr_ae
      filter_upwards [he] with g hg
      exact (gibbsReplicaMean_coordinate_of_integrable μ hH.of_uncurry_left hY.of_uncurry_left hg 1 0).symm
    _ = _ := hb.trans (integral_congr_ae (by
      filter_upwards [he] with g hg
      have hd := gibbsReplicaMean_coordinate_of_integrable μ hH.of_uncurry_left
        (show Measurable (fun x => countableGaussianCovariance v w L x x) from
          hK.comp (measurable_id.prodMk measurable_id)) hg 1 0
      exact congrArg (fun r => r - gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
        (fun x => countableGaussianCovariance v w L (x 1) (x 0))) hd))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegratedConvex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

variable {I : Type} [Fintype I]

lemma countableGaussianVector_measurable : Measurable (countableGaussianVector (I:=I)) := by
  unfold countableGaussianVector
  fun_prop

lemma countableGaussianVector_law :
    countableGaussianLaw.map (countableGaussianVector (I:=I))=stdGaussian (EuclideanSpace ℝ I) := by
  let c : (ℕ→ℝ)→I→ℝ := fun g i => g (countableCoordinate i)
  have hc : Measurable c := by fun_prop
  have hl : countableGaussianLaw.map c=Measure.infinitePi (fun _ : I => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj countableCoordinate_injective
  change countableGaussianLaw.map ((WithLp.toLp 2) ∘ c)=_
  rw [← Measure.map_map (PiLp.continuous_toLp 2 _).measurable hc,hl,
    Measure.infinitePi_eq_pi,map_pi_eq_stdGaussian]

lemma vectorGaussianRow_measurable {S : Type*} [MeasurableSpace S]
    {V : S→EuclideanSpace ℝ I} (hV : Measurable V) (i : ℕ) : Measurable (vectorGaussianRow V i) := by
  classical
  unfold vectorGaussianRow finiteGaussianRow
  apply Finset.measurable_sum
  intro j _
  split_ifs
  · exact (EuclideanSpace.proj j).continuous.measurable.comp hV
  · exact measurable_const

lemma vectorGaussianRow_field {S : Type*} (V : S→EuclideanSpace ℝ I) (g : ℕ→ℝ) (x : S) :
    countableGaussianField (vectorGaussianRow V) (fun _ => vectorGaussianLength I) g x=
      inner ℝ (V x) (countableGaussianVector g) := by
  unfold countableGaussianField gaussianPrefixField vectorGaussianRow vectorGaussianLength
  rw [finiteGaussianRow_field countableCoordinate_injective]
  rfl

lemma vectorGaussianRow_norm {S : Type*} (V : S→EuclideanSpace ℝ I) (x : S) :
    (∑ i : Fin (vectorGaussianLength I), vectorGaussianRow V i.val x^2)=‖V x‖^2 := by
  unfold vectorGaussianRow vectorGaussianLength
  rw [finiteGaussianRow_norm countableCoordinate_injective,← real_inner_self_eq_norm_sq]
  change (∑ i, V x i^2)=∑ i, V x i*V x i
  simp only [pow_two]

lemma vectorGaussianRow_covariance {S : Type*} (V W : S→EuclideanSpace ℝ I) (x y : S) :
    countableGaussianCovariance (vectorGaussianRow V) (vectorGaussianRow W)
      (fun _ => vectorGaussianLength I) x y = inner ℝ (W x) (V y) := by
  unfold countableGaussianCovariance gaussianPrefixCovariance maskedGaussianCoefficient
  simp only [Fin.is_lt,ite_true]
  change (∑ i : Fin (vectorGaussianLength I),
    finiteGaussianRow countableCoordinate (fun j => W x j) i.val *
    finiteGaussianRow countableCoordinate (fun j => V y j) i.val)=_
  calc
    _ = ∑ j, W x j*finiteGaussianRow countableCoordinate (fun k => V y k) (countableCoordinate j) :=
      finiteGaussianRow_sum countableCoordinate_injective (fun j => W x j)
        (fun i a => a*finiteGaussianRow countableCoordinate (fun j => V y j) i) (by simp)
    _ = ∑ j, W x j*V y j := by simp_rw [finiteGaussianRow_key countableCoordinate_injective]
    _ = _ := by
      change (∑ i, W x i*V y i)=∑ i, V y i*W x i
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma euclideanGaussian_tiltMean_ibp {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A D E : ℝ} (hA : ∀ x, |H x|≤A) (hD : ∀ x, ‖V x‖^2≤D) (hE : ∀ x, ‖W x‖^2≤E) :
    (∫ g, tiltMean μ (fun x => H x+inner ℝ (V x) g) (fun x => inner ℝ (W x) g) 1
      ∂stdGaussian (EuclideanSpace ℝ I)) =
    ∫ g, tiltMean μ (fun x => H x+inner ℝ (V x) g) (fun x => inner ℝ (W x) (V x)) 1 -
      gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) 2
        (fun x => inner ℝ (W (x 1)) (V (x 0))) ∂stdGaussian (EuclideanSpace ℝ I) := by
  have h1 : Measurable (fun a : EuclideanSpace ℝ I × S => H a.2+inner ℝ (V a.2) a.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  have h2 : Measurable (fun a : EuclideanSpace ℝ I × S => inner ℝ (W a.2) a.1) :=
    (hW.comp measurable_snd).inner measurable_fst
  have h3 : Measurable (fun x => inner ℝ (W x) (V x)) := hW.inner hV
  have h4 : Measurable (fun x : Fin 2→S => inner ℝ (W (x 1)) (V (x 0))) :=
    (hW.comp (measurable_pi_apply 1)).inner (hV.comp (measurable_pi_apply 0))
  have hleft := kernel_tiltMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g) (Y := fun g x => inner ℝ (W x) g) h1 h2
  have hright := (kernel_tiltMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g) (Y := fun _ x => inner ℝ (W x) (V x)) h1
    (h3.comp measurable_snd)).sub (kernel_replicaMean_measurable (Kernel.const (EuclideanSpace ℝ I) μ)
    (H := fun g x => H x+inner ℝ (V x) g)
    (G := fun _ x => inner ℝ (W (x 1)) (V (x 0))) h1 (h4.comp measurable_snd))
  have he := annealedGaussianTiltMean_ibp μ hH (vectorGaussianRow_measurable hV)
    (vectorGaussianRow_measurable hW) measurable_const hA
    (fun x => (vectorGaussianRow_norm V x).trans_le (hD x))
    (fun x => (vectorGaussianRow_norm W x).trans_le (hE x))
  have hham (g) : countableGaussianHamiltonian H (vectorGaussianRow V)
      (fun _ => vectorGaussianLength I) g = fun x => H x+inner ℝ (V x) (countableGaussianVector g) := by
    funext x
    exact congrArg (fun y => H x+y) (vectorGaussianRow_field V g x)
  have hfield (g) : countableGaussianField (vectorGaussianRow W)
      (fun _ => vectorGaussianLength I) g = fun x => inner ℝ (W x) (countableGaussianVector g) :=
    funext (vectorGaussianRow_field W g)
  simp_rw [hham,hfield,vectorGaussianRow_covariance] at he
  simp only [Kernel.const_apply] at hleft hright
  change Measurable (fun g => tiltMean μ (fun x => H x+inner ℝ (V x) g)
    (fun x => inner ℝ (W x) (V x)) 1 - gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) 2
      (fun x => inner ℝ (W (x 1)) (V (x 0)))) at hright
  rw [← countableGaussianVector_law (I:=I),
    integral_map countableGaussianVector_measurable.aemeasurable hleft.aestronglyMeasurable,
    integral_map countableGaussianVector_measurable.aemeasurable hright.aestronglyMeasurable]
  exact he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkAnnealedTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

lemma bulkMarkNorm_integrable (N M : ℕ) :
    Integrable (fun a : BulkDisorder N M => ‖a.2‖) (bulkDisorderLaw N M) :=
  ((((IsGaussian.memLp_id (stdGaussian (BulkMark N)) 2 (by simp)).norm).integrable (by norm_num))).comp_snd _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCovarianceDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma tiltMean_const_mul_general {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H G : S → ℝ) (a t : ℝ) :
    tiltMean μ H (fun x => a*G x) t = a*tiltMean μ H G t := by
  unfold tiltMean tiltIntegral
  simp_rw [← mul_assoc, mul_comm (Real.exp _) a,mul_assoc,integral_const_mul]
  ring

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkY_joint_measurable (N M : ℕ) (p : Fin N) :
    Measurable (fun a : BulkDisorder N M × NormalizedSpin N => bulkY N p a.1.2 a.2) :=
  (bulkY_measurable N p).comp (measurable_fst.snd.prodMk measurable_snd)

lemma bulkCouplingSlope_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Measurable (bulkCouplingSlope n M f v p u) := by
  apply Measurable.const_mul
  exact kernel_tiltMean_measurable (bulkSpinKernel n M)
    (H := fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)
    (Y := fun a x => bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable (bulkY_joint_measurable _ _ _)

lemma bulkCoupling_regular (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : BulkDisorder (n+1) M) :
    ContDiff ℝ 2 (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2) ∧
    ConvexOn ℝ univ (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2) ∧
    ∀ u, HasDerivAt (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2)
      (bulkCouplingSlope n M f v p u a) u := by
  let H := bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2
  let Y := fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x
  have hH : Measurable H := bulkHamiltonian_section_measurable _ _ _ _ a
  have hY : Measurable Y := (bulkY_measurable _ _).of_uncurry_left.const_mul _
  have he (u : ℝ) : Integrable (fun x => Real.exp (H x+u*Y x)) (unitSphereLaw (n+1)) := by
    have hi := bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    congr 1
    exact (bulkHamiltonian_update _ _ _ _ _ _ _ _).symm
  have hf : (fun u => bulkLogPartition n M f (Function.update v (p.val+1) u) a.1 a.2)=
      (fun u => Real.log (tiltPartition (unitSphereLaw (n+1)) (fun x => H x+u*Y x) 1)) := by
    funext u
    rw [bulkLogPartition_eq]
    congr 2
    funext x
    exact bulkHamiltonian_update _ _ _ _ _ _ _ _
  rw [hf]
  refine ⟨coupling_log_contDiff _ hH hY he,coupling_log_convex _ hH hY he,?_⟩
  intro u
  convert coupling_log_hasDerivAt (unitSphereLaw (n+1)) hH hY he u using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [bulkCouplingSlope,Y]
  rw [tiltMean_const_mul_general]
  congr 2
  funext x
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

lemma bulkExpectedLog_hasDerivAt (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Integrable (bulkCouplingSlope n M f v p u) (bulkDisorderLaw (n+1) M) ∧
    HasDerivAt (fun t => bulkExpectedLog n M f (Function.update v (p.val+1) t))
      (∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) u := by
  apply annealed_convex_hasDerivAt (bulkDisorderLaw (n+1) M)
    (fun t => (bulkLogPartition_measurable n M f _).aestronglyMeasurable)
    (fun t => (bulkCouplingSlope_measurable n M f v p t).aestronglyMeasurable)
    (fun t => (bulkLogPartition_memLp n M f _).integrable (by norm_num))
  exact ae_of_all _ fun a => (bulkCoupling_regular n M f v p a).2

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkThermal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkMarkNorm_memLp (n M : ℕ) :
    MemLp (fun a : BulkDisorder (n+1) M => ‖a.2‖) 2 (bulkDisorderLaw (n+1) M) := by
  exact ((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).comp_snd
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCouplingSlope_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) :
    |bulkCouplingSlope n M f v p u a|≤bulkCoefficient (n+1) p*‖a.2‖ := by
  unfold bulkCouplingSlope
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  apply mul_le_mul_of_nonneg_left _ (bulkCoefficient_pos n p).le
  exact tiltMean_bound_of_integrable (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkY_measurable _ _).of_uncurry_left
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a) (bulkY_bound _ _ _)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkEnergyDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCouplingSlope_eq_mean (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ)
    (a : BulkDisorder (n+1) M) :
    bulkCouplingSlope n M f v p u a = tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
      (fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x) 1 := by
  rw [tiltMean_const_mul_general]; rfl

lemma bulkEnergyDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    0≤bulkEnergyDeviation n M f v p u :=
  integral_nonneg fun _ => tiltMean_nonneg _ (fun _ => abs_nonneg _) _

lemma bulkEnergyDeviation_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkEnergyDeviation n M f v p u ≤
      2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
  let E := ∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M
  have hn := (bulkMarkNorm_memLp n M).integrable (by norm_num)
  have hE : |E|≤bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖ ∂bulkDisorderLaw (n+1) M :=
        integral_mono (bulkExpectedLog_hasDerivAt n M f v p u).1.abs (hn.const_mul _) (bulkCouplingSlope_bound n M f v p u)
      _ = _ := integral_const_mul _ _
  have hb (a : BulkDisorder (n+1) M) :
      tiltMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2)
        (fun x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-E|) 1 ≤
          bulkCoefficient (n+1) p*‖a.2‖+|E| := by
    have ht := tiltMean_bound_of_integrable (unitSphereLaw (n+1))
      (t:=1) (bulkHamiltonian_section_measurable _ _ _ _ a)
      (((bulkY_measurable _ _).of_uncurry_left.const_mul (bulkCoefficient (n+1) p)).sub_const E).abs
      (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f (Function.update v (p.val+1) u) a)
      (fun x => show abs (abs (bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x-E))≤bulkCoefficient (n+1) p*‖a.2‖+|E| from by
        rw [abs_abs]
        apply (abs_sub _ _).trans
        rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
        exact add_le_add (mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le) le_rfl)
    exact (le_abs_self _).trans ht
  calc
    _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖+|E| ∂bulkDisorderLaw (n+1) M :=
      integral_mono_of_nonneg (ae_of_all _ fun a => tiltMean_nonneg _ (fun _ => abs_nonneg _) _)
        ((hn.const_mul _).add (integrable_const |E|)) (ae_of_all _ hb)
    _ ≤ _ := by
      rw [integral_add (hn.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
      linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ParameterResampling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bulkParameterLaw_ae : ∀ᵐ v ∂bulkParameterLaw, ∀ j, v j∈Icc (1:ℝ) 2 := by
  rw [ae_all_iff]
  intro j
  have he : ∀ᵐ x ∂bulkParameterUniform, x∈Icc (1:ℝ) 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => ⟨hx.1.le,hx.2⟩
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => bulkParameterUniform) j).quasiMeasurePreserving.ae he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkParameterDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkFeature_joint_continuous (N : ℕ) :
    Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N => bulkFeature N a.1 a.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => fun_prop
  | inr i =>
    change Continuous (fun a : (ℕ→ℝ) × NormalizedSpin N =>
      bulkAmplitude N a.1 i.1*spinTensorFeature N (bulkDegree i.1) a.2 i.2)
    apply Continuous.mul
    · unfold bulkAmplitude; fun_prop
    · exact ((EuclideanSpace.proj i.2).continuous.comp (spinTensorFeature_continuous N (bulkDegree i.1))).comp continuous_snd

lemma bulkHamiltonian_parameter_continuous (N M : ℕ) (f : ℝ→ᵇℝ) :
    Continuous (fun a : ((ℕ→ℝ) × BulkDisorder N M) × NormalizedSpin N =>
      bulkHamiltonian N M f a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold bulkHamiltonian
  exact ((normalizedPatternEnergy_continuous N M f).comp
    (continuous_fst.snd.fst.prodMk continuous_snd)).add
    (((bulkFeature_joint_continuous N).comp (continuous_fst.fst.prodMk continuous_snd)).inner continuous_fst.snd.snd)

lemma bulkDegreeDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Measurable (bulkDegreeDeviation n M f p) := by
  let H := fun a : (ℕ→ℝ) × BulkDisorder (n+1) M =>
    bulkHamiltonian (n+1) M f a.1 a.2.1 a.2.2
  let Y := fun a : (ℕ→ℝ) × BulkDisorder (n+1) M =>
    fun x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x
  have hH : Measurable (Function.uncurry H) := (bulkHamiltonian_parameter_continuous (n+1) M f).measurable
  have hY : Measurable (Function.uncurry Y) :=
    ((bulkY_measurable (n+1) p).comp (measurable_fst.snd.snd.prodMk measurable_snd)).const_mul _
  have hE := (measurable_tiltMean_param (unitSphereLaw (n+1)) hH hY).stronglyMeasurable.integral_prod_right'
    (ν:=bulkDisorderLaw (n+1) M)
  have he := (measurable_tiltMean_param (unitSphereLaw (n+1)) hH
    (show Measurable (Function.uncurry (fun a x => |Y a x-∫ b, tiltMean (unitSphereLaw (n+1)) (H (a.1,b)) (Y (a.1,b)) 1 ∂bulkDisorderLaw (n+1) M|)) from
      (hY.sub (hE.measurable.comp measurable_fst.fst)).abs)).stronglyMeasurable.integral_prod_right'
        (ν:=bulkDisorderLaw (n+1) M) |>.measurable
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  unfold bulkDegreeDeviation bulkEnergyDeviation
  simp_rw [bulkCouplingSlope_eq_mean,Function.update_eq_self]
  rfl

lemma bulkDegreeDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) :
    0≤bulkDegreeDeviation n M f p v := bulkEnergyDeviation_nonneg n M f v p _

lemma bulkDegreeDeviation_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Integrable (bulkDegreeDeviation n M f p) bulkParameterLaw := by
  apply Integrable.of_bound (bulkDegreeDeviation_measurable n M f p).aestronglyMeasurable
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun v => by
    rw [Real.norm_eq_abs,abs_of_nonneg (bulkDegreeDeviation_nonneg n M f p v)]
    exact bulkEnergyDeviation_bound n M f v p _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkReplicaStein
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkNormalizedDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) :
    0≤bulkNormalizedDeviation n M f p v := by
  unfold bulkNormalizedDeviation
  exact div_nonneg (bulkDegreeDeviation_nonneg n M f p v)
    (mul_nonneg (bulkCoefficient_pos n p).le (by unfold bulkScale; positivity))

lemma bulkNormalizedDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Measurable (bulkNormalizedDeviation n M f p) := (bulkDegreeDeviation_measurable n M f p).div_const _

lemma bulkNormalizedDeviation_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) :
    Integrable (bulkNormalizedDeviation n M f p) bulkParameterLaw := (bulkDegreeDeviation_integrable n M f p).div_const _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DiagonalDeviation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma exists_slow_diagonal {b : ℕ→ℕ→ℝ} (hb : ∀ n p, 0≤b n p)
    (hlim : ∀ p, Tendsto (fun n => b n p) atTop (𝓝 0)) :
    ∃ J : ℕ→ℕ, Monotone J ∧ (∀ n, J n≤n) ∧ Tendsto J atTop atTop ∧
      Tendsto (fun n => ∑ p∈Finset.range (J n), b n p) atTop (𝓝 0) := by
  classical
  let P := fun n k => ∀ m≥n, (∑ p∈Finset.range k, b m p)≤1/(k+1:ℝ)
  have hP0 (n) : P n 0 := by intro m hm; simp
  let J := fun n => Nat.findGreatest (P n) n
  have hJ (n) : J n≤n := Nat.findGreatest_le _
  have hJP (n) : P n (J n) := Nat.findGreatest_spec (Nat.zero_le n) (hP0 n)
  have hJmono : Monotone J := by
    intro m n hmn
    exact Nat.findGreatest_mono (fun k hk l hl => hk l (hmn.trans hl)) hmn
  have hPJ (k) : ∀ᶠ n in atTop, k≤J n := by
    have hs : Tendsto (fun n => ∑ p∈Finset.range k, b n p) atTop (𝓝 (0:ℝ)) := by
      simpa using tendsto_finsetSum (Finset.range k) (fun p _ => hlim p)
    have he := hs.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(k+1:ℝ)))
    obtain ⟨N,hN⟩ := eventually_atTop.1 he
    filter_upwards [eventually_ge_atTop (max N k)] with n hn
    exact Nat.le_findGreatest ((le_max_right N k).trans hn)
      (fun m hm => (hN m ((le_max_left N k).trans (hn.trans hm))).le)
  have hJlim : Tendsto J atTop atTop := tendsto_atTop.2 hPJ
  refine ⟨J,hJmono,hJ,hJlim,?_⟩
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun p _ => hb n p))
    (fun n => hJP n n le_rfl)
  have hh : Tendsto (fun n => (J n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hJlim).atTop_add tendsto_const_nhds
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hh

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (d : ℕ→ℕ→X→ℝ)

lemma diagonalDeviationThreshold_pos (J : ℕ→ℕ) (n : ℕ) :
    0<diagonalDeviationThreshold μ d J n := by
  unfold diagonalDeviationThreshold
  exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)

lemma diagonalGoodSet_measurable (hm : ∀ n p, Measurable (d n p)) (J : ℕ→ℕ) (n : ℕ) :
    MeasurableSet (diagonalGoodSet μ d J n) := by
  unfold diagonalGoodSet
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_le (hm n p) measurable_const

lemma diagonalGoodSet_compl_bound [IsProbabilityMeasure μ] (hn : ∀ n p v, 0≤d n p v)
    (hi : ∀ n p, Integrable (d n p) μ) (J : ℕ→ℕ) (n : ℕ) :
    μ.real (diagonalGoodSet μ d J n)ᶜ ≤ Real.sqrt (diagonalDeviationMass μ d J n) := by
  let S := fun v => ∑ p∈Finset.range (J n), d n p v
  have hSn (v) : 0≤S v := Finset.sum_nonneg fun p _ => hn n p v
  have hSi : Integrable S μ := integrable_finsetSum _ (fun p _ => hi n p)
  have hSm : ∫ v, S v ∂μ = diagonalDeviationMass μ d J n := integral_finsetSum _ (fun p _ => hi n p)
  have ha : 0≤diagonalDeviationMass μ d J n := hSm ▸ integral_nonneg hSn
  have hs : (diagonalGoodSet μ d J n)ᶜ ⊆ {v | diagonalDeviationThreshold μ d J n≤S v} := by
    intro v hv
    simp only [diagonalGoodSet,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] at hv
    obtain ⟨p,hp,hpv⟩ := hv
    exact hpv.le.trans (Finset.single_le_sum (fun q _ => hn n q v) hp)
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hSn) hSi
    (diagonalDeviationThreshold μ d J n)
  rw [hSm] at hb
  have he := diagonalDeviationThreshold_pos μ d J n
  calc
    _ ≤ μ.real {v | diagonalDeviationThreshold μ d J n≤S v} := measureReal_mono hs
    _ ≤ diagonalDeviationMass μ d J n/diagonalDeviationThreshold μ d J n :=
      (le_div_iff₀ he).2 (by simpa [mul_comm] using hb)
    _ ≤ Real.sqrt (diagonalDeviationMass μ d J n) := by
      apply (div_le_iff₀ he).2
      dsimp [diagonalDeviationThreshold]
      nlinarith [Real.sq_sqrt ha, mul_nonneg (Real.sqrt_nonneg (diagonalDeviationMass μ d J n))
        (by positivity : (0:ℝ)≤1/(n+1:ℝ))]

lemma diagonalGoodSet_compl_tendsto [IsProbabilityMeasure μ] (hn : ∀ n p v, 0≤d n p v)
    (hi : ∀ n p, Integrable (d n p) μ) (J : ℕ→ℕ)
    (hJ : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0)) :
    Tendsto (fun n => μ.real (diagonalGoodSet μ d J n)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg)
    (diagonalGoodSet_compl_bound μ d hn hi J)
  simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hJ

lemma diagonalDeviationThreshold_tendsto (J : ℕ→ℕ)
    (hJ : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0)) :
    Tendsto (diagonalDeviationThreshold μ d J) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  change Tendsto (fun n => Real.sqrt (diagonalDeviationMass μ d J n)+1/(n+1:ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_zero,zero_add] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hJ).add h1

lemma diagonalGoodSet_deviation_tendsto (hn : ∀ n p v, 0≤d n p v) (J : ℕ→ℕ)
    (hJ : Tendsto J atTop atTop) (hmass : Tendsto (diagonalDeviationMass μ d J) atTop (𝓝 0))
    (v : ℕ→X) (hv : ∀ᶠ n in atTop, v n∈diagonalGoodSet μ d J n) (p : ℕ) :
    Tendsto (fun n => d n p (v n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => hn n p (v n)) _
    (diagonalDeviationThreshold_tendsto μ d J hmass)
  filter_upwards [hv, hJ.eventually (eventually_gt_atTop p)] with n hn hnp
  exact hn p (Finset.mem_range.2 hnp)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkGoodParameters
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkDeviationAt_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) (v : ℕ→ℝ) :
    0≤bulkDeviationAt n M f p v := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_nonneg n M f _ v
  · exact le_rfl

lemma bulkDeviationAt_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Measurable (bulkDeviationAt n M f p) := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_measurable n M f _
  · exact measurable_const

lemma bulkDeviationAt_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Integrable (bulkDeviationAt n M f p) bulkParameterLaw := by
  unfold bulkDeviationAt
  split_ifs with h
  · exact bulkNormalizedDeviation_integrable n M f _
  · exact integrable_const _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkCompactGG
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkJointDeviation_nonneg (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) (v : ℕ→ℝ) :
    0≤bulkJointDeviation α f n p v :=
  add_nonneg (bulkDeviationAt_nonneg _ _ _ _ _) (bulkDeviationAt_nonneg _ _ _ _ _)
lemma bulkJointDeviation_measurable (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) :
    Measurable (bulkJointDeviation α f n p) :=
  (bulkDeviationAt_measurable _ _ _ _).add (bulkDeviationAt_measurable _ _ _ _)
lemma bulkJointDeviation_integrable (α : ℝ) (f : ℝ→ᵇℝ) (n p : ℕ) :
    Integrable (bulkJointDeviation α f n p) bulkParameterLaw :=
  (bulkDeviationAt_integrable _ _ _ _).add (bulkDeviationAt_integrable _ _ _ _)

lemma bulkJointDeviation_integral_tendsto {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n => ∫ v, bulkJointDeviation α f n p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  have h₁ := bulkDeviationAt_integral_tendsto (fun n => patternCount α (n+1)) f hα
    (fun n => Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))) p
  have h₂ := omittedBulkDeviation_integral_tendsto hα f p
  have he (n : ℕ) : (∫ v, bulkJointDeviation α f n p v ∂bulkParameterLaw) =
      (∫ v, bulkDeviationAt n (patternCount α (n+1)) f p v ∂bulkParameterLaw) +
        ∫ v, omittedBulkDeviation α f n p v ∂bulkParameterLaw :=
    integral_add (bulkDeviationAt_integrable _ _ _ _) (bulkDeviationAt_integrable _ _ _ _)
  simp_rw [he]
  simpa only [add_zero] using h₁.add h₂

lemma bulkJointGoodSet_measurable (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    MeasurableSet (bulkJointGoodSet α f J n) := by
  refine (diagonalGoodSet_measurable _ _ (bulkJointDeviation_measurable α f) J n).inter ?_
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun p => (measurable_pi_apply p) measurableSet_Icc

lemma bulkJointGoodSet_compl_measure (α : ℝ) (f : ℝ→ᵇℝ) (J : ℕ→ℕ) (n : ℕ) :
    bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ =
      bulkParameterLaw.real (diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n)ᶜ := by
  simp only [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [bulkParameterLaw_ae] with v hv
  apply propext
  change ¬(v∈diagonalGoodSet bulkParameterLaw (bulkJointDeviation α f) J n ∧ ∀ p, v p∈Icc (1:ℝ) 2) ↔ _
  exact not_congr ⟨fun h => h.1, fun h => ⟨h,hv⟩⟩

theorem exists_bulkJointGoodParameters {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) :
    ∃ J : ℕ→ℕ, Monotone J ∧ (∀ n, J n≤n) ∧ Tendsto J atTop atTop ∧
      (∀ n, MeasurableSet (bulkJointGoodSet α f J n)) ∧
      Tendsto (fun n => bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ) atTop (𝓝 0) ∧
      (∀ v : ℕ→(ℕ→ℝ), (∀ᶠ n in atTop, v n∈bulkJointGoodSet α f J n) →
        ∀ p, Tendsto (fun n => bulkDeviationAt n (patternCount α (n+1)) f p (v n)) atTop (𝓝 0) ∧
          Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0)) := by
  have hn := bulkJointDeviation_nonneg α f
  have hi := bulkJointDeviation_integrable α f
  obtain ⟨J,hmon,hbound,hlim,hmass⟩ := exists_slow_diagonal
    (fun n p => integral_nonneg (hn n p)) (bulkJointDeviation_integral_tendsto hα f)
  refine ⟨J,hmon,hbound,hlim,bulkJointGoodSet_measurable α f J,?_,?_⟩
  · simpa only [bulkJointGoodSet_compl_measure] using
      diagonalGoodSet_compl_tendsto bulkParameterLaw (bulkJointDeviation α f) hn hi J hmass
  · intro v hv p
    have hd := diagonalGoodSet_deviation_tendsto bulkParameterLaw (bulkJointDeviation α f) hn J hlim hmass v
      (hv.mono fun n h => h.1) p
    constructor
    · exact squeeze_zero (fun n => bulkDeviationAt_nonneg _ _ _ _ _)
        (fun n => le_add_of_nonneg_right (bulkDeviationAt_nonneg _ _ _ _ _)) hd
    · exact squeeze_zero (fun n => bulkDeviationAt_nonneg _ _ _ _ _)
        (fun n => le_add_of_nonneg_left (bulkDeviationAt_nonneg _ _ _ _ _)) hd

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCounts
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma exists_cavityGoodParameters {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) :
    Nonempty (CavityGoodParameters α f) := by
  obtain ⟨J,hm,hl,ht,hms,hma,hd⟩:=exists_bulkJointGoodParameters hα f
  exact ⟨⟨J,hm,hl,ht,hms,hma,hd⟩⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCovarianceComparison
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bounded_log_partition_path_derivative {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (H D : ℝ→S→ℝ)
    (hH : ∀ t,Measurable (H t)) (hD : ∀ t,Measurable (D t))
    {A B : ℝ} (hA : ∀ t s,|H t s|≤A) (hB : ∀ t s,|D t s|≤B)
    (hd : ∀ t s,HasDerivAt (fun u=>H u s) (D t s) t) (t : ℝ) :
    HasDerivAt (fun u=>Real.log (tiltPartition μ (H u) 1))
      (tiltMean μ (H t) (D t) 1) t := by
  have hi (u : ℝ) : Integrable (fun s=>Real.exp (H u s)) μ :=
    Integrable.of_bound (hH u).exp.aestronglyMeasurable (Real.exp A)
      (ae_of_all _ fun s=>by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (le_abs_self _ |>.trans (hA u s)))
  have hp (u : ℝ) : 0<∫ s,Real.exp (H u s) ∂μ := by
    apply integral_pos_iff_support_of_nonneg (fun s=>(Real.exp_pos _).le) (hi u) |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u s=>Real.exp (H u s)) (F':=fun u s=>Real.exp (H u s)*D u s)
    (s:=univ) (bound:=fun _ : S=>Real.exp A*B) (x₀:=t)
    (by simp : univ∈𝓝 t) (Eventually.of_forall fun u=>(hH u).exp.aestronglyMeasurable)
    (hi t) (((hH t).exp.mul (hD t)).aestronglyMeasurable)
    (ae_of_all _ fun s u _=>by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (le_abs_self _ |>.trans (hA u s)))
        (hB u s) (abs_nonneg _) (Real.exp_pos _).le)
    (integrable_const _) (ae_of_all _ fun s u _=>(hd u s).exp)
  simpa only [tiltMean,tiltIntegral,tiltPartition,one_mul] using hh.2.log (hp t).ne'

variable {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]

lemma cavityGaussianRotation_norm {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {C : ℝ} (_hC : 0≤C)
    (hV : ∀ s,‖V s‖≤C) (hW : ∀ s,‖W s‖≤C) (t : ℝ) (s : S) :
    ‖cavityGaussianRotation V W t s‖≤2*C := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have h1 := mul_le_mul (Real.abs_cos_le_one t) (hV s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul (Real.abs_sin_le_one t) (hW s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

lemma cavityGaussianRotationVelocity_norm {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {C : ℝ} (_hC : 0≤C)
    (hV : ∀ s,‖V s‖≤C) (hW : ∀ s,‖W s‖≤C) (t : ℝ) (s : S) :
    ‖cavityGaussianRotationVelocity V W t s‖≤2*C := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_neg]
  have h1 := mul_le_mul (Real.abs_sin_le_one t) (hV s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul (Real.abs_cos_le_one t) (hW s) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

variable (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
  (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
  {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
  (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C)

include hH hV hW hA hC hHA hVC hWC

omit hH hV hW hA hC hHA hVC hWC in
lemma cavityGaussianRotation_log_derivative
    {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V W : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C : ℝ} (_hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C)
    (g : EuclideanSpace ℝ I) (t : ℝ) :
    HasDerivAt (fun u=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1))
      (tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
        (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1) t := by
  have hv (u : ℝ) : Measurable (cavityGaussianRotation V W u) := by unfold cavityGaussianRotation; fun_prop
  have hw (u : ℝ) : Measurable (cavityGaussianRotationVelocity V W u) := by unfold cavityGaussianRotationVelocity; fun_prop
  apply bounded_log_partition_path_derivative μ _ _
    (fun u=>hH.add ((hv u).inner measurable_const))
    (fun u=>(hw u).inner measurable_const)
    (A:=A+2*C*‖g‖) (B:=2*C*‖g‖)
  · intro u s
    exact (abs_add_le _ _).trans (add_le_add (hHA s)
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (cavityGaussianRotation_norm hC hVC hWC u s) (norm_nonneg g))))
  · intro u s
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (cavityGaussianRotationVelocity_norm hC hVC hWC u s) (norm_nonneg g))
  · intro u s
    simpa [cavityGaussianRotation,cavityGaussianRotationVelocity,inner_add_left,inner_smul_left] using
      ((((Real.hasDerivAt_cos u).mul_const (inner ℝ (V s) g)).add
        ((Real.hasDerivAt_sin u).mul_const (inner ℝ (W s) g))).const_add (H s))

lemma cavityGaussianRotation_mean_derivative (t : ℝ) :
    HasDerivAt (fun u=>∫ g,Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1) ∂stdGaussian (EuclideanSpace ℝ I))
      (∫ g,tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
        (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1
        ∂stdGaussian (EuclideanSpace ℝ I)) t := by
  have hv (u : ℝ) : Measurable (cavityGaussianRotation V W u) := by unfold cavityGaussianRotation; fun_prop
  have hw (u : ℝ) : Measurable (cavityGaussianRotationVelocity V W u) := by unfold cavityGaussianRotationVelocity; fun_prop
  have hh (u : ℝ) : Measurable (fun p : EuclideanSpace ℝ I×S=>
      H p.2+inner ℝ (cavityGaussianRotation V W u p.2) p.1) :=
    (hH.comp measurable_snd).add (((hv u).comp measurable_snd).inner measurable_fst)
  have hd (u : ℝ) : Measurable (fun p : EuclideanSpace ℝ I×S=>
      inner ℝ (cavityGaussianRotationVelocity V W u p.2) p.1) :=
    ((hw u).comp measurable_snd).inner measurable_fst
  have hm (u : ℝ) : Measurable (fun g=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)) :=
    (kernel_tiltPartition_measurable (Kernel.const _ μ) (hh u)).log
  have hmd (u : ℝ) : Measurable (fun g=>tiltMean μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g)
      (fun s=>inner ℝ (cavityGaussianRotationVelocity V W u s) g) 1) :=
    kernel_tiltMean_measurable (Kernel.const _ μ) (hh u) (hd u)
  have hn : Integrable (fun g : EuclideanSpace ℝ I=>‖g‖) (stdGaussian (EuclideanSpace ℝ I)) :=
    ((IsGaussian.memLp_two_id (μ:=stdGaussian (EuclideanSpace ℝ I))).integrable (by norm_num)).norm
  have hb (u : ℝ) (g : EuclideanSpace ℝ I) :
      |Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)|≤A+2*C*‖g‖ :=
    tilt_log_partition_bound μ (hH.add ((hv u).inner measurable_const)) (A:=A+2*C*‖g‖) (by positivity) (fun s=>
      (abs_add_le _ _).trans (add_le_add (hHA s) ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (cavityGaussianRotation_norm hC hVC hWC u s) (norm_nonneg g)))))
  have hi (u : ℝ) : Integrable (fun g=>Real.log (tiltPartition μ
      (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1)) (stdGaussian (EuclideanSpace ℝ I)) :=
    ((integrable_const A).add (hn.const_mul (2*C))).mono' (hm u).aestronglyMeasurable
      (ae_of_all _ fun g=>by simpa only [Real.norm_eq_abs,Pi.add_apply] using hb u g)
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun u g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g) 1))
    (F':=fun u g=>tiltMean μ (fun s=>H s+inner ℝ (cavityGaussianRotation V W u s) g)
      (fun s=>inner ℝ (cavityGaussianRotationVelocity V W u s) g) 1)
    (s:=univ) (bound:=fun g : EuclideanSpace ℝ I=>2*C*‖g‖) (x₀:=t)
    (by simp : univ∈𝓝 t) (Eventually.of_forall fun u=>(hm u).aestronglyMeasurable)
    (hi t) (hmd t).aestronglyMeasurable
    (ae_of_all _ fun g u _=>by
      rw [Real.norm_eq_abs]
      exact tiltMean_bound_general μ (hH.add ((hv u).inner measurable_const))
        ((hw u).inner measurable_const) (C:=2*C*‖g‖) (by positivity) (fun s=>(abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (cavityGaussianRotationVelocity_norm hC hVC hWC u s) (norm_nonneg g))))
    (hn.const_mul (2*C)) (ae_of_all _ fun g u _=>
      cavityGaussianRotation_log_derivative μ hH hV hW hA hC hHA hVC hWC g u)
  exact ht.2
omit hH hV hW hA hC hHA hVC hWC in
lemma cavityGaussianRotation_cross_covariance_bound
    {I : Type} {S : Type*} [Fintype I] [MeasurableSpace S]
    {V W : S→EuclideanSpace ℝ I} {ε : ℝ} (_hε : 0≤ε)
    (horth : ∀ x y,inner ℝ (V x) (W y)=0)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε)
    (t : ℝ) (x y : S) :
    |inner ℝ (cavityGaussianRotationVelocity V W t x) (cavityGaussianRotation V W t y)|≤ε := by
  have hr : inner ℝ (W x) (V y)=0 := by rw [real_inner_comm,horth]
  have he : inner ℝ (cavityGaussianRotationVelocity V W t x) (cavityGaussianRotation V W t y)=
      Real.sin t*Real.cos t*(inner ℝ (W x) (W y)-inner ℝ (V x) (V y)) := by
    simp only [cavityGaussianRotation,cavityGaussianRotationVelocity,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,conj_trivial,horth,hr]
    ring
  rw [he,abs_mul,abs_mul]
  have h1 : |Real.sin t| * |Real.cos t| ≤ 1 := by
    nlinarith [Real.abs_sin_le_one t,Real.abs_cos_le_one t,abs_nonneg (Real.sin t),abs_nonneg (Real.cos t)]
  exact (mul_le_mul h1 (hcov x y) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul ε)

theorem euclideanGaussian_covariance_comparison {ε : ℝ} (hε : 0≤ε)
    (horth : ∀ x y,inner ℝ (V x) (W y)=0)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (W s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I)|≤Real.pi*ε := by
  let F : ℝ→ℝ:=fun t=>∫ g,Real.log (tiltPartition μ
    (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g) 1) ∂stdGaussian (EuclideanSpace ℝ I)
  let D : ℝ→ℝ:=fun t=>∫ g,tiltMean μ
    (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g)
    (fun s=>inner ℝ (cavityGaussianRotationVelocity V W t s) g) 1 ∂stdGaussian (EuclideanSpace ℝ I)
  have hd (t : ℝ) : HasDerivAt F (D t) t :=
    cavityGaussianRotation_mean_derivative μ hH hV hW hA hC hHA hVC hWC t
  have hb (t : ℝ) : ‖D t‖≤2*ε := by
    have hv : Measurable (cavityGaussianRotation V W t) := by unfold cavityGaussianRotation; fun_prop
    have hw : Measurable (cavityGaussianRotationVelocity V W t) := by unfold cavityGaussianRotationVelocity; fun_prop
    have hc := cavityGaussianRotation_cross_covariance_bound (V:=V) (W:=W) hε horth hcov t
    change ‖∫ g,tiltMean μ _ _ 1 ∂stdGaussian (EuclideanSpace ℝ I)‖≤_
    rw [euclideanGaussian_tiltMean_ibp μ hH hv hw hHA
      (fun x=>pow_le_pow_left₀ (norm_nonneg _) (cavityGaussianRotation_norm hC hVC hWC t x) 2)
      (fun x=>pow_le_pow_left₀ (norm_nonneg _) (cavityGaussianRotationVelocity_norm hC hVC hWC t x) 2)]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=stdGaussian (EuclideanSpace ℝ I)) (C:=2*ε) (ae_of_all _ fun g=>by
        have hh : Measurable (fun s=>H s+inner ℝ (cavityGaussianRotation V W t s) g) :=
          hH.add (hv.inner measurable_const)
        have h1 := tiltMean_bound_general μ (t:=1) hh (hw.inner hv) hε (fun x=>hc x x)
        have h2 := tiltMean_bound_general (Measure.pi (fun _ : Fin 2=>μ)) (t:=1)
          (replicaPotential_measurable hh 2)
          ((hw.comp (measurable_pi_apply 1)).inner (hv.comp (measurable_pi_apply 0))) hε
          (fun xs=>hc (xs 1) (xs 0))
        rw [Real.norm_eq_abs]
        apply (abs_sub _ _).trans
        exact (add_le_add h1 h2).trans_eq (by ring))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t∈Icc (0:ℝ) (Real.pi/2))=>(hd t).hasDerivWithinAt)
    (fun t _=>hb t) (convex_Icc (0:ℝ) (Real.pi/2))
    (show (0:ℝ)∈Icc (0:ℝ) (Real.pi/2) by constructor; rfl; positivity)
    (show Real.pi/2∈Icc (0:ℝ) (Real.pi/2) by constructor; positivity; rfl)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg (by positivity : 0≤Real.pi/2)] at hm
  convert hm using 1
  · simp [F,cavityGaussianRotation]
  · ring
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityPerturbationCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bulkScale_sq_eq_rpow (N : ℕ) : bulkScale N^2=(N:ℝ)^((3:ℝ)/4) := by
  unfold bulkScale
  rw [←Real.rpow_mul_natCast (Nat.cast_nonneg N)]
  norm_num

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

section Sum
variable {I J : Type} [Fintype I] [Fintype J]
omit [Fintype I] [Fintype J] in
lemma gaussianSumSplit_measurable : Measurable (gaussianSumSplit (I:=I) (J:=J)) := by
  unfold gaussianSumSplit
  fun_prop
lemma gaussianInl_measurable : Measurable (gaussianInl (I:=I) (J:=J)) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop
lemma gaussianInr_measurable : Measurable (gaussianInr (I:=I) (J:=J)) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop
lemma gaussianSumSplit_preserving :
    MeasurePreserving (gaussianSumSplit (I:=I) (J:=J)) (stdGaussian (EuclideanSpace ℝ (I⊕J)))
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
  have hI : MeasurePreserving (WithLp.toLp 2 : (I→ℝ)→EuclideanSpace ℝ I)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ I)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hJ : MeasurePreserving (WithLp.toLp 2 : (J→ℝ)→EuclideanSpace ℝ J)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ J)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianSumSplit_measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map gaussianSumSplit_measurable (PiLp.continuous_toLp 2 _).measurable]
  convert ((hI.prod hJ).comp (measurePreserving_sumPiEquivProdPi (fun _ : I⊕J=>gaussianReal 0 1))).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  rfl
lemma gaussianInl_inner (x y : EuclideanSpace ℝ I) :
    inner ℝ (gaussianInl (J:=J) x) (gaussianInl y)=inner ℝ x y := by
  change (∑ i, gaussianInl (J:=J) y i*gaussianInl x i)=_
  simp only [Fintype.sum_sum_type,gaussianInl,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,add_zero]
  rfl
lemma gaussianInr_inner (x y : EuclideanSpace ℝ J) :
    inner ℝ (gaussianInr (I:=I) x) (gaussianInr y)=inner ℝ x y := by
  change (∑ i, gaussianInr (I:=I) y i*gaussianInr x i)=_
  simp only [Fintype.sum_sum_type,gaussianInr,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,zero_add]
  rfl
lemma gaussianInl_Inr_inner (x : EuclideanSpace ℝ I) (y : EuclideanSpace ℝ J) :
    inner ℝ (gaussianInl x) (gaussianInr y)=0 := by
  change (∑ i, gaussianInr (I:=I) y i*gaussianInl x i)=_
  simp [Fintype.sum_sum_type,gaussianInl,gaussianInr]
lemma gaussianInl_norm (x : EuclideanSpace ℝ I) : ‖gaussianInl (J:=J) x‖=‖x‖ := by
  have h:=gaussianInl_inner (J:=J) x x
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x,norm_nonneg (gaussianInl (J:=J) x)]
lemma gaussianInr_norm (x : EuclideanSpace ℝ J) : ‖gaussianInr (I:=I) x‖=‖x‖ := by
  have h:=gaussianInr_inner (I:=I) x x
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg x,norm_nonneg (gaussianInr (I:=I) x)]
lemma gaussianInl_linear (x : EuclideanSpace ℝ I) (g : EuclideanSpace ℝ (I⊕J)) :
    inner ℝ (gaussianInl x) g=inner ℝ x (gaussianSumSplit g).1 := by
  change (∑ i,g i*gaussianInl x i)=_
  simp only [Fintype.sum_sum_type,gaussianInl,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,add_zero]
  rfl
lemma gaussianInr_linear (x : EuclideanSpace ℝ J) (g : EuclideanSpace ℝ (I⊕J)) :
    inner ℝ (gaussianInr x) g=inner ℝ x (gaussianSumSplit g).2 := by
  change (∑ i,g i*gaussianInr x i)=_
  simp only [Fintype.sum_sum_type,gaussianInr,PiLp.toLp_apply,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,zero_add]
  rfl
end Sum

lemma gaussianLogPartition_measurable_finite {I S : Type*} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) :
    Measurable (fun g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)) := by
  apply Measurable.log
  have hm : Measurable (fun p : EuclideanSpace ℝ I×S=>H p.2+inner ℝ (V p.2) p.1) :=
    (hH.comp measurable_snd).add ((hV.comp measurable_snd).inner measurable_fst)
  simpa only [tiltPartition,one_mul] using hm.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma gaussianInl_log_integral {I J S : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) :
    (∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (gaussianInl (J:=J) (V s)) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))=
    ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ I) := by
  simp_rw [gaussianInl_linear]
  have hp : MeasurePreserving (fun g : EuclideanSpace ℝ (I⊕J)=>(gaussianSumSplit g).1)
      (stdGaussian (EuclideanSpace ℝ (I⊕J))) (stdGaussian (EuclideanSpace ℝ I)) :=
    measurePreserving_fst.comp gaussianSumSplit_preserving
  have he:=integral_map (μ:=stdGaussian (EuclideanSpace ℝ (I⊕J))) hp.measurable.aemeasurable (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

lemma gaussianInr_log_integral {I J S : Type} [Fintype I] [Fintype J] [MeasurableSpace S]
    (μ : Measure S) [SFinite μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ J}
    (hH : Measurable H) (hV : Measurable V) :
    (∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (gaussianInr (I:=I) (V s)) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))=
    ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
      ∂stdGaussian (EuclideanSpace ℝ J) := by
  simp_rw [gaussianInr_linear]
  have hp : MeasurePreserving (fun g : EuclideanSpace ℝ (I⊕J)=>(gaussianSumSplit g).2)
      (stdGaussian (EuclideanSpace ℝ (I⊕J))) (stdGaussian (EuclideanSpace ℝ J)) :=
    measurePreserving_snd.comp gaussianSumSplit_preserving
  have he:=integral_map (μ:=stdGaussian (EuclideanSpace ℝ (I⊕J))) hp.measurable.aemeasurable (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

theorem independentGaussian_covariance_comparison {I J S : Type} [Fintype I] [Fintype J]
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} {V : S→EuclideanSpace ℝ I} {W : S→EuclideanSpace ℝ J}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C ε : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hVC : ∀ s,‖V s‖≤C) (hWC : ∀ s,‖W s‖≤C) (hε : 0≤ε)
    (hcov : ∀ x y,|inner ℝ (W x) (W y)-inner ℝ (V x) (V y)|≤ε) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (W s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ J))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1)
        ∂stdGaussian (EuclideanSpace ℝ I)|≤Real.pi*ε := by
  have hv : Measurable (fun s=>gaussianInl (J:=J) (V s)) := gaussianInl_measurable.comp hV
  have hw : Measurable (fun s=>gaussianInr (I:=I) (W s)) := gaussianInr_measurable.comp hW
  have ht:=euclideanGaussian_covariance_comparison μ hH hv hw hA hC hHA
    (fun s=>by simpa only [gaussianInl_norm] using hVC s)
    (fun s=>by simpa only [gaussianInr_norm] using hWC s) hε
    (fun x y=>gaussianInl_Inr_inner (V x) (W y))
    (fun x y=>by simpa only [gaussianInr_inner,gaussianInl_inner] using hcov x y)
  rwa [gaussianInl_log_integral μ hH hV,gaussianInr_log_integral μ hH hW] at ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma cavityShell_measurable (L : ℕ) : MeasurableSet (cavityShell L) := by
  exact (isClosed_Icc.preimage (show Continuous (fun z : Spin L=>‖z‖^2) from continuous_norm.pow 2)).measurableSet

lemma stdGaussian_open_pos (k : ℕ) {U : Set (Spin (k+1))} (ho : IsOpen U) (hn : U.Nonempty) :
    0 < stdGaussian (Spin (k+1)) U := by
  have ha : (volume : Measure (Spin (k+1))) ≪ stdGaussian (Spin (k+1)) := by
    rw [←canonicalRadialMass_eq_stdGaussian]
    apply withDensity_absolutelyContinuous' (canonicalRadialDensity_continuous k 1).measurable.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x=>ne_of_gt (ENNReal.ofReal_pos.mpr (canonicalRadialDensity_pos k 1 x))
  exact pos_iff_ne_zero.mpr (fun h=>ne_of_gt (ho.measure_pos volume hn) (ha h))

lemma cavityShellMass_pos (k : ℕ) : 0 < cavityShellMass k := by
  have hu : ({z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} : Set (Spin (k+1))).Nonempty := by
    let z : Spin (k+1) := EuclideanSpace.single 0 (Real.sqrt ((k+1:ℕ)+(1/2:ℝ)))
    have hz : ‖z‖^2=(k+1:ℕ)+(1/2:ℝ) := by
      simp only [z,PiLp.norm_single,Real.norm_eq_abs,sq_abs]
      exact Real.sq_sqrt (by positivity)
    exact ⟨z,by change (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1; rw [hz]; constructor <;> linarith⟩
  have ho : IsOpen {z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} :=
    (isOpen_lt continuous_const (continuous_norm.pow 2)).inter (isOpen_lt (continuous_norm.pow 2) continuous_const)
  have hp := (stdGaussian_open_pos k ho hu).trans_le (measure_mono (show
    {z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} ⊆ cavityShell (k+1) from fun z hz=>⟨hz.1.le,hz.2.le⟩))
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

lemma cavityShellMass_le_one (k : ℕ) : cavityShellMass k≤1 := by
  exact measureReal_le_one

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityProductLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma cavity_gaussian_joint_log_integrable {A S I : Type*} [MeasurableSpace A]
    [MeasurableSpace S] [Fintype I] (Q : Measure A) [IsProbabilityMeasure Q]
    (μ : Measure S) [IsProbabilityMeasure μ] (H : A→S→ℝ) (V : S→EuclideanSpace ℝ I)
    (hH : Measurable (Function.uncurry H)) (hV : Measurable V)
    {C B : ℝ} (hC : 0≤C) (hB : 0≤B) (hHC : ∀ a x,|H a x|≤C) (hVB : ∀ x,‖V x‖≤B) :
    Integrable (fun p : A×EuclideanSpace ℝ I=>Real.log (tiltPartition μ
      (fun x=>H p.1 x+inner ℝ (V x) p.2) 1)) (Q.prod (stdGaussian (EuclideanSpace ℝ I))) := by
  have hi:=((integrable_const C).add
    ((IsGaussian.integrable_id (μ:=stdGaussian (EuclideanSpace ℝ I))).norm.const_mul B)).comp_snd Q
  have hm : Measurable (fun p : (A×EuclideanSpace ℝ I)×S=>H p.1.1 p.2+inner ℝ (V p.2) p.1.2) :=
    (hH.comp (measurable_fst.fst.prodMk measurable_snd)).add
      ((hV.comp measurable_snd).inner measurable_fst.snd)
  apply hi.mono' (by
    simpa only [tiltPartition,one_mul] using hm.exp.stronglyMeasurable.integral_prod_right'.measurable.log.aestronglyMeasurable)
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  apply tilt_log_partition_bound μ
    ((hH.comp (measurable_const.prodMk measurable_id)).add (hV.inner measurable_const))
    (add_nonneg hC (mul_nonneg hB (norm_nonneg _)))
  intro x
  exact (abs_add_le _ _).trans (add_le_add (hHC p.1 x)
    ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hVB x) (norm_nonneg _))))

lemma bulkExpectedLog_nested (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkExpectedLog n M f v=∫ a,∫ g,Real.log (tiltPartition (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 1) ∂stdGaussian (BulkMark (n+1))
      ∂finitePatternRowsLaw (n+1) M := by
  unfold bulkExpectedLog bulkDisorderLaw
  rw [integral_prod _ ((bulkLogPartition_memLp n M f v).integrable (by norm_num))]
  simp_rw [bulkLogPartition_eq]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGoodFreshLower
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction


lemma bulkExpectedLog_parameter_measurable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (bulkExpectedLog n M f) := by
  have hm : Measurable (fun p : (ℕ→ℝ)×BulkDisorder (n+1) M=>
      bulkLogPartition n M f p.1 p.2.1 p.2.2) := by
    simp_rw [bulkLogPartition_eq]
    simpa only [tiltPartition,one_mul] using
      (bulkHamiltonian_parameter_continuous (n+1) M f).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma bulkExpectedLog_box_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hv : ∀ p,|v (p+1)|≤2) :
    |bulkExpectedLog n M f v|≤M*‖f‖+2*|bulkScale (n+1)| *
      ∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M := by
  have hb : bulkFeatureBound (n+1) v≤2*|bulkScale (n+1)| := by
    have hh:=bulkFeatureBound_sq_le (n+1) v (by norm_num : (0:ℝ)≤2) hv
    have hs:=sq_abs (bulkScale (n+1))
    nlinarith [Real.sqrt_nonneg (∑ p,bulkAmplitude (n+1) v p^2),abs_nonneg (bulkScale (n+1))]
  let Q:=bulkDisorderLaw (n+1) M
  have hi : Integrable (fun a : BulkDisorder (n+1) M=>
      M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖) Q :=
    (integrable_const _).add ((bulkMarkNorm_integrable (n+1) M).const_mul _)
  calc
    _≤∫ a : BulkDisorder (n+1) M,|bulkLogPartition n M f v a.1 a.2| ∂Q := abs_integral_le_integral_abs
    _≤∫ a : BulkDisorder (n+1) M,M*‖f‖+2*|bulkScale (n+1)| *‖a.2‖ ∂Q := by
      apply integral_mono ((bulkLogPartition_memLp n M f v).integrable (by norm_num)).abs hi
      intro a
      exact (bulkLogPartition_bound n M f v a).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (norm_nonneg a.2)))
    _=_ := by rw [integral_add (integrable_const _) ((bulkMarkNorm_integrable (n+1) M).const_mul _),integral_const_mul]; simp [integral_const_mul]

lemma bulkExpectedLog_parameter_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (bulkExpectedLog n M f) bulkParameterLaw := by
  apply Integrable.of_bound (bulkExpectedLog_parameter_measurable n M f).aestronglyMeasurable
    (M*‖f‖+2*|bulkScale (n+1)| *∫ a : BulkDisorder (n+1) M,‖a.2‖ ∂bulkDisorderLaw (n+1) M)
  filter_upwards [bulkParameterLaw_ae] with v hv
  rw [Real.norm_eq_abs]
  exact bulkExpectedLog_box_bound n M f v (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellSubexp
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma cavityShell_subset_closedBall (k : ℕ) :
    cavityShell (k+1) ⊆ Metric.closedBall 0 (Real.sqrt ((k+1:ℕ)+1)) := by
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (Real.le_sqrt (norm_nonneg z) (by positivity)).mpr hz.2

lemma cavityShell_volume_ne_top (k : ℕ) :
    (volume : Measure (Spin (k+1))) (cavityShell (k+1))≠⊤ :=
  ne_of_lt ((measure_mono (cavityShell_subset_closedBall k)).trans_lt
    (isCompact_closedBall _ _).measure_lt_top)

lemma cavity_sqrt_power_gap (k : ℕ) :
    (Real.sqrt (k+1:ℕ))^(k+1)/(2*((k+1:ℕ)+1)) ≤
      (Real.sqrt ((k+1:ℕ)+1))^(k+1)-(Real.sqrt (k+1:ℕ))^(k+1) := by
  let a:=Real.sqrt (k+1:ℕ)
  let b:=Real.sqrt ((k+1:ℕ)+1)
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0<b := Real.sqrt_pos.mpr (by positivity)
  have hab : a≤b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a^2=(k+1:ℕ) := Real.sq_sqrt (by positivity)
  have hb2 : b^2=((k+1:ℕ)+1) := Real.sq_sqrt (by positivity)
  have hdiff : (b-a)*(b+a)=1 := by nlinarith
  have hlarge : a*(b+a)≤2*b^2 := by nlinarith [sq_nonneg (b-a)]
  have hsmall : a≤2*((k+1:ℕ)+1)*(b-a) := by
    have hh:=mul_le_mul_of_nonneg_right hlarge (sub_nonneg.mpr hab)
    nlinarith
  have hp : a^k≤b^k := pow_le_pow_left₀ ha.le hab k
  have hx : a^k*(b-a)≤b^(k+1)-a^(k+1) := by
    rw [pow_succ,pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hp hb.le]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((k+1:ℕ)+1))).mpr
  calc
    a^(k+1)=a^k*a := pow_succ _ _
    _≤a^k*(2*((k+1:ℕ)+1)*(b-a)) := mul_le_mul_of_nonneg_left hsmall (pow_nonneg ha.le _)
    _=(a^k*(b-a))*(2*((k+1:ℕ)+1)) := by ring
    _≤(b^(k+1)-a^(k+1))*(2*((k+1:ℕ)+1)) := mul_le_mul_of_nonneg_right hx (by positivity)

lemma cavityShell_volume_lower (k : ℕ) :
    (Real.sqrt (k+1:ℕ))^(k+1)/(2*((k+1:ℕ)+1)) *
       (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) ≤
      (volume : Measure (Spin (k+1))).real (cavityShell (k+1)) := by
  let A : Set (Spin (k+1)) := Metric.closedBall 0 (Real.sqrt ((k+1:ℕ)+1))
  let B : Set (Spin (k+1)) := Metric.closedBall 0 (Real.sqrt (k+1:ℕ))
  have hBA : B⊆A := Metric.closedBall_subset_closedBall (Real.sqrt_le_sqrt (by linarith))
  have hs : A\B⊆cavityShell (k+1) := by
    intro z hz
    have ha : ‖z‖≤Real.sqrt ((k+1:ℕ)+1) := by simpa only [A,Metric.mem_closedBall,dist_zero_right] using hz.1
    have hb : Real.sqrt (k+1:ℕ)<‖z‖ := by simpa only [B,Metric.mem_closedBall,dist_zero_right,not_le] using hz.2
    constructor
    · nlinarith [Real.sq_sqrt (show (0:ℝ)≤(k+1:ℕ) by positivity),norm_nonneg z,Real.sqrt_nonneg ((k+1:ℕ):ℝ)]
    · nlinarith [Real.sq_sqrt (show (0:ℝ)≤(k+1:ℕ)+1 by positivity),norm_nonneg z,Real.sqrt_nonneg ((k+1:ℕ)+1)]
  have hvol : (volume : Measure (Spin (k+1))).real (A\B)=
      ((Real.sqrt ((k+1:ℕ)+1))^(k+1)-(Real.sqrt (k+1:ℕ))^(k+1)) *
        (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) := by
    rw [measureReal_sdiff hBA (Metric.isClosed_closedBall.measurableSet) (isCompact_closedBall _ _).measure_ne_top]
    simp only [A,B,Measure.addHaar_real_closedBall' (volume : Measure (Spin (k+1))) 0 (Real.sqrt_nonneg _),finrank_euclideanSpace,Fintype.card_fin]
    ring
  apply (mul_le_mul_of_nonneg_right (cavity_sqrt_power_gap k) measureReal_nonneg).trans
  rw [←hvol]
  exact measureReal_mono hs (cavityShell_volume_ne_top k)

lemma cavityShell_density_lower (k : ℕ) :
    radialNormalizer k * Real.exp (-((k+1:ℕ)+1)/2) *
      (volume : Measure (Spin (k+1))).real (cavityShell (k+1)) ≤ cavityShellMass k := by
  change _≤(stdGaussian (Spin (k+1))).real _
  rw [←canonicalRadialMass_eq_stdGaussian,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) (cavityShell_measurable _)]
  have h := setIntegral_mono_on (integrableOn_const (cavityShell_volume_ne_top k) (C:=radialNormalizer k*Real.exp (-((k+1:ℕ)+1)/2)))
    (canonicalRadialDensity_integrable k (by norm_num : (0:ℝ)<1)).integrableOn (cavityShell_measurable (k+1))
    (fun z hz=>show radialNormalizer k*Real.exp (-((k+1:ℕ)+1)/2) ≤ canonicalRadialDensity k 1 z from by
      unfold canonicalRadialDensity
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (radialNormalizer_pos k).le
      have hh:=hz.2
      change ‖z‖^2≤(k+1:ℕ)+1 at hh
      nlinarith)
  simpa only [integral_const,measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul,mul_comm] using h

lemma cavity_band_density_upper (k : ℕ) {ε : ℝ} (hε : 0≤ε) :
    (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      radialNormalizer k * Real.exp (-((k+1:ℕ)*(1-ε))/2) *
        (Real.sqrt ((k+1:ℕ)*(1+ε)))^(k+1) *
          (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1) := by
  have hs : normSquareBand k ε ⊆ Metric.closedBall (0:Spin (k+1)) (Real.sqrt ((k+1:ℕ)*(1+ε))) := by
    intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      (Real.le_sqrt (norm_nonneg z) (by positivity)).mpr hz.2
  have hf : (volume : Measure (Spin (k+1))) (normSquareBand k ε)≠⊤ :=
    ne_of_lt ((measure_mono hs).trans_lt (isCompact_closedBall _ _).measure_lt_top)
  rw [canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) (normSquareBand_measurable _ _)]
  have hi := setIntegral_mono_on (canonicalRadialDensity_integrable k (by norm_num : (0:ℝ)<1)).integrableOn
    (integrableOn_const hf (C:=radialNormalizer k * Real.exp (-((k+1:ℕ)*(1-ε))/2))) (normSquareBand_measurable k ε)
    (fun z hz=>show canonicalRadialDensity k 1 z ≤ radialNormalizer k*Real.exp (-((k+1:ℕ)*(1-ε))/2) from by
      unfold canonicalRadialDensity
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (radialNormalizer_pos k).le
      have hh:=hz.1
      change (k+1:ℕ)*(1-ε)≤‖z‖^2 at hh
      nlinarith)
  simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul] at hi
  apply hi.trans
  have hm := measureReal_mono (μ:=(volume : Measure (Spin (k+1)))) hs (isCompact_closedBall _ _).measure_ne_top
  rw [Measure.addHaar_real_closedBall' (volume : Measure (Spin (k+1))) 0 (Real.sqrt_nonneg _),finrank_euclideanSpace,Fintype.card_fin] at hm
  convert mul_le_mul_of_nonneg_left hm (mul_pos (radialNormalizer_pos k) (Real.exp_pos (-((k+1:ℕ)*(1-ε))/2))).le using 1 <;> ring

lemma cavity_sqrt_pow_exp (k : ℕ) {ε : ℝ} (_hε : 0≤ε) :
    (Real.sqrt (1+ε))^(k+1)≤Real.exp (ε*(k+1:ℕ)/2) := by
  have hh : Real.sqrt (1+ε)≤Real.exp (ε/2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le,?_⟩
    rw [←Real.exp_nat_mul]
    convert Real.add_one_le_exp ε using 1 <;> ring_nf
  have hp:=pow_le_pow_left₀ (Real.sqrt_nonneg _) hh (k+1)
  rw [←Real.exp_nat_mul] at hp
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma cavityShell_band_comparison (k : ℕ) {ε : ℝ} (hε : 0≤ε) :
    (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      cavityShellMass k * (2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2) := by
  let D:=radialNormalizer k * (Real.sqrt (k+1:ℕ))^(k+1) *
    (volume : Measure (Spin (k+1))).real (Metric.closedBall 0 1)
  have hD : 0≤D := by
    exact mul_nonneg (mul_nonneg (radialNormalizer_pos k).le
      (pow_nonneg (Real.sqrt_nonneg _) _)) measureReal_nonneg
  have hl : D*Real.exp (-((k+1:ℕ)+1)/2)/(2*((k+1:ℕ)+1)) ≤ cavityShellMass k := by
    have hv:=mul_le_mul_of_nonneg_left (cavityShell_volume_lower k)
      (mul_pos (radialNormalizer_pos k) (Real.exp_pos (-((k+1:ℕ)+1)/2))).le
    apply le_trans _ (cavityShell_density_lower k)
    convert hv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [D]
    ring
  have hb : (canonicalRadialMass k 1).real (normSquareBand k ε)≤
      D*Real.exp (-((k+1:ℕ)*(1-ε))/2)*Real.exp (ε*(k+1:ℕ)/2) := by
    apply (cavity_band_density_upper k hε).trans
    rw [Real.sqrt_mul (by positivity),mul_pow]
    have hh := mul_le_mul_of_nonneg_left (cavity_sqrt_pow_exp k hε)
      (show 0≤D*Real.exp (-((k+1:ℕ)*(1-ε))/2) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [D]
    ring
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right hl
    (show 0≤(2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2) by positivity)
  convert hh using 1
  · rw [mul_assoc D,←Real.exp_add]
    rw [div_mul_eq_mul_div,eq_div_iff (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0)]
    rw [show D*Real.exp (-((k+1:ℕ)+1)/2)*((2*((k+1:ℕ)+1))*Real.exp (ε*(k+1:ℕ)+1/2))=
        D*(Real.exp (-((k+1:ℕ)+1)/2)*Real.exp (ε*(k+1:ℕ)+1/2))*(2*((k+1:ℕ)+1)) by ring,←Real.exp_add]
    congr 2
    ring_nf
  · ring

lemma cavityShell_log_lower (k : ℕ) {ε : ℝ} (hε : 0≤ε)
    (hb : (1/2:ℝ)≤(canonicalRadialMass k 1).real (normSquareBand k ε)) :
    -ε*(k+1:ℕ)-1/2-Real.log (4*((k+1:ℕ)+1))≤Real.log (cavityShellMass k) := by
  have h := Real.log_le_log (by norm_num : (0:ℝ)<1/2) (hb.trans (cavityShell_band_comparison k hε))
  rw [Real.log_mul (mul_pos (cavityShellMass_pos k) (by positivity)).ne' (Real.exp_pos _).ne',
    Real.log_mul (cavityShellMass_pos k).ne' (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0),Real.log_exp,
    Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one] at h
  have he : Real.log (4*((k+1:ℕ)+1))=Real.log 2+Real.log (2*((k+1:ℕ)+1)) := by
    rw [←Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity : (2*((k+1:ℕ)+1):ℝ)≠0)]
    congr 1
    ring
  rw [he]
  linarith

lemma cavityShell_log_error_tendsto :
    Tendsto (fun k : ℕ=>(1/2+Real.log (4*((k+1:ℕ)+1)))/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
  have hN : Tendsto (fun k : ℕ=>((k+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop (1/4) (-1) 1 (by norm_num)).comp
    ((tendsto_atTop_add_const_right _ 1 hN).const_mul_atTop (by norm_num : (0:ℝ)<4))
  have ht' : Tendsto (fun k : ℕ=>Real.log (4*((k+1:ℕ)+1))/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    dsimp only [Function.comp_def]
    rw [pow_one]
    congr 1
    ring
  have hi := (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1/2:ℝ)) atTop (𝓝 (1/2))).mul
    (tendsto_inv_atTop_zero.comp hN)
  convert hi.add ht' using 1 <;> simp only [mul_zero,zero_add,div_eq_mul_inv,add_mul,Function.comp_def]

theorem cavityShell_log_sublinear :
    Tendsto (fun k : ℕ=>Real.log (cavityShellMass k)/(k+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε : ℝ:=min (-a/2) (1/2)
    have he : 0<ε := lt_min (by linarith) (by norm_num)
    have he1 : ε<1 := (min_le_right _ _).trans_lt (by norm_num)
    have hae : a < -ε := by
      have hh : ε≤-a/2 := min_le_left _ _
      dsimp only [ε] at hh ⊢
      linarith
    have ht : Tendsto (fun k : ℕ=>-ε-(1/2+Real.log (4*((k+1:ℕ)+1)))/(k+1:ℕ)) atTop (𝓝 (-ε)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub cavityShell_log_error_tendsto
    filter_upwards [ht.eventually (lt_mem_nhds hae),canonicalRadial_band_eventually_half he he1] with k hk hb
    apply hk.trans_le
    have hh:=div_le_div_of_nonneg_right (cavityShell_log_lower k he.le hb)
      (by positivity : (0:ℝ)≤(k+1:ℕ))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  · intro b hb
    filter_upwards [] with k
    have hh := Real.log_nonpos (cavityShellMass_pos k).le (cavityShellMass_le_one k)
    exact (div_nonpos_of_nonpos_of_nonneg hh (by positivity)).trans_lt hb

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Field
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedPatternLog_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) :
    (1/(n+1:ℕ))*normalizedPatternLog n (patternCount α (n+1)) (β • φ) g=
      pressure α β φ (n+1) g := by
  unfold pressure sphereLaw
  rw [integral_map (by fun_prop) (by
    apply Continuous.aestronglyMeasurable
    unfold hamiltonian patternField
    fun_prop)]
  simp_rw [← normalizedPatternEnergy_source α β φ n g]
  unfold normalizedPatternLog
  ring

lemma normalizedPatternLog_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) :
    Measurable (normalizedPatternLog n M f) := by
  have hm := (Real.continuous_exp.comp (normalizedPatternEnergy_continuous (n+1) M f)).measurable
  exact Real.measurable_log.comp hm.stronglyMeasurable.integral_prod_right'.measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTelescoping
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma block_increment_linear_lower (F : ℕ→ℝ) {L : ℕ} (hL : 0<L) {q : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop,q≤F (n+L)-F n) :
    ∃ C : ℝ,∀ n : ℕ,(n:ℝ)*(q/L)-C≤F n := by
  obtain ⟨N,hN⟩:=eventually_atTop.1 hq
  have hb : BddAbove (Set.range (fun i : Fin (N+L)=>(i.val:ℝ)*(q/L)-F i.val)) :=
    (Set.finite_range _).bddAbove
  obtain ⟨C,hC⟩:=hb
  refine ⟨C,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<N+L
    · have hh:=hC (Set.mem_range_self (⟨n,hn⟩ : Fin (N+L)))
      dsimp at hh
      linarith
    · have hm : N≤n-L:=by omega
      have hml : n-L<n:=by omega
      have he : n-L+L=n:=by omega
      have hi:=ih (n-L) hml
      have ha:=hN (n-L) hm
      rw [he] at ha
      have hc : ((n-L:ℕ):ℝ)+(L:ℝ)=(n:ℝ) := by exact_mod_cast he
      have hlr : (L:ℝ)≠0 := by positivity
      have hr : (L:ℝ)*(q/L)=q := mul_div_cancel₀ q hlr
      have hr' : (n:ℝ)*(q/L)=((n-L:ℕ):ℝ)*(q/L)+q := by rw [←hc,add_mul,hr]
      rw [hr']
      linarith

lemma block_increment_asymptotic_lower (F : ℕ→ℝ) {L : ℕ} (hL : 0<L) {q : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop,q≤F (n+L)-F n) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,q/L-δ≤F n/(n+1:ℕ) := by
  obtain ⟨C,hC⟩:=block_increment_linear_lower F hL hq
  have ht : Tendsto (fun n : ℕ=>(C+q/L)/(n+1:ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (C+q/L)
  filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with n hn
  have hp : (0:ℝ)<(n+1:ℕ) := by positivity
  apply (le_div_iff₀ hp).mpr
  have he : (C+q/L)<δ*(n+1:ℕ) := (div_lt_iff₀ hp).mp hn
  have hh:=hC n
  push_cast at *
  nlinarith

lemma cavity_averaged_log_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤
      cavityAveragedLog α g.f n/(n+1:ℕ) := by
  obtain ⟨G⟩:=exists_cavityGoodParameters hα.le g.f
  let V:=(terminalVariational P α g.f).toReal
  let C:=α*‖g.dilationMark h1‖/2+‖g.f‖+1
  have ht : Tendsto (fun k : ℕ=>Real.log (cavityShellMass k)/(k+1:ℕ)-C/(k+1:ℕ)) atTop (𝓝 0) := by
    have hc : Tendsto (fun k : ℕ=>C/(k+1:ℕ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul C
    simpa only [sub_zero] using cavityShell_log_sublinear.sub hc
  obtain ⟨k,hk,hc⟩:=((cavity_averaged_increment_good P hB hα g h1 h2 h3 G
    (show 0<ε/3 by positivity)).and
    (ht.eventually (Ioi_mem_nhds (show -ε/3<0 by linarith)))).exists
  have hi:=hk 1 (by norm_num)
  let q:=Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
    (k+1:ℕ)*(V-ε/3)-‖g.f‖-1
  have hq : q/(k+1:ℕ)>V-2*ε/3 := by
    have hp : (0:ℝ)<(k+1:ℕ):=by positivity
    have he : q/(k+1:ℕ)=V-ε/3+
        (Real.log (cavityShellMass k)/(k+1:ℕ)-C/(k+1:ℕ)) := by
      dsimp [q,C]
      field_simp
      ring
    rw [he]
    linarith
  filter_upwards [block_increment_asymptotic_lower (cavityAveragedLog α g.f)
    (Nat.succ_pos k) (q:=q) hi (show 0<ε/3 by positivity)] with n hn
  change V-ε≤_
  linarith


lemma normalizedPatternLog_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (normalizedPatternLog n M f) (finitePatternRowsLaw (n+1) M) := by
  apply Integrable.of_bound (normalizedPatternLog_measurable n M f).aestronglyMeasurable (M*‖f‖)
  filter_upwards [] with a
  rw [Real.norm_eq_abs]
  simpa only [normalizedPatternLog,tiltPartition,one_mul,Function.comp_apply,id_eq] using
    tilt_log_partition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (by positivity : 0≤M*‖f‖) (normalizedPatternEnergy_bound _ _ _ a)

lemma bulkExpectedLog_unperturbed_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    |bulkExpectedLog n M f v-∫ a,normalizedPatternLog n M f a ∂finitePatternRowsLaw (n+1) M|≤
      Real.pi*bulkFeatureBound (n+1) v^2 := by
  have hj:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1) M)
    (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f) (bulkFeature (n+1) v)
    (normalizedPatternEnergy_continuous (n+1) M f).measurable
    (bulkFeature_continuous (n+1) v).measurable
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
    (normalizedPatternEnergy_bound _ _ _)
    (fun x=>(bulkFeature_norm _ _ _).le)
  have hp (a : Fin M→Fin (n+1)→ℝ) :
      |(∫ z,Real.log (tiltPartition (unitSphereLaw (n+1))
        (fun x=>normalizedPatternEnergy (n+1) M f a x+inner ℝ (bulkFeature (n+1) v x) z) 1)
        ∂stdGaussian (BulkMark (n+1)))-normalizedPatternLog n M f a|≤
      Real.pi*bulkFeatureBound (n+1) v^2 := by
    have h:=independentGaussian_covariance_comparison (unitSphereLaw (n+1))
      (V:=fun _=>(0:BulkMark (n+1)))
      ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
      measurable_const (bulkFeature_continuous (n+1) v).measurable
      (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
      (normalizedPatternEnergy_bound _ _ _ a)
      (fun _=>by simp) (fun x=>(bulkFeature_norm _ _ _).le)
      (sq_nonneg (bulkFeatureBound (n+1) v)) (fun x y=>by
        simp only [inner_zero_left,sub_zero]
        simpa only [bulkFeature_norm,pow_two] using abs_real_inner_le_norm (bulkFeature (n+1) v x) (bulkFeature (n+1) v y))
    simpa only [inner_zero_left,add_zero,integral_const,probReal_univ,one_smul,
      tiltPartition,one_mul,normalizedPatternLog,Function.comp_apply,id_eq] using h
  have hJ : Integrable (fun a : Fin M→Fin (n+1)→ℝ=>∫ z,Real.log
      (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a z) 1)
      ∂stdGaussian (BulkMark (n+1))) (finitePatternRowsLaw (n+1) M) := hj.integral_prod_left
  rw [bulkExpectedLog_nested,←integral_sub hJ (normalizedPatternLog_integrable n M f)]
  apply (abs_integral_le_integral_abs).trans
  calc
    (∫ a,|((∫ z,Real.log (tiltPartition (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a z) 1) ∂stdGaussian (BulkMark (n+1)))-
      normalizedPatternLog n M f a)| ∂finitePatternRowsLaw (n+1) M)≤
      ∫ _ : Fin M→Fin (n+1)→ℝ,Real.pi*bulkFeatureBound (n+1) v^2 ∂finitePatternRowsLaw (n+1) M :=
      integral_mono (hj.integral_prod_left.sub (normalizedPatternLog_integrable n M f)).abs (integrable_const _) hp
    _=_ := by simp

lemma cavityAveragedLog_unperturbed_bound {α : ℝ} (_hα : 0≤α) (f : ℝ→ᵇℝ) (n : ℕ) :
    |cavityAveragedLog α f n/(n+1:ℕ)-expectedPressure α 1 f (n+1)|≤
      4*Real.pi*bulkScale (n+1)^2/(n+1:ℕ) := by
  let A:=∫ a,normalizedPatternLog n (patternCount α (n+1)) f a ∂finitePatternRowsLaw (n+1) (patternCount α (n+1))
  have he : expectedPressure α 1 f (n+1)=A/(n+1:ℕ) := by
    unfold expectedPressure
    simp_rw [←normalizedPatternLog_source α 1 f n,one_smul]
    rw [integral_const_mul]
    change (1/(n+1:ℕ))*A=A/(n+1:ℕ)
    ring
  have hv : ∀ᵐ v ∂bulkParameterLaw,|bulkExpectedLog n (patternCount α (n+1)) f v-A|≤
      4*Real.pi*bulkScale (n+1)^2 := by
    filter_upwards [bulkParameterLaw_ae] with v hv
    have hb:=bulkFeatureBound_sq_le (n+1) v (by norm_num : (0:ℝ)≤2)
      (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)
    have hi:=bulkExpectedLog_unperturbed_bound n (patternCount α (n+1)) f v
    change |bulkExpectedLog n (patternCount α (n+1)) f v-A|≤_ at hi
    nlinarith [Real.pi_pos]
  have ha : |cavityAveragedLog α f n-A|≤4*Real.pi*bulkScale (n+1)^2 := by
    have hi:=(bulkExpectedLog_parameter_integrable n (patternCount α (n+1)) f).sub (integrable_const A)
    have hh:=integral_mono_ae hi.abs (integrable_const (4*Real.pi*bulkScale (n+1)^2)) hv
    have hh':=abs_integral_le_integral_abs (f:=fun v=>bulkExpectedLog n (patternCount α (n+1)) f v-A) (μ:=bulkParameterLaw)
    simp only [integral_sub (bulkExpectedLog_parameter_integrable _ _ f) (integrable_const A),
      integral_const,probReal_univ,one_smul] at hh hh'
    exact hh'.trans hh
  rw [he,←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(n+1:ℕ))]
  exact div_le_div_of_nonneg_right ha (by positivity)

lemma bulkScale_per_coordinate_tendsto :
    Tendsto (fun n : ℕ=>4*Real.pi*bulkScale (n+1)^2/(n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have he (n : ℕ) : bulkScale (n+1)^2/(n+1:ℕ)=((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [bulkScale_sq_eq_rpow]
    have hs:=Real.rpow_sub (by positivity : (0:ℝ)<(n+1:ℕ)) ((3:ℝ)/4) 1
    norm_num at hs
    simpa only [Nat.cast_add,Nat.cast_one,neg_div] using hs.symm
  convert ht.const_mul (4*Real.pi) using 1
  · funext n
    rw [mul_div_assoc,he]
    simp only [Function.comp_apply,neg_div]
  · simp
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma expectedPressure_lower_smooth_oai (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤expectedPressure α 1 g.f (n+1) := by
  filter_upwards [cavity_averaged_log_lower P hB hα g h1 h2 h3 (show 0<ε/2 by positivity),
    bulkScale_per_coordinate_tendsto.eventually (Iio_mem_nhds (show 0<ε/2 by positivity))] with n hn he
  have hb:=cavityAveragedLog_unperturbed_bound hα.le g.f n
  linarith [(abs_le.mp hb).2]

end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth_oai := @OAI.SphericalPerceptronFreeEnergy.expectedPressure_lower_smooth_oai
