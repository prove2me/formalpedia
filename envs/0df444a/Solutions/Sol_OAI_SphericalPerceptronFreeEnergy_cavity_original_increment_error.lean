-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:21:45.818643+00:00
-- url     : https://prove2.me/submissions/65828205-a7c5-4924-90a9-2c947c65047d

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_proxy_expected_lower

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
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

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PiMarkLaw
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

lemma gaussian_square_memLp_two (r : ℝ≥0) : MemLp (fun y : ℝ => y^2) 2 (gaussianReal 0 r) := by
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    apply (ENNReal.holderTriple_coe_iff (p := 4) (q := 4) (r := 2) (by norm_num)).mpr
    norm_num [NNReal.holderTriple_iff]
  have h4 : MemLp (fun y : ℝ => y) (4 : ℝ≥0∞) (gaussianReal 0 r) := memLp_id_gaussianReal 4
  have hm : MemLp (fun y : ℝ => y*y) 2 (gaussianReal 0 r) :=
    h4.mul h4
  simpa [pow_two] using hm

lemma gaussian_square_mean (r : ℝ≥0) : (∫ y, y^2 ∂gaussianReal 0 r) = r := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := r)
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 r))] at he
  simpa only [integral_id_gaussianReal,sub_zero] using he

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

lemma bulkFeature_inner (N : ℕ) (v : ℕ → ℝ) (x y : NormalizedSpin N) :
    inner ℝ (bulkFeature N v x) (bulkFeature N v y) =
      bulkScale N ^ 2 * bulkCovariance N v (spinOverlap x y) := by
  rw [bulkFeature, enrichedFeature_inner]
  simp only [zero_pow two_ne_zero, zero_mul, zero_add, bulkCovariance, Finset.mul_sum,
    bulkAmplitude, bulkDegree]
  apply Finset.sum_congr rfl
  intro i _
  ring

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_AmbientBulkFeature
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators ContDiff
namespace SphericalPerceptronFreeEnergy

lemma ambientTensorFeature_contDiff (N p : ℕ) : ContDiff ℝ ∞ (ambientTensorFeature N p) := by
  apply (PiLp.contDiff_toLp).comp
  apply contDiff_pi.mpr
  intro i
  exact contDiff_prod (fun j _ => (EuclideanSpace.proj (i j) : Spin N →L[ℝ] ℝ).contDiff)

lemma ambientBulkFeature_eq (N : ℕ) (v : ℕ→ℝ) (x : NormalizedSpin N) :
    ambientBulkFeature N v x.val=bulkFeature N v x := by
  ext i
  cases i <;> simp [ambientBulkFeature,bulkFeature,enrichedFeature,ambientTensorFeature,spinTensorFeature]

lemma ambientBulkFeature_contDiff (N : ℕ) (v : ℕ→ℝ) : ContDiff ℝ ∞ (ambientBulkFeature N v) := by
  apply (PiLp.contDiff_toLp).comp
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiff_const
  | inr i => exact contDiff_const.mul ((EuclideanSpace.proj i.2).contDiff.comp (ambientTensorFeature_contDiff _ _))

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkTangentError
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkCovarianceDerivative_bound (N : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovarianceDerivative N v r|≤C^2*bulkScale N^2 := by
  have hb (j : Fin N) : bulkAmplitude N v j^2*(j.val+1)≤C^2*bulkScale N^2*(1/2:ℝ)^(j.val+1) := by
    let w : ℝ := (1/2:ℝ)^(j.val+1)
    have hw : 0≤w := by dsimp [w]; positivity
    have hwp : w*(j.val+1)≤1 := by
      have hk : (j.val+1:ℝ)≤(2:ℝ)^(j.val+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=j.val+1)).le
      dsimp [w]
      rw [div_pow,one_pow,one_div_mul_eq_div]
      exact (div_le_one (by positivity)).mpr (by simpa only [Nat.cast_add,Nat.cast_one] using hk)
    have hv2 : v (j.val+1)^2≤C^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hv j.val) 2
    unfold bulkAmplitude
    rw [perturbationWeight_eq]
    change (bulkScale N*w*v (j.val+1))^2*(j.val+1)≤C^2*bulkScale N^2*w
    calc
      _ = bulkScale N^2*w^2*(j.val+1)*v (j.val+1)^2 := by ring
      _ ≤ bulkScale N^2*w^2*(j.val+1)*C^2 := mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = C^2*bulkScale N^2*w*(w*(j.val+1)) := by ring
      _ ≤ C^2*bulkScale N^2*w*1 := mul_le_mul_of_nonneg_left hwp (by positivity)
      _ = _ := mul_one _
  unfold bulkCovarianceDerivative
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin N, C^2*bulkScale N^2*(1/2:ℝ)^(j.val+1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul,abs_sq,abs_of_nonneg (by positivity : (0:ℝ)≤j.val+1),abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg r) hr) (by positivity)).trans (by simpa only [mul_one] using hb j)
    _ = C^2*bulkScale N^2*(∑ j : Fin N, (1/2:ℝ)^(j.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*bulkScale N^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N)
      (mul_nonneg (pow_nonneg hC 2) (sq_nonneg _))
    _ = _ := mul_one _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianPolar
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma normalizedGaussian_smul (n : ℕ) (r : Ioi (0:ℝ))
    (u : Metric.sphere (0:Spin (n+1)) 1) :
    ‖r.val • u.val‖⁻¹ • (r.val • u.val)=u.val := by
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one,smul_smul,
    inv_mul_cancel₀ (ne_of_gt r.prop),one_smul]

lemma normalizedGaussian_polar_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => (‖x‖,‖x‖⁻¹ • x))=
      ((gaussianRadiusLaw n).map Subtype.val).prod
        ((unitSphereLaw (n+1)).map Subtype.val) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop)]
  rw [stdGaussian_polar_lintegral n (fun x => F (‖x‖,‖x‖⁻¹ • x)) (by fun_prop),
    lintegral_prod _ hF.aemeasurable]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro r
  rw [lintegral_map (f:=fun y : Spin (n+1) => F (r.val,y)) (by fun_prop) measurable_subtype_coe]
  apply lintegral_congr
  intro u
  rw [normalizedGaussian_smul]
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBlock
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma gaussianBlockSplit_measurable (N L : ℕ) : Measurable (gaussianBlockSplit N L) := by
  unfold gaussianBlockSplit
  fun_prop

lemma gaussianBlockSplit_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockSplit N L) (stdGaussian (Spin (N+L)))
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L))) := by
  have hp := (measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1) finSumFinEquiv.symm)
  have hN : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hL : MeasurePreserving (WithLp.toLp 2 : (Fin L→ℝ)→Spin L)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin L)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianBlockSplit_measurable N L,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (gaussianBlockSplit_measurable N L)
    (PiLp.continuous_toLp 2 _).measurable]
  convert ((hN.prod hL).comp hp).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  apply Prod.ext <;> ext i <;>
    simp [gaussianBlockSplit,MeasurableEquiv.piCongrLeft,MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft,Equiv.piCongrLeft',eq_rec_constant]

lemma stdGaussian_direction_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1)).map Subtype.val := by
  have : IsProbabilityMeasure ((gaussianRadiusLaw n).map Subtype.val) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := congrArg (fun μ : Measure (ℝ×Spin (n+1)) => μ.map Prod.snd) (normalizedGaussian_polar_law n)
  rwa [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod,measure_univ,one_smul] at h

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityDisintegration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

lemma stdGaussian_radial_preserving (n : ℕ) :
    MeasurePreserving (fun p : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 => p.1.val •p.2.val)
      ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))) (stdGaussian (Spin (n+1))) := by
  refine ⟨by fun_prop,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),lintegral_prod _ (by fun_prop)]
  exact (stdGaussian_polar_lintegral n F hF).symm

lemma cavityBlockNormalize_measurable (N L : ℕ) : Measurable (cavityBlockNormalize N L) := by
  unfold cavityBlockNormalize
  fun_prop

lemma gaussianBlockSplit_normalize (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockSplit N L (‖x‖⁻¹ •x)=cavityBlockNormalize N L (gaussianBlockSplit N L x) := by
  unfold cavityBlockNormalize
  rw [←gaussianBlockSplit_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  apply Prod.ext <;> ext i <;> rfl

lemma sphereBlock_gaussian_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      ((stdGaussian (Spin (n+1))).prod (stdGaussian (Spin L))).map (cavityBlockNormalize (n+1) L) := by
  have hd : (stdGaussian (Spin (n+1+L))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1+L)).map Subtype.val := by
    have he : n+1+L=(n+L)+1 := by omega
    rw [he]
    exact stdGaussian_direction_law (n+L)
  have h := congrArg (fun μ : Measure (Spin (n+1+L)) => μ.map (gaussianBlockSplit (n+1) L)) hd
  rw [Measure.map_map (gaussianBlockSplit_measurable _ _) (by fun_prop),
    Measure.map_map (gaussianBlockSplit_measurable _ _) measurable_subtype_coe] at h
  simp only [Function.comp_def] at h
  rw [←h,←(gaussianBlockSplit_preserving (n+1) L).map_eq,
    Measure.map_map (cavityBlockNormalize_measurable _ _) (gaussianBlockSplit_measurable _ _)]
  congr 1
  funext x
  exact gaussianBlockSplit_normalize (n+1) L x

lemma cavityRadialBlock_eq (n L : ℕ) (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityBlockNormalize (n+1) L (p.1.1.val •p.1.2.val,p.2) := by
  have hn : ‖p.1.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.1.2.prop
  simp only [cavityRadialBlock,cavityBlockNormalize,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show (0:ℝ)<p.1.1.val from p.1.1.prop),hn,mul_one,smul_smul]

theorem sphereBlock_radial_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L))).map
        (cavityRadialBlock n L) := by
  rw [sphereBlock_gaussian_law]
  have hp := (stdGaussian_radial_preserving n).prod (MeasurePreserving.id (stdGaussian (Spin L)))
  rw [←hp.map_eq,Measure.map_map (cavityBlockNormalize_measurable _ _) hp.measurable]
  congr 1
  funext p
  exact (cavityRadialBlock_eq n L p).symm

lemma countableGaussian_eval_preserving (i : ℕ) :
    MeasurePreserving (fun g : ℕ→ℝ=>g i) countableGaussianLaw (gaussianReal 0 1) :=
  ⟨measurable_pi_apply i,Measure.infinitePi_map_eval _ i⟩

lemma countableGaussian_square_strongLaw :
    ∀ᵐ g ∂countableGaussianLaw,
      Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(g i)^2)/(n:ℝ)) atTop (𝓝 1) := by
  have hi (i : ℕ) : IdentDistrib (fun g : ℕ→ℝ=>g i) (fun x : ℝ=>x)
      countableGaussianLaw (gaussianReal 0 1) :=
    ⟨(measurable_pi_apply i).aemeasurable,measurable_id.aemeasurable,by
      change Measure.map _ _ = Measure.map id _
      rw [Measure.map_id]; exact (countableGaussian_eval_preserving i).map_eq⟩
  have hint : Integrable (fun g : ℕ→ℝ=>(g 0)^2) countableGaussianLaw :=
    ((gaussian_square_memLp_two 1).comp_measurePreserving
      (countableGaussian_eval_preserving 0)).integrable (by norm_num)
  have hind := iIndepFun_infinitePi (P:=fun _ : ℕ=>gaussianReal 0 1)
    (X:=fun _ : ℕ=>fun x : ℝ=>x^2) (fun _=>by fun_prop)
  have h := strong_law_ae_real (fun i (g : ℕ→ℝ)=>(g i)^2) hint
    (fun i j hij=>hind.indepFun hij) (fun i=>(hi i).sq.trans (hi 0).sq.symm)
  have hm : (∫ g,(g 0)^2 ∂countableGaussianLaw)=1 := by
    rw [(hi 0).sq.integral_eq,gaussian_square_mean]; rfl
  rwa [hm] at h

lemma cavityCoupledScale_measurable (n L : ℕ) :
    Measurable (Function.uncurry (cavityCoupledScale n L)) := by
  unfold cavityCoupledScale Function.uncurry
  fun_prop

lemma cavityCoupledScale_tendsto (L : ℕ) (g : ℕ→ℝ) (z : Spin L)
    (hg : Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(g i)^2)/(n:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n=>cavityCoupledScale n L g z) atTop (𝓝 1) := by
  have hs := hg.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=> (n+1:ℕ)⁻¹ : ℕ→ℝ) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hnum : Tendsto (fun n : ℕ=> ((n+1+L:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x:=(1:ℝ))).add (hi.const_mul (L:ℝ))
    convert ht using 1
    · funext n
      push_cast
      field_simp
    · simp
  have hden : Tendsto (fun n : ℕ=> ((∑ i∈Finset.range (n+1),(g i)^2)+‖z‖^2)/(n+1:ℕ)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,add_mul,mul_zero,add_zero] using hs.add (hi.const_mul (‖z‖^2))
  have ht := hnum.sqrt.div hden.sqrt (by norm_num : Real.sqrt (1:ℝ)≠0)
  simp only [Real.sqrt_one,div_one] at ht
  apply ht.congr'
  filter_upwards [] with n
  change Real.sqrt (_/_)/Real.sqrt (_/_) = _
  unfold cavityCoupledScale
  rw [Real.sqrt_div (by positivity),Real.sqrt_div (by positivity)]
  have hn : Real.sqrt ((n+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

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

lemma countableGaussian_prefix_preserving (n : ℕ) :
    MeasurePreserving (fun g=>WithLp.toLp 2 (gaussianCoordinatePrefix n g))
      countableGaussianLaw (stdGaussian (Spin n)) :=
  (show MeasurePreserving (WithLp.toLp 2 : (Fin n→ℝ)→Spin n)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin n)) from
        ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩).comp
    (gaussianCoordinatePrefix_measurePreserving n)

lemma countableGaussian_prefix_norm (n : ℕ) (g : ℕ→ℝ) :
    ‖WithLp.toLp 2 (gaussianCoordinatePrefix n g)‖^2=∑ i∈Finset.range n,(g i)^2 := by
  simp only [EuclideanSpace.norm_sq_eq,gaussianCoordinatePrefix,Real.norm_eq_abs,sq_abs]
  exact Fin.sum_univ_eq_sum_range (fun i=>(g i)^2) n

lemma cavityCoupledBlock_measurable (n L : ℕ) : Measurable (cavityCoupledBlock n L) :=
  (cavityCoupledScale_measurable n L).smul measurable_snd

lemma cavitySphereLaw_coupled (n L : ℕ) :
    (cavitySphereLaw n L : Measure (Spin L))=
      (countableGaussianLaw.prod (stdGaussian (Spin L))).map (cavityCoupledBlock n L) := by
  have hp := (countableGaussian_prefix_preserving (n+1)).prod
    (MeasurePreserving.id (stdGaussian (Spin L)))
  have h := congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>
    μ.map (fun p=>Real.sqrt (n+1+L:ℕ) •p.2)) (sphereBlock_gaussian_law n L)
  rw [Measure.map_map (by fun_prop) (show Measurable (fun u : Metric.sphere (0 : Spin (n+1+L)) 1 => gaussianBlockSplit (n+1) L u.val) from (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe),
    Measure.map_map (by fun_prop) (cavityBlockNormalize_measurable _ _)] at h
  simp only [Function.comp_def] at h
  change (unitSphereLaw (n+1+L)).map _ = _
  rw [h,←hp.map_eq,Measure.map_map (by unfold cavityBlockNormalize; fun_prop) hp.measurable]
  congr 1
  funext p
  simp only [Function.comp_def,cavityBlockNormalize,cavityCoupledBlock,cavityCoupledScale,
    smul_smul,div_eq_mul_inv,Prod.map_fst,Prod.map_snd,id_eq]
  rw [countableGaussian_prefix_norm]

lemma cavityCoupledBlock_tendsto_ae (L : ℕ) :
    ∀ᵐ p ∂countableGaussianLaw.prod (stdGaussian (Spin L)),
      Tendsto (fun n=>cavityCoupledBlock n L p) atTop (𝓝 p.2) := by
  have hf : ∀ᵐ p ∂countableGaussianLaw.prod (stdGaussian (Spin L)),
      Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(p.1 i)^2)/(n:ℝ)) atTop (𝓝 1) :=
    (measurePreserving_fst (μ:=countableGaussianLaw) (ν:=stdGaussian (Spin L))).quasiMeasurePreserving.ae
      countableGaussian_square_strongLaw
  filter_upwards [hf] with p hp
  simpa only [one_smul,cavityCoupledBlock] using (cavityCoupledScale_tendsto L p.1 p.2 hp).smul
    (tendsto_const_nhds (x:=p.2))

theorem cavitySphereLaw_tendsto (L : ℕ) :
    Tendsto (fun n=>cavitySphereLaw n L) atTop (𝓝 (cavityGaussianLaw L)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have he n : (∫ z,F z ∂(cavitySphereLaw n L : Measure (Spin L)))=
      ∫ p,F (cavityCoupledBlock n L p) ∂countableGaussianLaw.prod (stdGaussian (Spin L)) := by
    rw [cavitySphereLaw_coupled,integral_map (cavityCoupledBlock_measurable n L).aemeasurable F.continuous.aestronglyMeasurable]
  have he0 : (∫ z,F z ∂(cavityGaussianLaw L : Measure (Spin L)))=
      ∫ p : (ℕ→ℝ)×Spin L,F p.2 ∂countableGaussianLaw.prod (stdGaussian (Spin L)) := by
    symm
    rw [←integral_map measurable_snd.aemeasurable F.continuous.aestronglyMeasurable,
      Measure.map_snd_prod,measure_univ,one_smul]
    rfl
  simp_rw [he,he0]
  apply tendsto_integral_of_dominated_convergence (fun _=>‖F‖)
    (fun n=>(F.measurable.comp (cavityCoupledBlock_measurable n L)).aestronglyMeasurable)
    (integrable_const ‖F‖)
  · intro n
    exact ae_of_all _ fun p=>F.norm_coe_le_norm _
  · filter_upwards [cavityCoupledBlock_tendsto_ae L] with p hp
    exact F.continuous.continuousAt.tendsto.comp hp

lemma cavityShell_measurable (L : ℕ) : MeasurableSet (cavityShell L) := by
  exact (isClosed_Icc.preimage (show Continuous (fun z : Spin L=>‖z‖^2) from continuous_norm.pow 2)).measurableSet

lemma stdGaussian_sphere_null (k : ℕ) (r : ℝ) :
    stdGaussian (Spin (k+1)) (Metric.sphere 0 r)=0 := by
  rw [←canonicalRadialMass_eq_stdGaussian]
  exact withDensity_absolutelyContinuous _ _ (Measure.addHaar_sphere volume 0 r)

lemma cavityShell_frontier_null (k : ℕ) :
    stdGaussian (Spin (k+1)) (frontier (cavityShell (k+1)))=0 := by
  have hs : frontier (cavityShell (k+1)) ⊆
      Metric.sphere 0 (Real.sqrt (k+1:ℕ)) ∪ Metric.sphere 0 (Real.sqrt ((k+1:ℕ)+1)) := by
    intro z hz
    have h := (continuous_norm.pow 2).frontier_preimage_subset (Icc ((k+1:ℕ):ℝ) ((k+1:ℕ)+1)) hz
    rw [frontier_Icc (by linarith)] at h
    simp only [mem_preimage,mem_insert_iff,mem_singleton_iff,Pi.pow_apply] at h
    rcases h with h|h
    · left
      simp only [Metric.mem_sphere,dist_zero_right,←h,Real.sqrt_sq (norm_nonneg z)]
    · right
      simp only [Metric.mem_sphere,dist_zero_right,←h,Real.sqrt_sq (norm_nonneg z)]
  apply measure_mono_null hs
  rw [measure_union_null (stdGaussian_sphere_null k _) (stdGaussian_sphere_null k _)]

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

lemma cavitySphereLaw_shell_tendsto (k : ℕ) :
    Tendsto (fun n=>(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))) atTop (𝓝 (cavityShellMass k)) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (cavitySphereLaw_tendsto (k+1)) (cavityShell_frontier_null k))

lemma cavitySphereLaw_shell_log_tendsto (k : ℕ) :
    Tendsto (fun n=>Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))) atTop (𝓝 (Real.log (cavityShellMass k))) :=
  (cavitySphereLaw_shell_tendsto k).log (cavityShellMass_pos k).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBlockProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma cavityUnitEmbed_measurable (n L : ℕ) : Measurable (cavityUnitEmbed n L) := by
  unfold cavityUnitEmbed
  fun_prop

lemma cavity_radial_rho {r b : ℝ} (hr : 0 < r) (_hb : 0≤b) :
    Real.sqrt (1-((Real.sqrt (r^2+b^2))⁻¹*b)^2)=(Real.sqrt (r^2+b^2))⁻¹*r := by
  have hs : 0<Real.sqrt (r^2+b^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2:=Real.sq_sqrt (show 0 ≤ r^2+b^2 by positivity)
  have hsum : ((Real.sqrt (r^2+b^2))⁻¹*r)^2+((Real.sqrt (r^2+b^2))⁻¹*b)^2=1 := by
    field_simp
    nlinarith
  rw [show 1-((Real.sqrt (r^2+b^2))⁻¹*b)^2=((Real.sqrt (r^2+b^2))⁻¹*r)^2 by linarith,
    Real.sqrt_sq (by positivity)]

lemma cavityRadialBlock_unitEmbed (n L : ℕ)
    (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityUnitEmbed n L (p.1.2,cavityRadialUnit n L (p.1.1,p.2)) := by
  have ha : 0≤(Real.sqrt (p.1.1.val^2+‖p.2‖^2))⁻¹ := by positivity
  unfold cavityRadialBlock cavityUnitEmbed cavityRadialUnit
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,cavity_radial_rho p.1.1.prop (norm_nonneg p.2)]

lemma cavityRadial_reorder_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>(p.1.2,(p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod ((gaussianRadiusLaw n).prod (stdGaussian (Spin L)))) :=
  by
    let : IsProbabilityMeasure (unitSphereLaw (n+1)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    have hs : MeasurePreserving (Prod.swap : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 →
        Metric.sphere (0:Spin (n+1)) 1×Ioi (0:ℝ))
        ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1)))
        ((unitSphereLaw (n+1)).prod (gaussianRadiusLaw n)) := Measure.measurePreserving_swap
    exact (measurePreserving_prodAssoc (unitSphereLaw (n+1)) (gaussianRadiusLaw n) (stdGaussian (Spin L))).comp
      (hs.prod (MeasurePreserving.id (stdGaussian (Spin L))))

lemma cavityUnitPair_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>
      (p.1.2,cavityRadialUnit n L (p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)) :=
  by
    have h1 := MeasurePreserving.id (unitSphereLaw (n+1))
    have h2 : MeasurePreserving (cavityRadialUnit n L)
        ((gaussianRadiusLaw n).prod (stdGaussian (Spin L))) (cavityUnitLaw n L) :=
      ⟨cavityRadialUnit_measurable n L,rfl⟩
    exact (h1.prod h2).comp (cavityRadial_reorder_preserving n L)

theorem sphereBlock_product_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u=>gaussianBlockSplit (n+1) L u.val)=
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)).map (cavityUnitEmbed n L) := by
  rw [sphereBlock_radial_law,←(cavityUnitPair_preserving n L).map_eq,
    Measure.map_map (cavityUnitEmbed_measurable n L) (cavityUnitPair_preserving n L).measurable]
  congr 1
  funext p
  exact cavityRadialBlock_unitEmbed n L p

lemma cavityUnitLaw_actual (n L : ℕ) :
    (cavityUnitLaw n L : Measure (Spin L))=
      (unitSphereLaw (n+1+L)).map (fun u=>(gaussianBlockSplit (n+1) L u.val).2) := by
  have he:=congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>μ.map Prod.snd) (sphereBlock_product_law n L)
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1=>gaussianBlockSplit (n+1) L u.val) :=
    (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe
  rw [Measure.map_map measurable_snd hm,
    Measure.map_map measurable_snd (cavityUnitEmbed_measurable n L)] at he
  change _=((unitSphereLaw (n+1)).prod (cavityUnitLaw n L : Measure (Spin L))).map Prod.snd at he
  rw [Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he.symm

lemma cavitySphereLaw_unit (n L : ℕ) :
    (cavitySphereLaw n L : Measure (Spin L))=
      (cavityUnitLaw n L : Measure (Spin L)).map (fun z=>Real.sqrt (n+1+L:ℕ) •z) := by
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1 =>
      (gaussianBlockSplit (n+1) L u.val).2) :=
    (((gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe).snd)
  rw [cavityUnitLaw_actual,Measure.map_map (by fun_prop) hm]
  rfl

lemma cavitySphereBlockEmbed_measurable (n L : ℕ) : Measurable (cavitySphereBlockEmbed n L) := by
  unfold cavitySphereBlockEmbed
  apply (cavityUnitEmbed_measurable n L).comp
  fun_prop

lemma cavitySphereBlockEmbed_scaled (n L : ℕ) (x : Metric.sphere (0:Spin (n+1)) 1) (z : Spin L) :
    cavitySphereBlockEmbed n L (x,Real.sqrt (n+1+L:ℕ) •z)=cavityUnitEmbed n L (x,z) := by
  have hp : 0<Real.sqrt (n+1+L:ℕ) := Real.sqrt_pos.mpr (by positivity)
  simp only [cavitySphereBlockEmbed,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]

lemma cavitySphereBlockEmbed_formula (n L : ℕ) (p : Metric.sphere (0:Spin (n+1)) 1×Spin L) :
    cavitySphereBlockEmbed n L p=
      (Real.sqrt (1-‖p.2‖^2/(n+1+L:ℕ)) •p.1.val,(Real.sqrt (n+1+L:ℕ))⁻¹ •p.2) := by
  have hp : 0≤((n+1+L:ℕ):ℝ) := by positivity
  simp only [cavitySphereBlockEmbed,cavityUnitEmbed,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,inv_pow,Real.sq_sqrt hp,div_eq_mul_inv,mul_comm]

theorem sphereBlock_scaled_product_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u=>gaussianBlockSplit (n+1) L u.val)=
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)).map (cavitySphereBlockEmbed n L) := by
  have hs : MeasurePreserving (fun z : Spin L=>Real.sqrt (n+1+L:ℕ) •z)
      (cavityUnitLaw n L) (cavitySphereLaw n L) :=
    ⟨by fun_prop,(cavitySphereLaw_unit n L).symm⟩
  let : IsProbabilityMeasure (unitSphereLaw (n+1)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hp : MeasurePreserving (fun p : Metric.sphere (0:Spin (n+1)) 1×Spin L =>
      (p.1,Real.sqrt (n+1+L:ℕ) •p.2))
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L : Measure (Spin L)))
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L : Measure (Spin L))) :=
    (MeasurePreserving.id (unitSphereLaw (n+1))).prod hs
  rw [sphereBlock_product_law,←hp.map_eq,
    Measure.map_map (cavitySphereBlockEmbed_measurable n L) hp.measurable]
  congr 1
  funext p
  exact (cavitySphereBlockEmbed_scaled n L p.1 p.2).symm

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

lemma cavity_count_bounds {α : ℝ} (hα : 0≤α) (N : ℕ) :
    α*N-1≤(patternCount α N:ℝ) ∧ (patternCount α N:ℝ)≤α*N := by
  constructor
  · have h:=Nat.lt_floor_add_one (α*(N:ℝ))
    dsimp only [patternCount]
    linarith
  · exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg N))

lemma cavity_count_density {α : ℝ} (hα : 0≤α) :
    Tendsto (fun n=>(patternCount α (n+1):ℝ)/(n+1:ℕ)) atTop (𝓝 α) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi:=tendsto_inv_atTop_zero.comp hN
  have hl: Tendsto (fun n : ℕ=>α-((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 α) := by
    simpa only [sub_zero,Function.comp_def] using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    have h:=(cavity_count_bounds hα (n+1)).1
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
    calc
      _ = α*(n+1:ℕ)-1 := by field_simp
      _ ≤ _ := h
  · intro n
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2

lemma cavity_fresh_count {α : ℝ} (hα : 0≤α) (n L : ℕ) :
    patternCount α (n+1)+cavityFreshCount α n L=patternCount α (n+1+L) ∧
    |(cavityFreshCount α n L:ℝ)-(L:ℝ)*α|≤1 ∧
    cavityFreshCount α n L≤⌈(L:ℝ)*α+1⌉₊ := by
  have hm : patternCount α (n+1)≤patternCount α (n+1+L) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right (n+1) L) hα)
  have he : (cavityFreshCount α n L:ℝ)=(patternCount α (n+1+L):ℝ)-(patternCount α (n+1):ℝ) := by
    exact Nat.cast_sub hm
  refine ⟨Nat.add_sub_of_le hm,?_,?_⟩
  · rw [he,abs_le]
    have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    constructor <;> nlinarith [h0.1,h0.2,h1.1,h1.2]
  · have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    have hh : (cavityFreshCount α n L:ℝ)≤(L:ℝ)*α+1 := by rw [he]; nlinarith [h0.1,h1.2]
    exact_mod_cast hh.trans (Nat.le_ceil ((L:ℝ)*α+1))


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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
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

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityQuadraticDrop
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

lemma cavity_exp_abs_cauchy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H Q : Ω→ℝ} (hE : MemLp (fun y=>Real.exp (H y)) 2 P) (hQ : MemLp Q 2 P) :
    (∫ y,Real.exp (H y)*|Q y| ∂P)≤
      Real.sqrt (∫ y,Real.exp (2*H y) ∂P)*Real.sqrt (∫ y,(Q y)^2 ∂P) := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have he := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hE) (by simpa using hQ)
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.rpow_two, sq_abs] at he
  simp_rw [←Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat] at he
  simpa only [Real.sqrt_eq_rpow,one_div] using he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityUniformRemainder
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavityNormMoment_integrable (L p : ℕ) :
    Integrable (fun y : Spin L=>‖y‖^p) (stdGaussian (Spin L)) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (Spin L)) (p:ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma cavityRemainderMajorant_integrable (L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    Integrable (fun y : Spin L=>cavityRemainderMajorant c N ‖y‖) (stdGaussian (Spin L)) := by
  have h1 : Integrable (fun y : Spin L=>‖y‖) (stdGaussian (Spin L)) := by
    simpa using cavityNormMoment_integrable L 1
  exact (((integrable_const (c 0/N^2)).add ((h1.const_mul (c 1)).div_const _)).add
    (((cavityNormMoment_integrable L 2).const_mul (c 2)).div_const _)).add
    (((cavityNormMoment_integrable L 3).const_mul (c 3)).div_const _)

lemma cavityRemainderMajorant_mean (L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    (∫ y : Spin L,cavityRemainderMajorant c N ‖y‖ ∂stdGaussian (Spin L))=
      c 0/N^2+c 1*cavityNormMoment L 1/(N*Real.sqrt N)+
        c 2*cavityNormMoment L 2/N^2+c 3*cavityNormMoment L 3/(N*Real.sqrt N) := by
  have h1 : Integrable (fun y : Spin L=>‖y‖) (stdGaussian (Spin L)) := by
    simpa using cavityNormMoment_integrable L 1
  have h2:=cavityNormMoment_integrable L 2
  have h3:=cavityNormMoment_integrable L 3
  unfold cavityRemainderMajorant cavityNormMoment
  have hi0 : Integrable (fun _ : Spin L=>c 0/N^2) (stdGaussian (Spin L)) := integrable_const _
  have hi1 : Integrable (fun y : Spin L=>c 1*‖y‖/(N*Real.sqrt N)) (stdGaussian (Spin L)) :=
    (h1.const_mul _).div_const _
  have hi2 : Integrable (fun y : Spin L=>c 2*‖y‖^2/N^2) (stdGaussian (Spin L)) :=
    (h2.const_mul _).div_const _
  have hi3 : Integrable (fun y : Spin L=>c 3*‖y‖^3/(N*Real.sqrt N)) (stdGaussian (Spin L)) :=
    (h3.const_mul _).div_const _
  have ha := integral_add ((hi0.add hi1).add hi2) hi3
  have hb := integral_add (hi0.add hi1) hi2
  have hd := integral_add hi0 hi1
  simp only [Pi.add_apply] at ha hb hd
  rw [ha,hb,hd]
  simp only [integral_div,integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,pow_one]

lemma cavityRemainderMajorant_row_mean (M L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    (∫ y : Fin M→Spin L,∑ i,cavityRemainderMajorant c N ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
    M*(c 0/N^2+c 1*cavityNormMoment L 1/(N*Real.sqrt N)+
        c 2*cavityNormMoment L 2/N^2+c 3*cavityNormMoment L 3/(N*Real.sqrt N)) := by
  have hi (i : Fin M) : Integrable
      (fun y : Fin M→Spin L=>cavityRemainderMajorant c N ‖y i‖)
      (Measure.pi (fun _=>stdGaussian (Spin L))) :=
    ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i).integrable_comp
      (cavityRemainderMajorant_integrable L c N).aestronglyMeasurable).mpr
      (cavityRemainderMajorant_integrable L c N)
  rw [integral_finsetSum _ (fun i _=>hi i)]
  have he (i : Fin M) :
      (∫ y : Fin M→Spin L,cavityRemainderMajorant c N ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin L))) =
      ∫ y : Spin L,cavityRemainderMajorant c N ‖y‖ ∂stdGaussian (Spin L) := by
    have hp := measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i
    have hh := (integral_map hp.measurable.aemeasurable
      (hp.map_eq ▸ (cavityRemainderMajorant_integrable L c N).aestronglyMeasurable)).symm
    simpa only [hp.map_eq,Function.eval] using hh
  simp_rw [he,cavityRemainderMajorant_mean]
  simp
  ring

lemma cavityRemainderMajorant_row_tendsto (M : ℕ→ℕ) (L : ℕ) (c : Fin 4→ℝ)
    {α : ℝ} (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>∫ y : Fin (M n)→Spin L,∑ i,cavityRemainderMajorant c (n+1:ℕ) ‖y i‖
      ∂Measure.pi (fun _=>stdGaussian (Spin L))) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hs : Tendsto (fun n : ℕ=>(Real.sqrt (n+1:ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have ht:=hM.mul (((hi.const_mul (c 0)).add (hs.const_mul (c 1*cavityNormMoment L 1))).add
    (hi.const_mul (c 2*cavityNormMoment L 2)) |>.add (hs.const_mul (c 3*cavityNormMoment L 3)))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [cavityRemainderMajorant_row_mean]
  field_simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityExpectedQDrop
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavity_log_integrable_of_bound {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Y) (H : S×Y→ℝ)
    (hH : Measurable H) (K : Y→ℝ) (hK : Integrable K P)
    (hK0 : ∀ y,0≤K y) (hB : ∀ s y,|H (s,y)|≤K y) :
    Integrable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) P := by
  have hm : Measurable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) :=
    hH.exp.stronglyMeasurable.integral_prod_left'.measurable.log
  apply hK.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y=>by
    rw [Real.norm_eq_abs]
    simpa only [tiltPartition,one_mul,Function.comp_def,id_eq] using tilt_log_partition_bound μ
      (hH.comp (measurable_id.prodMk measurable_const)) (hK0 y) (fun s=>hB s y)

lemma cavity_quadratic_cost_tendsto_zero (M : ℕ→ℕ) (A B C D α : ℝ)
    (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>Real.exp (2*C+(1/Real.sqrt (n+1:ℕ))^2*D^2*M n*A^2)*
      Real.sqrt ((1/(2*(n+1:ℕ)))^2*(D^2)^2*squareGaussianVariance*M n*B^2))
        atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have he := ((hM.mul_const (D^2*A^2)).const_add (2*C)).rexp
  have hq := (((hM.mul hi).mul_const ((D^2)^2*squareGaussianVariance*B^2/4))).sqrt
  have ht := he.mul hq
  simp only [mul_zero,zero_mul,Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hs : Real.sqrt (n+1:ℕ)≠0 := (Real.sqrt_pos.mpr hn).ne'
  have hs2 := Real.sq_sqrt hn.le
  congr 2
  · rw [div_pow,one_pow,hs2]
    field_simp
  · field_simp
    ring

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

lemma bulkCovariance_bound (N : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovariance N v r|≤C^2 := by
  have ht (j : Fin N) :
      |((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2*v (j.val+1)^2*r^(j.val+1)|≤C^2*(1/2:ℝ)^(j.val+1) := by
    rw [perturbationWeight_eq,abs_mul,abs_mul,abs_sq,abs_sq,abs_pow]
    have hw0 : 0≤(1/2:ℝ)^(j.val+1) := by positivity
    have hw1 : (1/2:ℝ)^(j.val+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv2 : v (j.val+1)^2≤C^2 := by
      exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hv j.val)
    calc
      _ ≤ ((1/2:ℝ)^(j.val+1))^2*C^2*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _))
          (pow_le_one₀ (abs_nonneg r) hr) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (show ((1/2:ℝ)^(j.val+1))^2≤(1/2:ℝ)^(j.val+1) by nlinarith) (sq_nonneg C)]
  unfold bulkCovariance
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin N,C^2*(1/2:ℝ)^(j.val+1) := Finset.sum_le_sum fun j _=>ht j
    _ = C^2*(∑ j : Fin N,(1/2:ℝ)^(j.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (sq_nonneg C)
    _ = _ := mul_one _

lemma bulkCovariance_scaled_hasDerivAt (N : ℕ) (v : ℕ→ℝ) (r : ℝ) :
    HasDerivAt (fun t=>bulkScale N^2*bulkCovariance N v t)
      (bulkCovarianceDerivative N v r) r := by
  have he (t : ℝ) : bulkScale N^2*bulkCovariance N v t=
      ∑ j : Fin N,bulkAmplitude N v j^2*t^(j.val+1) := by
    simp only [bulkCovariance,bulkAmplitude,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  simpa [bulkCovarianceDerivative,mul_assoc] using HasDerivAt.fun_sum
    (u:=Finset.univ) (fun j (_ : j∈(Finset.univ : Finset (Fin N)))=>
      ((hasDerivAt_id r).pow (j.val+1)).const_mul (bulkAmplitude N v j^2))

lemma bulkCovariance_scaled_lipschitz (N : ℕ) (v : ℕ→ℝ) {C r s : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) (hs : |s|≤1) :
    |bulkScale N^2*bulkCovariance N v s-bulkScale N^2*bulkCovariance N v r|≤
      C^2*bulkScale N^2*|s-r| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t∈Icc (-1:ℝ) 1)=>(bulkCovariance_scaled_hasDerivAt N v t).hasDerivWithinAt)
    (fun t ht=>show ‖bulkCovarianceDerivative N v t‖≤C^2*bulkScale N^2 by
      simpa only [Real.norm_eq_abs] using bulkCovarianceDerivative_bound N v hC hv (abs_le.mpr ht))
    (convex_Icc (-1:ℝ) 1) (abs_le.mp hr) (abs_le.mp hs)
  simpa only [Real.norm_eq_abs] using hh

lemma bulkCovariance_dimension_tail (N L : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovariance (N+L) v r-bulkCovariance N v r|≤
      (L:ℝ)*C^2*(1/2:ℝ)^(N+1) := by
  have he : bulkCovariance (N+L) v r-bulkCovariance N v r=
      ∑ j : Fin L,((2:ℝ)^(-((N+j.val+1:ℕ):ℤ)))^2*v (N+j.val+1)^2*r^(N+j.val+1) := by
    unfold bulkCovariance
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd,add_sub_cancel_left]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ : Fin L,C^2*(1/2:ℝ)^(N+1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [perturbationWeight_eq,abs_mul,abs_mul,abs_sq,abs_sq,abs_pow]
      have hw0 : 0≤(1/2:ℝ)^(N+j.val+1) := by positivity
      have hw1 : (1/2:ℝ)^(N+j.val+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hwt : (1/2:ℝ)^(N+j.val+1)≤(1/2:ℝ)^(N+1) := by
        have he : N+j.val+1=(N+1)+j.val := by omega
        rw [he,pow_add]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num) : (1/2:ℝ)^j.val≤1) (by positivity)).trans_eq (mul_one _)
      have hv2 : v (N+j.val+1)^2≤C^2 := by
        exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hv (N+j.val))
      calc
        _ ≤ ((1/2:ℝ)^(N+j.val+1))^2*C^2*1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _))
            (pow_le_one₀ (abs_nonneg r) hr) (by positivity) (by positivity)
        _ ≤ C^2*(1/2:ℝ)^(N+j.val+1) := by
          nlinarith [mul_le_mul_of_nonneg_left (show ((1/2:ℝ)^(N+j.val+1))^2≤(1/2:ℝ)^(N+j.val+1) by nlinarith) (sq_nonneg C)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hwt (sq_nonneg C)
    _ = _ := by simp; ring

theorem cavity_bulk_covariance_bound (N L : ℕ) (v : ℕ→ℝ) {C r s : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) (hs : |s|≤1) :
    |bulkScale (N+L)^2*bulkCovariance (N+L) v s-bulkScale N^2*bulkCovariance N v r|≤
      C^2*bulkScale (N+L)^2*|s-r|+
        bulkScale (N+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(N+1))+
        |bulkScale (N+L)^2-bulkScale N^2| * C^2 := by
  calc
    _ ≤ |bulkScale (N+L)^2*bulkCovariance (N+L) v s-bulkScale (N+L)^2*bulkCovariance (N+L) v r|+
        |bulkScale (N+L)^2*bulkCovariance (N+L) v r-bulkScale N^2*bulkCovariance N v r| := abs_sub_le _ _ _
    _ ≤ C^2*bulkScale (N+L)^2*|s-r|+
        (bulkScale (N+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(N+1))+|bulkScale (N+L)^2-bulkScale N^2| * C^2) := by
      apply add_le_add (bulkCovariance_scaled_lipschitz (N+L) v hC hv hr hs)
      calc
        _ ≤ |bulkScale (N+L)^2*(bulkCovariance (N+L) v r-bulkCovariance N v r)|+
            |(bulkScale (N+L)^2-bulkScale N^2)*bulkCovariance N v r| := by
          convert abs_add_le (bulkScale (N+L)^2*(bulkCovariance (N+L) v r-bulkCovariance N v r))
            ((bulkScale (N+L)^2-bulkScale N^2)*bulkCovariance N v r) using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          ring
        _ ≤ _ := by
          rw [abs_mul,abs_sq,abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (bulkCovariance_dimension_tail N L v hC hv hr) (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (bulkCovariance_bound N v hC hv hr) (abs_nonneg _))
    _ = _ := by ring

lemma bulkScale_sq_eq_rpow (N : ℕ) : bulkScale N^2=(N:ℝ)^((3:ℝ)/4) := by
  unfold bulkScale
  rw [←Real.rpow_mul_natCast (Nat.cast_nonneg N)]
  norm_num

lemma bulkScale_sq_shift_bound (n L : ℕ) :
    |bulkScale (n+1+L)^2-bulkScale (n+1)^2|≤
      (3/4:ℝ)*(L:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hd (x : ℝ) (hx : x∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ)) :
      HasDerivWithinAt (fun x : ℝ=>x^((3:ℝ)/4))
        ((3/4:ℝ)*x^(-(1:ℝ)/4)) (Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ)) x := by
    simpa only [show (3:ℝ)/4-1=-(1:ℝ)/4 by norm_num] using
      (Real.hasDerivAt_rpow_const (p:=(3:ℝ)/4) (Or.inl (ne_of_gt (hn.trans_le hx.1)))).hasDerivWithinAt
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun x hx=>show ‖(3/4:ℝ)*x^(-(1:ℝ)/4)‖≤(3/4:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hn.trans_le hx.1).le _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn hx.1 (by norm_num)) (by norm_num))
    (convex_Icc _ _)
    (show ((n+1:ℕ):ℝ)∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ) by constructor; rfl; exact_mod_cast Nat.le_add_right (n+1) L)
    (show ((n+1+L:ℕ):ℝ)∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ) by constructor; exact_mod_cast Nat.le_add_right (n+1) L; rfl)
  rw [bulkScale_sq_eq_rpow,bulkScale_sq_eq_rpow]
  simpa only [Real.norm_eq_abs,Nat.cast_add,add_sub_cancel_left,
    abs_of_nonneg (Nat.cast_nonneg L : (0:ℝ)≤L),mul_assoc,mul_comm,mul_left_comm] using hh

lemma bulkScale_sq_div_shift_bound (n L : ℕ) :
    bulkScale (n+1+L)^2/(n+1:ℕ)≤
      (L+1:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hNL : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have he : bulkScale (n+1+L)^2=(n+1+L:ℕ)*((n+1+L:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [bulkScale_sq_eq_rpow]
    calc
      _ = ((n+1+L:ℕ):ℝ)^((1:ℝ)+(-(1:ℝ)/4)) := by norm_num
      _ = _ := by rw [Real.rpow_add hNL,Real.rpow_one]
  rw [he]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ((n+1+L:ℕ):ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn (by exact_mod_cast Nat.le_add_right (n+1) L) (by norm_num)) hNL.le
    _ ≤ _ := by
      have hb : ((n+1+L:ℕ):ℝ)≤(L+1:ℝ)*(n+1:ℕ) := by
        have h1 : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg L) (show (0:ℝ)≤(n+1:ℕ)-1 by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn.le (-(1:ℝ)/4))]

lemma cavityBulkCovarianceError_nonneg (n L : ℕ) (C : ℝ) {D : ℝ} (hD : 0≤D) :
    0 ≤ cavityBulkCovarianceError n L C D := by unfold cavityBulkCovarianceError; positivity

lemma cavity_bulk_covariance_shell (n L : ℕ) (v : ℕ→ℝ) {C D r s : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hv : ∀ j, |v (j+1)|≤C)
    (hr : |r|≤1) (hs : |s|≤1) (hδ : |s-r|≤D/(n+1:ℕ)) :
    |bulkScale (n+1+L)^2*bulkCovariance (n+1+L) v s-
      bulkScale (n+1)^2*bulkCovariance (n+1) v r| ≤ cavityBulkCovarianceError n L C D := by
  apply (cavity_bulk_covariance_bound (n+1) L v hC hv hr hs).trans
  unfold cavityBulkCovarianceError
  have ht : C^2*bulkScale (n+1+L)^2*|s-r|≤C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ)) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul hδ (le_refl (C^2*bulkScale (n+1+L)^2)) (by positivity)
        (div_nonneg hD (by positivity))
  exact add_le_add (add_le_add ht le_rfl) le_rfl

lemma cavityBulkCovarianceError_tendsto (L : ℕ) (C : ℝ) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun n=>cavityBulkCovarianceError n L C D) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)^(-(1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have hd : Tendsto (fun n=>C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ))) atTop (𝓝 0) :=
    squeeze_zero (fun n=>mul_nonneg (mul_nonneg (sq_nonneg C) hD) (by positivity))
      (fun n=>mul_le_mul_of_nonneg_left (bulkScale_sq_div_shift_bound n L)
        (mul_nonneg (sq_nonneg C) hD))
      (by simpa using (hp.const_mul (L+1:ℝ)).const_mul (C^2*D))
  have hs : Tendsto (fun n=>|bulkScale (n+1+L)^2-bulkScale (n+1)^2|) atTop (𝓝 0) :=
    squeeze_zero (fun n=>abs_nonneg _) (fun n=>bulkScale_sq_shift_bound n L)
      (by simpa using hp.const_mul ((3/4:ℝ)*(L:ℝ)))
  have hg : Tendsto (fun n : ℕ=>(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
      ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat 1))
  have hng : Tendsto (fun n : ℕ=>(n+1+1:ℕ)*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    simpa only [pow_one,Function.comp_def] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat 1))
  have hng' : Tendsto (fun n : ℕ=>(n+1+L:ℕ)*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    convert hng.add (hg.const_mul (L-1:ℝ)) using 1
    · ext n
      push_cast
      ring
    · simp
  have ht : Tendsto (fun n=>bulkScale (n+1+L)^2*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>by positivity) (fun n=>show _≤(n+1+L:ℕ)*(1/2:ℝ)^(n+1+1) from
      mul_le_mul_of_nonneg_right ?_ (by positivity)) hng'
    have hx : (1:ℝ)≤(n+1+L:ℕ) := by exact_mod_cast (by omega : 1≤n+1+L)
    rw [bulkScale_sq_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3:ℝ)/4≤1)
  convert (hd.add (ht.const_mul ((L:ℝ)*C^2))).add (hs.mul_const (C^2)) using 1
  · ext n
    unfold cavityBulkCovarianceError
    ring
  · simp
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma gaussianBlockJoin_measurable (N L : ℕ) : Measurable (gaussianBlockJoin N L) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> fun_prop

lemma gaussianBlockJoin_split (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockJoin N L (gaussianBlockSplit N L x)=x := by
  ext i
  induction i using Fin.addCases <;> simp [gaussianBlockSplit,gaussianBlockJoin]

lemma gaussianBlockJoin_inner (N L : ℕ) (p q : Spin N×Spin L) :
    inner ℝ (gaussianBlockJoin N L p) (gaussianBlockJoin N L q)=
      inner ℝ p.1 q.1+inner ℝ p.2 q.2 := by
  change (∑ i : Fin (N+L),gaussianBlockJoin N L q i*gaussianBlockJoin N L p i)=_
  rw [Fin.sum_univ_add]
  simp only [gaussianBlockJoin,PiLp.toLp_apply,Fin.addCases_left,Fin.addCases_right]
  rfl

lemma cavityRho_bounds (N L : ℕ) (z : Spin L) (hD : 0<(N+L:ℕ))
    (hz : ‖z‖^2≤(N+L:ℕ)) :
    0 ≤ cavityRho N L z ∧ cavityRho N L z≤1 ∧
      1-cavityRho N L z≤‖z‖^2/(N+L:ℕ) := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  have hq : 0≤‖z‖^2/(N+L:ℕ) := by positivity
  have hq1 : ‖z‖^2/(N+L:ℕ)≤1 := (div_le_one hDp).mpr hz
  have hsq := Real.sq_sqrt (show 0≤1-‖z‖^2/(N+L:ℕ) by linarith)
  have hp := Real.sqrt_nonneg (1-‖z‖^2/(N+L:ℕ))
  have hu : Real.sqrt (1-‖z‖^2/(N+L:ℕ))≤1 := by nlinarith
  refine ⟨hp,hu,?_⟩
  dsimp [cavityRho]
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hu)]

lemma cavityNormalizedVec_inner (N L : ℕ) (x x' : NormalizedSpin N) (z z' : Spin L)
    (hD : 0<(N+L:ℕ)) :
    inner ℝ (cavityNormalizedVec N L x z) (cavityNormalizedVec N L x' z')=
      cavityRho N L z*cavityRho N L z'*spinOverlap x x'+inner ℝ z z'/(N+L:ℕ) := by
  have hDp : (0:ℝ)<(N+L:ℕ) := by exact_mod_cast hD
  simp only [cavityNormalizedVec,gaussianBlockJoin_inner,inner_smul_left,inner_smul_right,
    conj_trivial,spinOverlap]
  rw [show (Real.sqrt (N+L:ℕ))⁻¹*((Real.sqrt (N+L:ℕ))⁻¹*inner ℝ z z')=
      inner ℝ z z'/(N+L:ℕ) by
    rw [←mul_assoc,←pow_two,inv_pow,Real.sq_sqrt hDp.le,div_eq_mul_inv,mul_comm]]
  ring

lemma cavityNormalizedVec_overlap_error (n L : ℕ) (x x' : NormalizedSpin (n+1))
    (z z' : Spin L) {D : ℝ} (hz : ‖z‖^2≤D) (hz' : ‖z'‖^2≤D)
    (hD : D≤(n+1+L:ℕ)) :
    |inner ℝ (cavityNormalizedVec (n+1) L x z) (cavityNormalizedVec (n+1) L x' z')-
      spinOverlap x x'|≤3*D/(n+1:ℕ) := by
  have hp : 0<(n+1+L:ℕ) := by omega
  have hpr : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have hD0 : 0≤D := (sq_nonneg ‖z‖).trans hz
  have hr := cavityRho_bounds (n+1) L z hp (hz.trans hD)
  have hr' := cavityRho_bounds (n+1) L z' hp (hz'.trans hD)
  have hrlo : 0 ≤ cavityRho (n+1) L z*cavityRho (n+1) L z' := mul_nonneg hr.1 hr'.1
  have hrhi : cavityRho (n+1) L z*cavityRho (n+1) L z'≤1 := by nlinarith
  have hrerr : |cavityRho (n+1) L z*cavityRho (n+1) L z'-1|≤2*D/(n+1+L:ℕ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hrhi)]
    have ha := (hr.2.2.trans (div_le_div_of_nonneg_right hz hpr.le))
    have hb := (hr'.2.2.trans (div_le_div_of_nonneg_right hz' hpr.le))
    rw [mul_div_assoc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2.1) (sub_nonneg.mpr hr'.2.1)]
  have hi : |inner ℝ z z'|≤D := by
    apply (abs_real_inner_le_norm z z').trans
    nlinarith [sq_nonneg (‖z‖-‖z'‖)]
  rw [cavityNormalizedVec_inner _ _ _ _ _ _ hp]
  have he : cavityRho (n+1) L z*cavityRho (n+1) L z'*spinOverlap x x'+inner ℝ z z'/(n+1+L:ℕ)-spinOverlap x x'=
      (cavityRho (n+1) L z*cavityRho (n+1) L z'-1)*spinOverlap x x'+inner ℝ z z'/(n+1+L:ℕ) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_div,abs_of_pos hpr]
  have hspin : |spinOverlap x x'|≤1 := spinOverlap_abs_le x x'
  calc
    _≤2*D/(n+1+L:ℕ)*1+D/(n+1+L:ℕ) :=
      add_le_add (mul_le_mul hrerr hspin (abs_nonneg _) (by positivity))
        (div_le_div_of_nonneg_right hi hpr.le)
    _=3*D/(n+1+L:ℕ) := by ring
    _≤3*D/(n+1:ℕ) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_cast; omega)

lemma cavityNormalizedVec_covariance (n L : ℕ) (v : ℕ→ℝ) (C : ℝ) (hC : 0≤C)
    (hv : ∀ j,|v (j+1)|≤C) (x x' : NormalizedSpin (n+1)) (z z' : Spin L)
    (hz : ‖z‖^2≤(L:ℝ)+1) (hz' : ‖z'‖^2≤(L:ℝ)+1) :
    |inner ℝ (ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L x z))
        (ambientBulkFeature (n+1+L) v (cavityNormalizedVec (n+1) L x' z'))-
      inner ℝ (bulkFeature (n+1) v x) (bulkFeature (n+1) v x')|≤
      cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  have hD : (L:ℝ)+1≤(n+1+L:ℕ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0<(n+1+L:ℕ) := by omega
  let u : NormalizedSpin (n+1+L):=⟨cavityNormalizedVec (n+1) L x z,by
    simpa only [Metric.mem_sphere,dist_zero_right] using cavityNormalizedVec_norm _ _ x z hp (hz.trans hD)⟩
  let u' : NormalizedSpin (n+1+L):=⟨cavityNormalizedVec (n+1) L x' z',by
    simpa only [Metric.mem_sphere,dist_zero_right] using cavityNormalizedVec_norm _ _ x' z' hp (hz'.trans hD)⟩
  change |inner ℝ (ambientBulkFeature _ v u.val) (ambientBulkFeature _ v u'.val)-_|≤_
  rw [ambientBulkFeature_eq,ambientBulkFeature_eq,bulkFeature_inner,bulkFeature_inner]
  apply cavity_bulk_covariance_shell n L v hC (by positivity) hv (spinOverlap_abs_le x x') (spinOverlap_abs_le u u')
  exact cavityNormalizedVec_overlap_error n L x x' z z' hz hz' hD

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellPerturbation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

lemma cavityRho_measurable (N L : ℕ) : Measurable (cavityRho N L) := by
  unfold cavityRho
  fun_prop

lemma cavityNormalizedVec_measurable (N L : ℕ) :
    Measurable (fun p : NormalizedSpin N×Spin L=>cavityNormalizedVec N L p.1 p.2) := by
  unfold cavityNormalizedVec
  apply (gaussianBlockJoin_measurable N L).comp
  exact (((cavityRho_measurable N L).comp measurable_snd).smul measurable_fst.subtype_val).prodMk
    (measurable_snd.const_smul ((Real.sqrt (N+L:ℕ))⁻¹))

lemma ambientBulkFeature_measurable_comp {S : Type*} [MeasurableSpace S]
    (N : ℕ) (v : ℕ→ℝ) {u : S→Spin N} (hu : Measurable u) :
    Measurable (fun s=>ambientBulkFeature N v (u s)) :=
  (ambientBulkFeature_contDiff N v).continuous.measurable.comp hu

lemma cavityShellFeature_measurable (n L : ℕ) (v : ℕ→ℝ) :
    Measurable (cavityShellFeature n L v) := by
  unfold cavityShellFeature
  apply ambientBulkFeature_measurable_comp
  exact (cavityNormalizedVec_measurable (n+1) L).comp
    (f:=fun s : CavityShellSpin n L=>(s.1,s.2.val))
    (measurable_fst.prodMk measurable_snd.subtype_val)

lemma cavityShellFeature_norm (n L : ℕ) (v : ℕ→ℝ) (s : CavityShellSpin n L) :
    ‖cavityShellFeature n L v s‖=bulkFeatureBound (n+1+L) v := by
  have hz : ‖s.2.val‖^2≤(n+1+L:ℕ) := s.2.prop.2.trans (by
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  let u : NormalizedSpin (n+1+L) := ⟨cavityNormalizedVec (n+1) L s.1 s.2.val,by
    simpa only [Metric.mem_sphere,dist_zero_right] using
      cavityNormalizedVec_norm _ _ s.1 s.2.val (by omega) hz⟩
  change ‖ambientBulkFeature _ v u.val‖=_
  rw [ambientBulkFeature_eq,bulkFeature_norm]

theorem cavity_shell_perturbation_comparison (n L : ℕ) (v : ℕ→ℝ)
    (μ : Measure (CavityShellSpin n L)) [IsProbabilityMeasure μ]
    {H : CavityShellSpin n L→ℝ} (hH : Measurable H)
    {A C : ℝ} (hA : 0≤A) (hC : 0≤C) (hHA : ∀ s,|H s|≤A)
    (hv : ∀ j,|v (j+1)|≤C) :
    |(∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (cavityShellFeature n L v s) g) 1)
        ∂stdGaussian (BulkMark (n+1+L)))-
      ∫ g,Real.log (tiltPartition μ (fun s=>H s+inner ℝ (bulkFeature (n+1) v s.1) g) 1)
        ∂stdGaussian (BulkMark (n+1))|≤
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  let B := bulkFeatureBound (n+1) v+bulkFeatureBound (n+1+L) v
  have hB1 : 0≤bulkFeatureBound (n+1) v := Real.sqrt_nonneg _
  have hB2 : 0≤bulkFeatureBound (n+1+L) v := Real.sqrt_nonneg _
  apply independentGaussian_covariance_comparison μ hH
    ((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst)
    (cavityShellFeature_measurable n L v) hA
    (C:=B) (by dsimp [B]; positivity) hHA
  · intro s
    simp only [Function.comp_apply,bulkFeature_norm]
    exact le_add_of_nonneg_right hB2
  · intro s
    rw [cavityShellFeature_norm]
    exact le_add_of_nonneg_left hB1
  · exact cavityBulkCovarianceError_nonneg _ _ _ (by positivity)
  · intro x y
    exact cavityNormalizedVec_covariance n L v C hC hv x.1 y.1 x.2.val y.2.val x.2.prop.2 y.2.prop.2

lemma cavityShellProbability_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellProbability n L) := by
  let ν := (cavitySphereLaw n L : Measure (Spin L))
  let := cond_isProbabilityMeasure (μ:=ν) hp
  apply (MeasurableEmbedding.subtype_coe (cavityShell_measurable L)).isProbabilityMeasure_comap
  simp only [Subtype.range_coe]
  apply (mem_ae_iff_prob_eq_one (cavityShell_measurable L)).mpr
  exact cond_apply_self hp (measure_ne_top _ _)

lemma cavityShellBaseLaw_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellBaseLaw n L) := by
  let := cavityShellProbability_probability n L hp
  unfold cavityShellBaseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cavityShell_probability_eventually (k : ℕ) :
    ∀ᶠ n in atTop, (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0 := by
  have he := (cavitySphereLaw_shell_tendsto k).eventually (lt_mem_nhds (cavityShellMass_pos k))
  filter_upwards [he] with n hn
  exact ne_of_gt (ENNReal.toReal_pos_iff.mp hn).1

lemma cavityShellSpinEmbedding_measurable (n L : ℕ) : Measurable (cavityShellSpinEmbedding n L) := by
  apply Measurable.subtype_mk
  exact (cavityNormalizedVec_measurable (n+1) L).comp
    (f:=fun s : CavityShellSpin n L=>(s.1,s.2.val))
    (measurable_fst.prodMk measurable_snd.subtype_val)

lemma cavityShellPatternEnergy_measurable (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) : Measurable (cavityShellPatternEnergy n L M f a) := by
  exact (normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp
    (f:=fun s : CavityShellSpin n L=>(a,cavityShellSpinEmbedding n L s))
    (measurable_const.prodMk (cavityShellSpinEmbedding_measurable n L))

lemma cavityShellPatternEnergy_bound (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L M f a s|≤M*‖f‖ :=
  normalizedPatternEnergy_bound _ _ _ _ _

theorem cavity_true_shell_perturbation (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ j,|v (j+1)|≤C)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    |(∫ g,Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g) 1)
        ∂stdGaussian (BulkMark (n+1+L)))-
      ∫ g,Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (bulkFeature (n+1) v s.1) g) 1)
        ∂stdGaussian (BulkMark (n+1))|≤
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1)) := by
  let := cavityShellBaseLaw_probability n L hp
  exact cavity_shell_perturbation_comparison n L v (cavityShellBaseLaw n L)
    (cavityShellPatternEnergy_measurable n L M f a) (by positivity) hC
    (cavityShellPatternEnergy_bound n L M f a) hv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellExpansion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityJoinedPatterns_projection (N L M : ℕ) (a : Fin M→Fin N→ℝ)
    (y : Fin M→Spin L) (x : NormalizedSpin N) (z : Spin L) (i : Fin M) :
    (∑ j,cavityJoinedPatterns N L M a y i j*cavityNormalizedVec N L x z j)=
      cavityRho N L z*(∑ j,a i j*x.val j)+inner ℝ z (y i)/Real.sqrt (N+L:ℕ) := by
  rw [Fin.sum_univ_add]
  simp only [cavityJoinedPatterns,cavityNormalizedVec,gaussianBlockJoin,PiLp.toLp_apply,
    Fin.addCases_left,Fin.addCases_right,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [Finset.mul_sum,Finset.sum_div]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro j _hj
    ring

lemma cavityShellPatternEnergy_join (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (s : CavityShellSpin n L) :
    cavityShellPatternEnergy n L M f (cavityJoinedPatterns (n+1) L M a y) s=
      ∑ i,f (Real.sqrt (1-‖s.2.val‖^2/((n+1:ℕ)+L))*(∑ j,a i j*s.1.val j)+
        inner ℝ s.2.val (y i)/Real.sqrt ((n+1:ℕ)+L)) := by
  unfold cavityShellPatternEnergy normalizedPatternEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  change (∑ j,cavityJoinedPatterns (n+1) L M a y i j*cavityNormalizedVec (n+1) L s.1 s.2.val j)=_
  rw [cavityJoinedPatterns_projection]
  simp only [cavityRho,Nat.cast_add]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteEvaluation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma gaussianBlockJoin_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockJoin N L)
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L)))
      (stdGaussian (Spin (N+L))) := by
  refine ⟨gaussianBlockJoin_measurable N L,?_⟩
  rw [←(gaussianBlockSplit_preserving N L).map_eq,
    Measure.map_map (gaussianBlockJoin_measurable N L) (gaussianBlockSplit_measurable N L)]
  simp only [Function.comp_def,gaussianBlockJoin_split]
  exact Measure.map_id

lemma stdGaussian_ofLp_preserving (N : ℕ) :
    MeasurePreserving (WithLp.ofLp : Spin N→Fin N→ℝ) (stdGaussian (Spin N))
      (Measure.pi fun _=>gaussianReal 0 1) := by
  refine ⟨(PiLp.continuous_ofLp 2 _).measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,
    Measure.map_map (PiLp.continuous_ofLp 2 _).measurable (PiLp.continuous_toLp 2 _).measurable]
  exact Measure.map_id

lemma cavityJoinedPatterns_preserving (N L M : ℕ) :
    MeasurePreserving (fun p : (Fin M→Fin N→ℝ)×(Fin M→Spin L)=>
      cavityJoinedPatterns N L M p.1 p.2)
      ((Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
      (Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1) := by
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hj := (stdGaussian_ofLp_preserving (N+L)).comp
    ((gaussianBlockJoin_preserving N L).comp (ht.prod (MeasurePreserving.id _)))
  have hp := measurePreserving_pi (fun _ : Fin M=>(Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
      (stdGaussian (Spin L))) (fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1)
      (fun _=>hj)
  have hr := (measurePreserving_arrowProdEquivProdArrow (Fin N→ℝ) (Spin L) (Fin M)
    (fun _=>Measure.pi fun _=>gaussianReal 0 1) (fun _=>stdGaussian (Spin L))).symm
  convert hp.comp hr using 1
  all_goals try with_reducible_and_instances rfl
  funext p i j
  rfl

lemma cavity_log_uniform_change {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {F G : S→ℝ}
    (hF : Measurable F) (hG : Measurable G) {A E : ℝ} (hA : 0≤A)
    (hFA : ∀ s,|F s|≤A) (hE : ∀ s,|F s-G s|≤E) :
    |Real.log (∫ s,Real.exp (F s) ∂μ)-Real.log (∫ s,Real.exp (G s) ∂μ)|≤E := by
  have hGA (s : S) : |G s|≤A+|E| := by
    calc
      _=|G s-F s+F s| := by ring_nf
      _≤|G s-F s|+|F s| := abs_add_le _ _
      _≤|E|+A := add_le_add ((show |G s-F s|≤E by simpa only [abs_sub_comm] using hE s).trans (le_abs_self E)) (hFA s)
      _=A+|E| := add_comm _ _
  have hFi : Integrable (fun s=>Real.exp (F s)) μ := by
    apply Integrable.of_bound hF.exp.aestronglyMeasurable (Real.exp A)
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hFA s))
  have hGi : Integrable (fun s=>Real.exp (G s)) μ := by
    apply Integrable.of_bound hG.exp.aestronglyMeasurable (Real.exp (A+|E|))
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hGA s))
  exact abs_log_integral_exp_sub_le μ hFi hGi
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hF hA hFA 1)
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hG (by positivity) hGA 1) hE

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFreshReplacement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityNormMoment_two (N : ℕ) : cavityNormMoment N 2=N := by
  unfold cavityNormMoment
  rw [←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ:=fun _ : Fin N=>gaussianReal 0 1)
      (f:=fun y : ℝ=>y^2) (by fun_prop),gaussian_square_mean]
    simp
  · intro i _
    exact ((gaussian_square_memLp_two 1).comp_measurePreserving
      (measurePreserving_eval _ i)).integrable (by norm_num)

lemma cavityNormMoment_one_le (N : ℕ) : cavityNormMoment N 1≤Real.sqrt N := by
  have h := cavity_exp_abs_cauchy (stdGaussian (Spin N))
    (H:=fun _=>0) (Q:=fun y=>‖y‖)
    (by simpa using (memLp_const (1:ℝ) : MemLp (fun _ : Spin N=>(1:ℝ)) 2 (stdGaussian (Spin N))))
    ((IsGaussian.memLp_id (stdGaussian (Spin N)) 2 (by norm_num)).norm)
  simp only [Real.exp_zero,one_mul,abs_of_nonneg (norm_nonneg _),mul_zero,
    integral_const,probReal_univ,smul_eq_mul,Real.sqrt_one] at h
  have he : (∫ y : Spin N,‖y‖^2 ∂stdGaussian (Spin N))=N := cavityNormMoment_two N
  rw [he] at h
  simpa only [cavityNormMoment,pow_one] using h

lemma cavity_fresh_pattern_error (n L : ℕ) (f : Jet3) (a : Fin (n+1)→ℝ)
    (y : Spin L) (s : CavityShellSpin n L) :
    |f.f (cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+
      inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ))-f.f (∑ j,a j*s.1.val j)|≤
    ‖f.d1‖*(((L:ℝ)+1)/(n+1+L:ℕ)*‖WithLp.toLp 2 a‖+
      ((L:ℝ)+1)/Real.sqrt (n+1+L:ℕ)*‖y‖) := by
  have hp : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have hz := s.2.prop.2
  have hD : ‖s.2.val‖^2≤(n+1+L:ℕ) := by
    simp only [Nat.cast_add,Nat.cast_one] at *
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hr := cavityRho_bounds (n+1) L s.2.val (by omega) hD
  have hz1 : ‖s.2.val‖≤(L:ℝ)+1 := by
    nlinarith [sq_nonneg (‖s.2.val‖-1),Nat.cast_nonneg (α:=ℝ) L]
  have hx : ‖s.1.val‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using s.1.prop
  have ha : |∑ j,a j*s.1.val j|≤‖WithLp.toLp 2 a‖ := by
    have hi := abs_real_inner_le_norm s.1.val (WithLp.toLp 2 a)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      starRingEnd_apply,star_trivial,PiLp.toLp_apply,hx,one_mul] using hi
  have hi : |inner ℝ s.2.val y|≤((L:ℝ)+1)*‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hz1 (norm_nonneg _))
  have hl := f.lipschitz.dist_le_mul
    (cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ))
    (∑ j,a j*s.1.val j)
  simp only [Real.dist_eq,coe_nnnorm] at hl
  apply hl.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [show cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ)-
    (∑ j,a j*s.1.val j)=(cavityRho (n+1) L s.2.val-1)*(∑ j,a j*s.1.val j)+
    inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_div,abs_of_pos (Real.sqrt_pos.mpr hp),abs_of_nonpos (sub_nonpos.mpr hr.2.1)]
  apply add_le_add
  · have hb := hr.2.2.trans (div_le_div_of_nonneg_right hz hp.le)
    exact mul_le_mul (by simpa only [neg_sub] using hb) ha (abs_nonneg _) (by positivity)
  · simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hi (Real.sqrt_nonneg _)

lemma cavity_fresh_pattern_sum_error (n L d : ℕ) (f : Jet3)
    (a : Fin d→Fin (n+1)→ℝ) (y : Fin d→Spin L) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L d f.f (cavityJoinedPatterns (n+1) L d a y) s-
      normalizedPatternEnergy (n+1) d f.f a s.1| ≤ cavityFreshMajorant (n+1) L d f a y := by
  rw [cavityShellPatternEnergy_join]
  unfold normalizedPatternEnergy cavityFreshMajorant
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simpa only [cavityRho,Nat.cast_add,Nat.cast_one] using cavity_fresh_pattern_error n L f (a i) (y i) s

lemma cavity_fresh_log_replacement (n L d : ℕ) (f : Jet3)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (H : CavityShellSpin n L→ℝ) (hH : Measurable H) {A : ℝ}
    (hA : 0≤A) (hHA : ∀ s,|H s|≤A)
    (a : Fin d→Fin (n+1)→ℝ) (y : Fin d→Spin L) :
    |Real.log (∫ s,Real.exp (H s+cavityShellPatternEnergy n L d f.f
        (cavityJoinedPatterns (n+1) L d a y) s) ∂cavityShellBaseLaw n L)-
      Real.log (∫ s,Real.exp (H s+normalizedPatternEnergy (n+1) d f.f a s.1)
        ∂cavityShellBaseLaw n L)| ≤ cavityFreshMajorant (n+1) L d f a y := by
  let := cavityShellBaseLaw_probability n L hp
  have hnew := cavityShellPatternEnergy_measurable n L d f.f
    (cavityJoinedPatterns (n+1) L d a y)
  have hold : Measurable (fun s : CavityShellSpin n L=>normalizedPatternEnergy (n+1) d f.f a s.1) := by
    unfold normalizedPatternEnergy
    have hc := f.f.continuous.measurable
    fun_prop
  apply cavity_log_uniform_change (cavityShellBaseLaw n L) (hH.add hnew) (hH.add hold)
    (A:=A+d*‖f.f‖) (add_nonneg hA (by positivity))
  · intro s
    exact (abs_add_le _ _).trans (add_le_add (hHA s) (cavityShellPatternEnergy_bound n L d f.f _ s))
  · intro s
    simpa only [Pi.add_apply,add_sub_add_left_eq_sub] using cavity_fresh_pattern_sum_error n L d f a y s

lemma cavity_row_norm_integrable (d L : ℕ) :
    Integrable (fun y : Fin d→Spin L=>∑ i,‖y i‖) (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  apply integrable_finsetSum
  intro i hi
  simpa only [pow_one,Function.comp_def,Function.eval] using ((measurePreserving_eval (fun _ : Fin d=>stdGaussian (Spin L)) i).integrable_comp_of_integrable
    (cavityNormMoment_integrable L 1))

lemma cavity_row_norm_mean (d L : ℕ) :
    (∫ y : Fin d→Spin L,∑ i,‖y i‖ ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      d*cavityNormMoment L 1 := by
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ:=fun _ : Fin d=>stdGaussian (Spin L))
      (f:=fun y : Spin L=>‖y‖) (by fun_prop)]
    simp [cavityNormMoment]
  · intro i hi
    simpa only [pow_one,Function.comp_def,Function.eval] using ((measurePreserving_eval (fun _ : Fin d=>stdGaussian (Spin L)) i).integrable_comp_of_integrable
      (cavityNormMoment_integrable L 1))

lemma cavityFreshMajorant_integrable (N L d : ℕ) (f : Jet3) :
    Integrable (fun p : (Fin d→Spin N)×(Fin d→Spin L)=>
      cavityFreshMajorant N L d f (fun i=>WithLp.ofLp (p.1 i)) p.2)
      ((Measure.pi (fun _=>stdGaussian (Spin N))).prod (Measure.pi (fun _=>stdGaussian (Spin L)))) := by
  simp only [cavityFreshMajorant,WithLp.toLp_ofLp,Finset.sum_add_distrib,←Finset.mul_sum]
  exact ((((cavity_row_norm_integrable d N).comp_fst (Measure.pi (fun _ : Fin d=>stdGaussian (Spin L)))).const_mul _).add
    (((cavity_row_norm_integrable d L).comp_snd (Measure.pi (fun _ : Fin d=>stdGaussian (Spin N)))).const_mul _)).const_mul _

lemma cavityFreshMajorant_mean (N L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Spin N)×(Fin d→Spin L),
      cavityFreshMajorant N L d f (fun i=>WithLp.ofLp (p.1 i)) p.2
      ∂(Measure.pi (fun _=>stdGaussian (Spin N))).prod (Measure.pi (fun _=>stdGaussian (Spin L))))=
      ‖f.d1‖*d*(((L:ℝ)+1)/(N+L:ℕ)*cavityNormMoment N 1+
        ((L:ℝ)+1)/Real.sqrt (N+L:ℕ)*cavityNormMoment L 1) := by
  simp only [cavityFreshMajorant,WithLp.toLp_ofLp,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [integral_const_mul,integral_add
    (((cavity_row_norm_integrable d N).comp_fst (Measure.pi (fun _ : Fin d=>stdGaussian (Spin L)))).const_mul _)
    (((cavity_row_norm_integrable d L).comp_snd (Measure.pi (fun _ : Fin d=>stdGaussian (Spin N)))).const_mul _)]
  simp only [integral_const_mul]
  rw [integral_fun_fst (fun a : Fin d→Spin N=>∑ i,‖a i‖),
    integral_fun_snd (fun y : Fin d→Spin L=>∑ i,‖y i‖)]
  simp only [probReal_univ,one_smul,cavity_row_norm_mean]
  ring

lemma cavityFreshMajorant_mean_bound (n L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Spin (n+1))×(Fin d→Spin L),
      cavityFreshMajorant (n+1) L d f (fun i=>WithLp.ofLp (p.1 i)) p.2
      ∂(Measure.pi (fun _=>stdGaussian (Spin (n+1)))).prod (Measure.pi (fun _=>stdGaussian (Spin L))))≤
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ) := by
  rw [cavityFreshMajorant_mean]
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hnL : ((n+1:ℕ):ℝ)≤(n+1+L:ℕ) := by exact_mod_cast Nat.le_add_right (n+1) L
  have ha : ((L:ℝ)+1)/(n+1+L:ℕ)*cavityNormMoment (n+1) 1≤
      ((L:ℝ)+1)/Real.sqrt (n+1:ℕ) := by
    calc
      _≤((L:ℝ)+1)/(n+1+L:ℕ)*Real.sqrt (n+1:ℕ) :=
        mul_le_mul_of_nonneg_left (cavityNormMoment_one_le _) (by positivity)
      _≤((L:ℝ)+1)/(n+1:ℕ)*Real.sqrt (n+1:ℕ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hn hnL) (Real.sqrt_nonneg _)
      _=((L:ℝ)+1)/Real.sqrt (n+1:ℕ) := by
        rw [div_mul_eq_mul_div,mul_div_assoc,Real.sqrt_div_self']
        ring
  have hb : ((L:ℝ)+1)/Real.sqrt (n+1+L:ℕ)*cavityNormMoment L 1≤
      ((L:ℝ)+1)/Real.sqrt (n+1:ℕ)*Real.sqrt L := by
    exact (mul_le_mul_of_nonneg_left (cavityNormMoment_one_le L) (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hn) (Real.sqrt_le_sqrt hnL))
        (Real.sqrt_nonneg _))
  apply (mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity : 0≤‖f.d1‖*(d:ℝ))).trans_eq
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellRestriction
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma unitSphere_cavityAmbient_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map Subtype.val=
      ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)).map
        (fun p=>cavityNormalizedVec (n+1) L p.1 p.2) := by
  have h:=congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>μ.map (gaussianBlockJoin (n+1) L))
    (sphereBlock_scaled_product_law n L)
  have hm : Measurable (fun u : NormalizedSpin (n+1+L)=>gaussianBlockSplit (n+1) L u.val) :=
    (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe
  rw [Measure.map_map (gaussianBlockJoin_measurable (n+1) L) hm,
    Measure.map_map (gaussianBlockJoin_measurable (n+1) L) (cavitySphereBlockEmbed_measurable n L)] at h
  simpa only [Function.comp_def,gaussianBlockJoin_split,cavitySphereBlockEmbed_formula,
    cavityNormalizedVec,cavityRho] using h

lemma cavityShellProbability_integral (n L : ℕ) (F : Spin L→ℝ) :
    (∫ z : {z : Spin L // z∈cavityShell L},F z.val ∂cavityShellProbability n L)=
      ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))⁻¹*
        ∫ z in cavityShell L,F z ∂(cavitySphereLaw n L : Measure (Spin L)) := by
  unfold cavityShellProbability
  rw [integral_subtype_comap (cavityShell_measurable L)]
  simp only [ProbabilityTheory.cond,Measure.restrict_smul,Measure.restrict_restrict (cavityShell_measurable L),
    inter_self,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.real]

theorem cavity_actual_shell_restriction (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (F : NormalizedSpin (n+1+L)→ℝ) (hF : Measurable F) {A : ℝ} (hA : 0≤A)
    (hF0 : ∀ x,0≤F x) (hFA : ∀ x,F x≤A) :
    (cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L)*
      (∫ s,F (cavityShellSpinEmbedding n L s) ∂cavityShellBaseLaw n L)≤
        ∫ x,F x ∂unitSphereLaw (n+1+L) := by
  let := cavityShellBaseLaw_probability n L hp
  let := cavityShellProbability_probability n L hp
  obtain ⟨E,hE,hEF⟩ := (MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet :
    MeasurableSet (Metric.sphere (0:Spin (n+1+L)) 1))).exists_measurable_extend hF (fun _=>inferInstance)
  let W : Spin (n+1+L)→ℝ:=fun x=>max 0 (min A (E x))
  have hW : Measurable W:=measurable_const.max (measurable_const.min hE)
  have hW0 (x) : 0≤W x := le_max_left _ _
  have hWA (x) : W x≤A := max_le hA (min_le_left _ _)
  have hWF (x : NormalizedSpin (n+1+L)) : W x.val=F x := by
    have he : E x.val=F x := congrFun hEF x
    simp only [W,he,min_eq_right (hFA x),max_eq_right (hF0 x)]
  let G : NormalizedSpin (n+1)×Spin L→ℝ:=fun p=>W (cavityNormalizedVec (n+1) L p.1 p.2)
  have hG : Measurable G:=hW.comp (cavityNormalizedVec_measurable (n+1) L)
  have hi : Integrable G ((unitSphereLaw (n+1)).prod (cavitySphereLaw n L)) := by
    apply Integrable.of_bound hG.aestronglyMeasurable A
    exact ae_of_all _ fun p=>by
      change ‖W (cavityNormalizedVec (n+1) L p.1 p.2)‖≤A
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hW0 _)] using hWA (cavityNormalizedVec (n+1) L p.1 p.2)
  have heq : (∫ x,F x ∂unitSphereLaw (n+1+L))=
      ∫ p,G p ∂(unitSphereLaw (n+1)).prod (cavitySphereLaw n L) := by
    calc
      _=∫ x,W x.val ∂unitSphereLaw (n+1+L) := integral_congr_ae (ae_of_all _ fun x=>(hWF x).symm)
      _=∫ x,W x ∂(unitSphereLaw (n+1+L)).map Subtype.val :=
        (integral_map measurable_subtype_coe.aemeasurable hW.aestronglyMeasurable).symm
      _=_ := by rw [unitSphere_cavityAmbient_law,integral_map (cavityNormalizedVec_measurable (n+1) L).aemeasurable hW.aestronglyMeasurable]
  rw [heq,integral_prod _ hi]
  have hsi : Integrable (fun s : CavityShellSpin n L=>F (cavityShellSpinEmbedding n L s))
      (cavityShellBaseLaw n L) := by
    apply Integrable.of_bound (hF.comp (cavityShellSpinEmbedding_measurable n L)).aestronglyMeasurable A
    exact ae_of_all _ fun s=>by
      change ‖F (cavityShellSpinEmbedding n L s)‖≤A
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 _)] using hFA (cavityShellSpinEmbedding n L s)
  rw [cavityShellBaseLaw,integral_prod _ hsi,←integral_const_mul]
  apply integral_mono_ae
  · exact hsi.integral_prod_left.const_mul _
  · exact hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  have hs : (fun z : {z : Spin L // z∈cavityShell L}=>F (cavityShellSpinEmbedding n L (x,z)))=
      (fun z=>G (x,z.val)) := by
    funext z
    exact (hWF (cavityShellSpinEmbedding n L (x,z))).symm
  rw [hs]
  have hc:=cavityShellProbability_integral n L (fun z=>G (x,z))
  rw [hc]
  have hm : (cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L)≠0 :=
    ne_of_gt (ENNReal.toReal_pos hp (measure_ne_top _ _))
  rw [←mul_assoc,mul_inv_cancel₀ hm,one_mul]
  exact setIntegral_le_integral hx (ae_of_all _ fun z=>hW0 _)


lemma cavityShell_bulkHamiltonian (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (g : BulkMark (n+1+L)) (s : CavityShellSpin n L) :
    bulkHamiltonian (n+1+L) M f v a g (cavityShellSpinEmbedding n L s)=
      cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g := by
  unfold bulkHamiltonian cavityShellPatternEnergy cavityShellFeature
  exact congrArg (fun y=> (∑ i, f (∑ j, a i j * (cavityShellSpinEmbedding n L s).val j))+
    inner ℝ y g) (ambientBulkFeature_eq (n+1+L) v (cavityShellSpinEmbedding n L s)).symm

lemma cavity_restriction_log_of_bounded (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (H : NormalizedSpin (n+1+L)→ℝ) (hH : Measurable H) {A : ℝ}
    (hA : 0≤A) (hB : ∀ x,|H x|≤A) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))+
      Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>H (cavityShellSpinEmbedding n L s)) 1)≤
      Real.log (tiltPartition (unitSphereLaw (n+1+L)) H 1) := by
  let := cavityShellBaseLaw_probability n L hp
  have hR := cavity_actual_shell_restriction n L hp
    (fun x=>Real.exp (H x)) hH.exp
    (Real.exp_pos A).le (fun _=>(Real.exp_pos _).le)
    (fun x=>Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x)))
  have hm : 0<(cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L) :=
    ENNReal.toReal_pos hp (measure_ne_top _ _)
  have hs := tilt_partition_pos (cavityShellBaseLaw n L)
    (hH.comp (cavityShellSpinEmbedding_measurable n L)) hA
    (fun s=>hB (cavityShellSpinEmbedding n L s)) 1
  simp only [tiltPartition,one_mul,Function.comp_apply] at hs
  have hh := Real.log_le_log (mul_pos hm hs) hR
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hs)] at hh
  simpa only [tiltPartition,one_mul] using hh

lemma cavity_actual_shell_log_restriction (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (g : BulkMark (n+1+L))
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))+
      Real.log (tiltPartition (cavityShellBaseLaw n L)
        (fun s=>cavityShellPatternEnergy n L M f a s+inner ℝ (cavityShellFeature n L v s) g) 1)≤
      Real.log (tiltPartition (unitSphereLaw (n+1+L))
        (bulkHamiltonian (n+1+L) M f v a g) 1) := by
  have hH : Measurable (bulkHamiltonian (n+1+L) M f v a g) :=
    (bulkHamiltonian_section_measurable (n+1+L) M f v (a,g))
  have h := cavity_restriction_log_of_bounded n L hp
    (bulkHamiltonian (n+1+L) M f v a g) hH
    (add_nonneg (mul_nonneg (Nat.cast_nonneg M) (norm_nonneg f))
      (mul_nonneg (by unfold bulkFeatureBound; positivity) (norm_nonneg g)))
    (bulkHamiltonian_bound (n+1+L) M f v (a,g))
  simpa only [cavityShell_bulkHamiltonian] using h

lemma cavity_gaussian_log_integrable {I S : Type} [Fintype I] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S→ℝ} {V : S→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hHA : ∀ s,|H s|≤A) (hVB : ∀ s,‖V s‖≤B) :
    Integrable (fun g=>Real.log (tiltPartition μ (fun s=>H s+inner ℝ (V s) g) 1))
      (stdGaussian (EuclideanSpace ℝ I)) := by
  apply Integrable.mono' ((integrable_const A).add
    ((IsGaussian.integrable_id (μ:=stdGaussian (EuclideanSpace ℝ I))).norm.const_mul B))
    (gaussianLogPartition_measurable_finite μ hH hV).aestronglyMeasurable
  exact ae_of_all _ fun g=>by
    rw [Real.norm_eq_abs]
    apply tilt_log_partition_bound μ (hH.add (hV.inner measurable_const))
      (add_nonneg hA (mul_nonneg hB (norm_nonneg _)))
    intro s
    apply (abs_add_le _ _).trans
    exact add_le_add (hHA s) ((abs_real_inner_le_norm (V s) g).trans
      (mul_le_mul_of_nonneg_right (hVB s) (norm_nonneg _)))

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

lemma cavity_integral_preserving {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure A) (ν : Measure B)
    (F : A→B) (hF : MeasurePreserving F μ ν) (g : B→E) (hg : AEStronglyMeasurable g ν) :
    (∫ a,g (F a) ∂μ)=∫ b,g b ∂ν := by
  rw [←hF.map_eq] at hg ⊢
  exact (integral_map hF.measurable.aemeasurable hg).symm

lemma cavity_prod_front_swap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : A×B×C=>(p.2.1,p.1,p.2.2))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  exact (measurePreserving_prodAssoc ν μ ρ).comp
    ((Measure.measurePreserving_swap.prod (MeasurePreserving.id ρ)).comp
      (measurePreserving_prodAssoc μ ν ρ).symm)

lemma cavity_product_shuffle {A G B Y Z : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [MeasurableSpace B] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure A) (γ : Measure G) (ν : Measure B) (η : Measure Y) (ζ : Measure Z)
    [SFinite μ] [SFinite γ] [SFinite ν] [SFinite η] [SFinite ζ] :
    MeasurePreserving (fun p : (A×G)×B×Y×Z=>(((p.1.1,p.2.2.1),(p.2.1,p.2.2.2)),p.1.2))
      ((μ.prod γ).prod (ν.prod (η.prod ζ))) (((μ.prod η).prod (ν.prod ζ)).prod γ) := by
  have h1:=(MeasurePreserving.id (μ.prod γ)).prod (cavity_prod_front_swap ν η ζ)
  have h2:=measurePreserving_prodAssoc μ γ (η.prod (ν.prod ζ))
  have h3:=(MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=γ) (ν:=η.prod (ν.prod ζ)))
  have h4:=(measurePreserving_prodAssoc μ (η.prod (ν.prod ζ)) γ).symm
  have h5:=((measurePreserving_prodAssoc μ η (ν.prod ζ)).symm).prod (MeasurePreserving.id γ)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma cavityRowsAppend_preserving (N M d : ℕ) :
    MeasurePreserving (fun p=>cavityRowsAppend N M d p.1 p.2)
      ((finitePatternRowsLaw N M).prod (finitePatternRowsLaw N d))
      (finitePatternRowsLaw N (M+d)) := by
  convert (measurePreserving_piCongrLeft (fun _ : Fin (M+d)=>Measure.pi fun _ : Fin N=>gaussianReal 0 1)
    finSumFinEquiv).comp (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin M⊕Fin d=>Measure.pi fun _ : Fin N=>gaussianReal 0 1)) using 1
  · funext p i
    simp only [Function.comp_apply,MeasurableEquiv.coe_piCongrLeft,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    rcases h : finSumFinEquiv.symm i with j | j <;> simp [cavityRowsAppend,Equiv.piCongrLeft_apply,h,Equiv.sumPiEquivProdPi]
  · rfl
  · rfl

lemma normalizedPatternEnergy_append (N M d : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin N→ℝ) (b : Fin d→Fin N→ℝ) (x : NormalizedSpin N) :
    normalizedPatternEnergy N (M+d) f (cavityRowsAppend N M d a b) x=
      normalizedPatternEnergy N M f a x+normalizedPatternEnergy N d f b x := by
  unfold normalizedPatternEnergy
  rw [←finSumFinEquiv.sum_comp]
  simp only [cavityRowsAppend,Equiv.symm_apply_apply,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma cavityShellPatternEnergy_append (n L M d : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (b : Fin d→Fin (n+1+L)→ℝ) (x : CavityShellSpin n L) :
    cavityShellPatternEnergy n L (M+d) f (cavityRowsAppend (n+1+L) M d a b) x=
      cavityShellPatternEnergy n L M f a x+cavityShellPatternEnergy n L d f b x := by
  exact normalizedPatternEnergy_append _ _ _ _ _ _ _


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

lemma cavityShellPatternEnergy_joint_measurable (n L M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f p.1 p.2) := by
  change Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>normalizedPatternEnergy (n+1+L) M f p.1 (cavityShellSpinEmbedding n L p.2))
  exact (normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp
    (f:=fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>(p.1,cavityShellSpinEmbedding n L p.2))
    (measurable_fst.prodMk ((cavityShellSpinEmbedding_measurable n L).comp measurable_snd))

lemma cavityShellLowLog_integrable (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (cavityShellLowLog n L M f v)
      ((finitePatternRowsLaw (n+1+L) M).prod (stdGaussian (BulkMark (n+1)))) := by
  let := cavityShellBaseLaw_probability n L hp
  apply cavity_gaussian_joint_log_integrable _ _ _ _
    (cavityShellPatternEnergy_joint_measurable n L M f)
    ((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst)
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
    (cavityShellPatternEnergy_bound n L M f)
  intro x
  exact (bulkFeature_norm _ _ _).le

lemma bulkExpectedLog_nested (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkExpectedLog n M f v=∫ a,∫ g,Real.log (tiltPartition (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 1) ∂stdGaussian (BulkMark (n+1))
      ∂finitePatternRowsLaw (n+1) M := by
  unfold bulkExpectedLog bulkDisorderLaw
  rw [integral_prod _ ((bulkLogPartition_memLp n M f v).integrable (by norm_num))]
  simp_rw [bulkLogPartition_eq]
  rfl

theorem cavity_expected_shell_restriction (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))-
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1))+
      (∫ p,cavityShellLowLog n L M f v p
        ∂(finitePatternRowsLaw (n+1+L) M).prod (stdGaussian (BulkMark (n+1))))≤
      bulkExpectedLog (n+L) M f v := by
  let := cavityShellBaseLaw_probability n L hp
  have hlo:=cavityShellLowLog_integrable n L M f v hp
  have hhi:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1+L) M)
    (cavityShellBaseLaw n L) (cavityShellPatternEnergy n L M f) (cavityShellFeature n L v)
    (cavityShellPatternEnergy_joint_measurable n L M f) (cavityShellFeature_measurable n L v)
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (cavityShellPatternEnergy_bound n L M f)
    (fun x=>(cavityShellFeature_norm n L v x).le)
  rw [integral_prod _ hlo,bulkExpectedLog_nested]
  rw [show n+L+1=n+1+L by omega]
  let : IsProbabilityMeasure (unitSphereLaw (n+1+L)) := by
    rw [show n+1+L=(n+L)+1 by omega]; infer_instance
  have hb:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1+L) M)
    (unitSphereLaw (n+1+L)) (normalizedPatternEnergy (n+1+L) M f) (bulkFeature (n+1+L) v)
    (normalizedPatternEnergy_continuous (n+1+L) M f).measurable (bulkFeature_continuous _ _).measurable
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (normalizedPatternEnergy_bound _ _ _)
    (fun x=>(bulkFeature_norm _ _ _).le)
  have hpoint : ∀ a,Real.log ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))-
      Real.pi*cavityBulkCovarianceError n L C (3*((L:ℝ)+1))+
      (∫ g,cavityShellLowLog n L M f v (a,g) ∂stdGaussian (BulkMark (n+1)))≤
      ∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
        (bulkHamiltonian (n+1+L) M f v a g) 1) ∂stdGaussian (BulkMark (n+1+L)) := by
    intro a
    have hr:=cavity_gaussian_log_integrable (cavityShellBaseLaw n L)
      (cavityShellPatternEnergy_measurable n L M f a) (cavityShellFeature_measurable n L v)
      (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _) (cavityShellPatternEnergy_bound n L M f a)
      (fun x=>(cavityShellFeature_norm n L v x).le)
    have hb':=cavity_gaussian_log_integrable (unitSphereLaw (n+1+L))
      ((normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp (measurable_const.prodMk measurable_id))
      (bulkFeature_continuous (n+1+L) v).measurable (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
      (normalizedPatternEnergy_bound _ _ _ a) (fun x=>(bulkFeature_norm _ _ _).le)
    have hc:=cavity_true_shell_perturbation n L M f a v hC hv hp
    have hh:=integral_mono ((integrable_const _).add hr) hb'
      (cavity_actual_shell_log_restriction n L M f v a · hp)
    simp only [Pi.add_apply,Function.comp_def,id_eq] at hh
    rw [integral_add (integrable_const _) hr,integral_const,probReal_univ,one_smul] at hh
    dsimp [cavityShellLowLog] at ⊢
    change _≤∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
      (fun s=>normalizedPatternEnergy (n+1+L) M f a s+inner ℝ (bulkFeature (n+1+L) v s) g) 1) ∂_
    linarith [(abs_le.mp hc).1]
  have hi:=integral_mono ((integrable_const _).add hlo.integral_prod_left) hb.integral_prod_left hpoint
  simp only [Pi.add_apply] at hi
  change _≤∫ a,∫ g,Real.log (tiltPartition (unitSphereLaw (n+1+L))
    (fun s=>normalizedPatternEnergy (n+1+L) M f a s+inner ℝ (bulkFeature (n+1+L) v s) g) 1)
      ∂stdGaussian (BulkMark (n+1+L)) ∂finitePatternRowsLaw (n+1+L) M
  simpa only [integral_add (integrable_const _) hlo.integral_prod_left,integral_const,probReal_univ,one_smul,bulkHamiltonian] using hi
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityIncrementLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityIncrementFullRows_preserving (n L M d : ℕ) :
    MeasurePreserving (fun p : CavityIncrementRandom n L M d=>(cavityIncrementFullRows n L M d p,p.1.2))
      (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1)))) := by
  let : IsProbabilityMeasure (stdGaussian (BulkMark (n+1))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) M) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1+L) M) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1+L) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : SFinite (stdGaussian (BulkMark (n+1))) := inferInstance
  let : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have h1 := cavity_product_shuffle (finitePatternRowsLaw (n+1) M) (stdGaussian (BulkMark (n+1)))
    (finitePatternRowsLaw (n+1) d) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))
    (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))
  let : SFinite ((finitePatternRowsLaw (n+1) M).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))) := inferInstance
  let : SFinite ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := inferInstance
  have hOld : MeasurePreserving (fun p=>(cavityJoinedPatterns (n+1) L M p.1 p.2))
      ((finitePatternRowsLaw (n+1) M).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
      (finitePatternRowsLaw (n+1+L) M) := cavityJoinedPatterns_preserving (n+1) L M
  have hNew : MeasurePreserving (fun p=>(cavityJoinedPatterns (n+1) L d p.1 p.2))
      ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
      (finitePatternRowsLaw (n+1+L) d) := cavityJoinedPatterns_preserving (n+1) L d
  have h2 := hOld.prod hNew
  have h3 := h2.prod (MeasurePreserving.id (stdGaussian (BulkMark (n+1))))
  have h4 := (cavityRowsAppend_preserving (n+1+L) M d).prod
    (MeasurePreserving.id (stdGaussian (BulkMark (n+1))))
  exact h4.comp (h3.comp h1)

lemma cavityShellLowLog_measurable (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Measurable (cavityShellLowLog n L M f v) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hH : Measurable (fun p : ((Fin M→Fin (n+1+L)→ℝ)×BulkMark (n+1))×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f p.1.1 p.2+inner ℝ (bulkFeature (n+1) v p.2.1) p.1.2) :=
    ((cavityShellPatternEnergy_joint_measurable n L M f).comp
      (measurable_fst.fst.prodMk measurable_snd)).add
      (((bulkFeature_continuous (n+1) v).measurable.comp measurable_snd.fst).inner measurable_fst.snd)
  unfold cavityShellLowLog tiltPartition
  simpa only [one_mul] using
    (hH.exp.stronglyMeasurable.integral_prod_right' (ν:=cavityShellBaseLaw n L)).measurable.log

lemma cavityIncrement_actual_integrable (n L M d : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (fun p : CavityIncrementRandom n L M d=>
      cavityShellLowLog n L (M+d) f v (cavityIncrementFullRows n L M d p,p.1.2))
        (cavityIncrementLaw n L M d) :=
  ((cavityIncrementFullRows_preserving n L M d).integrable_comp
    (cavityShellLowLog_measurable n L (M+d) f v hp).aestronglyMeasurable).mpr
      (cavityShellLowLog_integrable n L (M+d) f v hp)

lemma cavityIncrement_actual_expectation (n L M d : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    (∫ p : CavityIncrementRandom n L M d,
      cavityShellLowLog n L (M+d) f v (cavityIncrementFullRows n L M d p,p.1.2)
        ∂cavityIncrementLaw n L M d)=
      ∫ p,cavityShellLowLog n L (M+d) f v p
        ∂(finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1))) :=
  cavity_integral_preserving _ _ _ (cavityIncrementFullRows_preserving n L M d) _
    (cavityShellLowLog_measurable n L (M+d) f v hp).aestronglyMeasurable

lemma finiteRows_toLp_preserving (N d : ℕ) :
    MeasurePreserving (fun a : Fin d→Fin N→ℝ=>fun i=>WithLp.toLp 2 (a i))
      (finitePatternRowsLaw N d) (Measure.pi fun _ : Fin d=>stdGaussian (Spin N)) := by
  apply measurePreserving_pi
  intro i
  exact ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩

lemma cavityFreshMajorant_rows_integrable (N L d : ℕ) (f : Jet3) :
    Integrable (fun p : (Fin d→Fin N→ℝ)×(Fin d→Spin L)=>cavityFreshMajorant N L d f p.1 p.2)
      ((finitePatternRowsLaw N d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := by
  have hi:=cavityFreshMajorant_integrable N L d f
  have hp:=(finiteRows_toLp_preserving N d).prod (MeasurePreserving.id (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
  convert (hp.integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma cavityFreshMajorant_rows_mean_bound (n L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Fin (n+1)→ℝ)×(Fin d→Spin L),cavityFreshMajorant (n+1) L d f p.1 p.2
      ∂(finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))≤
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ) := by
  let : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have hi:=cavityFreshMajorant_integrable (n+1) L d f
  have hp:=(finiteRows_toLp_preserving (n+1) d).prod (MeasurePreserving.id (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
  have h:=cavity_integral_preserving _ _ _ hp _ hi.aestronglyMeasurable
  exact (Eq.trans (by rfl) h).le.trans (cavityFreshMajorant_mean_bound n L d f)

lemma cavityProxyProjection_preserving (n L M d : ℕ) :
    MeasurePreserving (cavityProxyProjection n L M d) (cavityIncrementLaw n L M d) (cavityProxyLaw n L M d) :=
  (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod measurePreserving_fst)

lemma cavityProxyHamiltonian_measurable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>cavityProxyHamiltonian n L M d f v p.1 p.2) := by
  have hj : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) :=
    (cavityJoinedPatterns_preserving (n+1) L M).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.1.1,p.1.2.2))
      (measurable_fst.fst.fst.prodMk measurable_fst.snd.snd)
  have hs : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) p.2) :=
    (cavityShellPatternEnergy_joint_measurable n L M f.f).comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2,p.2))
      (hj.prodMk measurable_snd)
  have hm : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      inner ℝ (bulkFeature (n+1) v p.2.1) p.1.1.2) :=
    (((bulkFeature_continuous (n+1) v).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>p.2.1) measurable_snd.fst).inner measurable_fst.fst.snd)
  have hn : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      normalizedPatternEnergy (n+1) d f.f p.1.2.1 p.2.1) :=
    (normalizedPatternEnergy_continuous (n+1) d f.f).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.2.1,p.2.1))
      (measurable_fst.snd.fst.prodMk measurable_snd.fst)
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact (hs.add hm).add hn

lemma cavityProxyLog_measurable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Measurable (cavityProxyLog n L M d f v) := by
  let :=cavityShellBaseLaw_probability n L hp
  exact (cavityProxyHamiltonian_measurable n L M d f v).exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma cavityProxyHamiltonian_bound (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : CavityProxyRandom n L M d) (s : CavityShellSpin n L) :
    |cavityProxyHamiltonian n L M d f v p s|≤(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ := by
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
      (by simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) p.1.2)))
        (normalizedPatternEnergy_bound (n+1) d f.f _ _))).trans_eq (by ring)

lemma cavityProxyLog_integrable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (cavityProxyLog n L M d f v) (cavityProxyLaw n L M d) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hb : Integrable (fun p : BulkDisorder (n+1) M=>‖p.2‖) (bulkDisorderLaw (n+1) M) :=
    (IsGaussian.integrable_id (μ:=stdGaussian (BulkMark (n+1)))).norm.comp_snd (finitePatternRowsLaw (n+1) M)
  have hg : Integrable (fun p : CavityProxyRandom n L M d=>‖p.1.2‖) (cavityProxyLaw n L M d) :=
    hb.comp_fst ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
  have hm : Measurable (fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>
      cavityProxyHamiltonian n L M d f v p.2 p.1) :=
    (cavityProxyHamiltonian_measurable n L M d f v).comp
      (f:=fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>(p.2,p.1)) measurable_swap
  unfold cavityProxyLog
  apply cavity_log_integrable_of_bound (cavityShellBaseLaw n L) (cavityProxyLaw n L M d)
    (fun p=>cavityProxyHamiltonian n L M d f v p.2 p.1)
    hm
    (fun p=>(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖)
    ((integrable_const _).add (hg.const_mul _))
    (fun p=>by unfold bulkFeatureBound; positivity)
  intro s p
  exact cavityProxyHamiltonian_bound n L M d f v p s

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityOldExpectation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma cavity_actual_proxy_log_bound (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (p : CavityIncrementRandom n L M d) :
    |cavityShellLowLog n L (M+d) f.f v (cavityIncrementFullRows n L M d p,p.1.2)-
      cavityProxyLog n L M d f v (cavityProxyProjection n L M d p)|≤
        cavityFreshMajorant (n+1) L d f p.2.1 p.2.2.2 := by
  let H:=fun s : CavityShellSpin n L=>cavityShellPatternEnergy n L M f.f
    (cavityJoinedPatterns (n+1) L M p.1.1 p.2.2.1) s+inner ℝ (bulkFeature (n+1) v s.1) p.1.2
  have hm : Measurable H := (cavityShellPatternEnergy_measurable n L M f.f _).add
    (((bulkFeature_continuous (n+1) v).measurable.comp measurable_fst).inner measurable_const)
  have hb : ∀ s,|H s|≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ := by
    intro s
    exact (abs_add_le _ _).trans (add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
      (by simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) p.1.2))
  have hh:=cavity_fresh_log_replacement n L d f hp H hm
    (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ from by unfold bulkFeatureBound; positivity)
    hb p.2.1 p.2.2.2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  unfold cavityShellLowLog tiltPartition cavityIncrementFullRows
  simp_rw [one_mul,cavityShellPatternEnergy_append]
  congr 2
  funext s
  congr 1
  dsimp only [H]
  ring

lemma cavityFreshProjection_preserving (n L M d : ℕ) :
    MeasurePreserving (fun p : CavityIncrementRandom n L M d=>(p.2.1,p.2.2.2))
      (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L))) := by
  have : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have h1 : MeasurePreserving Prod.snd (cavityIncrementLaw n L M d)
      ((finitePatternRowsLaw (n+1) d).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod
        (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))) := measurePreserving_snd
  have h2 : MeasurePreserving Prod.snd
      ((Measure.pi fun _ : Fin M=>stdGaussian (Spin L)).prod (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)))
      (Measure.pi fun _ : Fin d=>stdGaussian (Spin L)) := measurePreserving_snd
  exact ((MeasurePreserving.id (finitePatternRowsLaw (n+1) d)).prod h2).comp h1

lemma cavity_fresh_expected_lower (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    (∫ p,cavityProxyLog n L M d f v p ∂cavityProxyLaw n L M d)-
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ)≤
    ∫ p,cavityShellLowLog n L (M+d) f.f v p
      ∂(finitePatternRowsLaw (n+1+L) (M+d)).prod (stdGaussian (BulkMark (n+1))) := by
  let F:=fun p : CavityIncrementRandom n L M d=>
    cavityShellLowLog n L (M+d) f.f v (cavityIncrementFullRows n L M d p,p.1.2)
  let G:=fun p : CavityIncrementRandom n L M d=>cavityProxyLog n L M d f v (cavityProxyProjection n L M d p)
  let R:=fun p : CavityIncrementRandom n L M d=>cavityFreshMajorant (n+1) L d f p.2.1 p.2.2.2
  have hF:=cavityIncrement_actual_integrable n L M d f.f v hp
  have hG : Integrable G (cavityIncrementLaw n L M d) := (cavityProxyProjection_preserving n L M d).integrable_comp_of_integrable
    (cavityProxyLog_integrable n L M d f v hp)
  have hr:=cavityFreshMajorant_rows_integrable (n+1) L d f
  have hR : Integrable R (cavityIncrementLaw n L M d) := (cavityFreshProjection_preserving n L M d).integrable_comp_of_integrable hr
  have hi:=integral_mono (hG.sub hR) hF (fun p=>by
    have hb:=(abs_le.mp (cavity_actual_proxy_log_bound n L M d f v hp p)).1
    change G p-R p≤F p
    dsimp only [F,G,R]
    linarith)
  change (∫ p,G p-R p ∂cavityIncrementLaw n L M d)≤∫ p,F p ∂cavityIncrementLaw n L M d at hi
  rw [integral_sub hG hR] at hi
  have heG:=cavity_integral_preserving _ _ _ (cavityProxyProjection_preserving n L M d) _
    (cavityProxyLog_measurable n L M d f v hp).aestronglyMeasurable
  have heR:=cavity_integral_preserving _ _ _ (cavityFreshProjection_preserving n L M d) _ hr.aestronglyMeasurable
  change (∫ p,G p ∂cavityIncrementLaw n L M d)=_ at heG
  change (∫ p,R p ∂cavityIncrementLaw n L M d)=_ at heR
  rw [heG,heR] at hi
  have heF:=cavityIncrement_actual_expectation n L M d f.f v hp
  change (∫ p,F p ∂cavityIncrementLaw n L M d)=_ at heF
  rw [heF] at hi
  exact (sub_le_sub_left (cavityFreshMajorant_rows_mean_bound n L d f) _).trans hi
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem cavity_finite_increment_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))-
      Real.pi*cavityBulkCovarianceError n (k+1) C (3*((k+1:ℕ)+1))-
      cavityOldError n k M d f h1 h2 h3-
      ‖f.d1‖*d*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)+
      cavityBulkFullLog k d n M f v ≤
      bulkExpectedLog (n+(k+1)) (M+d) f.f v-bulkExpectedLog n M f.f v := by
  have hs:=cavity_expected_shell_restriction n (k+1) (M+d) f.f v hC hv hp
  have hf:=cavity_fresh_expected_lower n (k+1) M d f v hp
  have ho:=cavity_proxy_expected_lower n k M d f h1 h2 h3 hn hp v
  simp only [Nat.cast_add,Nat.cast_one] at *
  linarith

lemma cavityUniformError_tendsto (k D : ℕ) (M : ℕ→ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (C KC : ℝ) {α : ℝ}
    (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>cavityUniformError n k (M n) D f h1 h2 h3 C KC) atTop (𝓝 0) := by
  have hc:=(cavityBulkCovarianceError_tendsto (k+1) C (by positivity : (0:ℝ)≤3*((k+1:ℕ)+1))).const_mul Real.pi
  have hq:=cavity_quadratic_cost_tendsto_zero M ‖f.d1‖ ‖f.d2‖
    (D*‖f.f‖+((k+1:ℕ)+1)*KC/2) ((k+1:ℕ)+1) α hM
  have hr:=cavityRemainderMajorant_row_tendsto M (k+1)
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) hM
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hf:=(tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).const_mul
    (‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1)))
  convert ((hc.add hq).add hr).add hf using 1 <;>
    simp [cavityUniformError,div_eq_mul_inv]

lemma cavity_finite_increment_uniform (n k M d D : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) {C KC : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (hd : d≤D) (hK : M/(n+1:ℕ)*‖f.dilationMark h1‖≤KC) :
    Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))-KC/2-
      cavityUniformError n k M D f h1 h2 h3 C KC+cavityBulkFullLog k d n M f v ≤
      bulkExpectedLog (n+(k+1)) (M+d) f.f v-bulkExpectedLog n M f.f v := by
  have hinc:=cavity_finite_increment_lower n k M d f h1 h2 h3 hn hp v hC hv
  have hd' : (d:ℝ)≤D:=by exact_mod_cast hd
  have hE : d*‖f.f‖+((k+1:ℕ)+1)*(M/(n+1:ℕ)*‖f.dilationMark h1‖)/2≤
      D*‖f.f‖+((k+1:ℕ)+1)*KC/2 := by gcongr
  have hq :
      Real.exp (2*(d*‖f.f‖+((k+1:ℕ)+1)*(M/(n+1:ℕ)*‖f.dilationMark h1‖)/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2) ≤
      Real.exp (2*(D*‖f.f‖+((k+1:ℕ)+1)*KC/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2) := by
    gcongr
  have hf : ‖f.d1‖*d*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)≤
      ‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ) := by gcongr
  dsimp only [cavityOldError] at hinc
  dsimp only [cavityUniformError]
  simp only [Nat.cast_add,Nat.cast_one] at *
  linarith


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

lemma cavity_original_increment_error_oai {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2-δ+
        cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v≤
      cavityOriginalIncrement α g.f n k v := by
  let KC:=α*‖g.dilationMark h1‖
  let D:=⌈((k+1:ℕ):ℝ)*α+1⌉₊
  let E:=fun n=>cavityUniformError n k (patternCount α (n+1)) D g h1 h2 h3 2 KC
  have hE : Tendsto E atTop (𝓝 0):=cavityUniformError_tendsto k D _ g h1 h2 h3 2 KC (cavity_count_density hα)
  have he:=((cavitySphereLaw_shell_log_tendsto k).sub_const (KC/2)).sub hE
  simp only [sub_zero] at he
  have hev:=he.eventually (Ioi_mem_nhds (show Real.log (cavityShellMass k)-KC/2-δ<
    Real.log (cavityShellMass k)-KC/2 by linarith))
  filter_upwards [hev,cavityShell_probability_eventually k,eventually_ge_atTop (2*((k+1)+1))] with n hn hp hN
  intro v hv
  have hK : (patternCount α (n+1):ℝ)/(n+1:ℕ)*‖g.dilationMark h1‖≤KC := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2
  have hinc:=cavity_finite_increment_uniform n k (patternCount α (n+1)) (cavityFreshCount α n (k+1)) D
    g h1 h2 h3 (by omega) hp v (by norm_num : (0:ℝ)≤2) hv (cavity_fresh_count hα n (k+1)).2.2 hK
  rw [(cavity_fresh_count hα n (k+1)).1] at hinc
  have heq : n+1+(k+1)=n+(k+1)+1:=by omega
  rw [heq] at hinc
  change _ ≤ cavityOriginalIncrement α g.f n k v at hinc
  dsimp only [E,KC] at hn hinc
  linarith


end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error_oai := @OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error_oai
