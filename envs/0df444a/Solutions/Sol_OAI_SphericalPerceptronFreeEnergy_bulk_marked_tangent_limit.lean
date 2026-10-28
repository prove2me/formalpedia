-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:30:26.222254+00:00
-- url     : https://prove2.me/submissions/9953b45e-e991-4d75-8505-e88955cf627b

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

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

lemma tilt_law_probability {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    IsProbabilityMeasure (tiltLaw μ v t) := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral {v F : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    ∫ x, F x ∂tiltLaw μ v t = tiltMean μ v F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (Real.exp (t * v x))) from (hv.const_mul t).exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos μ hv hC hvC t).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

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

section GibbsProducts
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_law_apply {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ v t s = (ENNReal.ofReal (tiltPartition μ v t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * v x) ∂μ) := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply _ (replicaPotential_measurable hv n)
    (mul_nonneg (Nat.cast_nonneg n) hC) (replicaPotential_bound hvC n) t (MeasurableSet.univ_pi hs),
    replica_partition μ hv n,ENNReal.ofReal_pow (tilt_partition_pos μ hv hC hvC t).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential v n x) =
      ∏ i, Real.exp (t * v (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply μ hv hC hvC t (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

end GibbsProducts

lemma gaussian_pi_coordinate_integrationByParts (n : ℕ) (i : Fin (n+1))
    {F D : (Fin (n+1) → ℝ) → ℝ} (hF : Measurable F) (hD : Measurable D)
    {C B : ℝ} (hFC : ∀ g, |F g| ≤ C) (hDB : ∀ g, |D g| ≤ B)
    (hd : ∀ (g : Fin n → ℝ) (t : ℝ),
      HasDerivAt (fun u => F (i.insertNth u g)) (D (i.insertNth t g)) t) :
    (∫ g, g i * F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, D g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hmF : Measurable (fun p : ℝ × (Fin n → ℝ) => F (i.insertNth p.1 p.2)) :=
    hF.comp e.measurable
  have hmD : Measurable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2)) :=
    hD.comp e.measurable
  have hiF : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * F (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) := by
    apply ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst ν |>.mul_bdd
      hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFC (i.insertNth p.1 p.2)
  have hiD : Integrable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    Integrable.of_bound hmD.aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hDB (i.insertNth p.1 p.2))
  rw [← he.integral_comp e.measurableEmbedding (fun g => g i * F g),
    ← he.integral_comp e.measurableEmbedding D]
  change (∫ p : ℝ × (Fin n → ℝ), ((i.insertNth p.1 p.2 : Fin (n+1) → ℝ) i) *
    F (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν) =
      ∫ p : ℝ × (Fin n → ℝ), D (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν
  simp only [Fin.insertNth_apply_same]
  rw [integral_prod_symm _ hiF,integral_prod_symm _ hiD]
  apply integral_congr_ae
  exact ae_of_all _ fun g => standardGaussian_integrationByParts (hd g)
    (hmD.comp (measurable_id.prodMk measurable_const))
    (fun t => hFC (i.insertNth t g)) (fun t => hDB (i.insertNth t g))

section GaussianField
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean {Ω : Type*} [MeasurableSpace Ω]
    {v : Ω → S → ℝ} {F : S → ℝ} (hv : Measurable (Function.uncurry v))
    (hF : Measurable F) : Measurable (fun g => tiltMean μ (v g) F 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hv.exp.mul (hF.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable).div
      hv.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma gaussianField_measurable {n : ℕ} {v : Fin n → S → ℝ}
    (hv : ∀ i, Measurable (v i)) :
    Measurable (fun p : (Fin n → ℝ) × S => gaussianField n v p.1 p.2) := by
  unfold gaussianField
  fun_prop

omit [MeasurableSpace S] in
lemma gaussianField_insertNth {n : ℕ} (i : Fin (n+1)) (v : Fin (n+1) → S → ℝ)
    (g : Fin n → ℝ) (t : ℝ) (x : S) :
    gaussianField (n+1) v (i.insertNth t g) x =
      t*v i x + gaussianField n (fun j => v (i.succAbove j)) g x := by
  classical
  rw [gaussianField,Fin.sum_univ_succAbove _ i]
  simp [gaussianField]

omit [IsProbabilityMeasure μ] in
lemma tilt_mean_mulObservable {v F : S → ℝ} (c t : ℝ) :
    tiltMean μ v (fun x => c*F x) t = c * tiltMean μ v F t := by
  unfold tiltMean tiltIntegral
  simp_rw [show ∀ x, Real.exp (t*v x)*(c*F x) = c*(Real.exp (t*v x)*F x) by intro; ring]
  rw [integral_const_mul]
  ring

end GaussianField

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_integral {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ)
    (F : (Fin n → S) → ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  rw [← tilt_law_pi μ hv hC hvC n t,tilt_law_integral _
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n)]

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TiltReplicaCoordinate
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
section ReplicaCalculus
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_replica_coordinate {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (j : Fin n) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (fun x => F (x j)) t =
      tiltMean μ v F t := by
  have := tilt_law_probability μ hv hC hvC t
  rw [tilt_replica_integral μ hv hC hvC,← tilt_law_integral μ hv hC hvC t]
  have he := measurePreserving_eval (fun _ : Fin n => tiltLaw μ v t) j
  conv_rhs => rw [← he.map_eq,integral_map he.measurable.aemeasurable hF.aestronglyMeasurable]

lemma tilt_mean_sum {ι : Type*} (s : Finset ι) {v : S → ℝ} {F : ι → S → ℝ}
    (hv : Measurable v) (hF : ∀ i ∈ s, Measurable (F i))
    {C : ℝ} {D : ι → ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ i ∈ s, ∀ x, |F i x| ≤ D i) (t : ℝ) :
    tiltMean μ v (fun x => ∑ i ∈ s, F i x) t = ∑ i ∈ s, tiltMean μ v (F i) t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [← tilt_law_integral μ hv hC hvC t]
  exact integral_finsetSum s fun i hi => Integrable.of_bound (hF i hi).aestronglyMeasurable
    (D i) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD i hi x)

lemma tilt_replica_sum {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D)
    (n : ℕ) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (replicaPotential F n) t =
      n * tiltMean μ v F t := by
  change tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n)
    (fun x => ∑ i, F (x i)) t = _
  rw [tilt_mean_sum (Measure.pi fun _ : Fin n => μ) Finset.univ
    (F := fun i (x : Fin n → S) => F (x i)) (replicaPotential_measurable hv n)
    (fun i _ => hF.comp (measurable_pi_apply i)) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n) (fun i _ x => hFD (x i))]
  simp_rw [tilt_replica_coordinate μ hv hF hC hvC]
  simp

lemma tilt_replica_new_product {n : ℕ} {v F : S → ℝ} {G : (Fin n → S) → ℝ}
    (hv : Measurable v) (hF : Measurable F) (hG : Measurable G)
    {C D B : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C)
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin (n+1) => μ) (replicaPotential v (n+1))
      (fun x => F (x 0) * G (fun j => x j.succ)) t =
      tiltMean μ v F t * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) G t := by
  have := tilt_law_probability μ hv hC hvC t
  simp_rw [tilt_replica_integral μ hv hC hvC]
  rw [← tilt_law_integral μ hv hC hvC t]
  let ν := tiltLaw μ v t
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0) * G (fun j => x j.succ))]
  change (∫ p : S × (Fin n → S), F ((Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) 0) *
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

end ReplicaCalculus

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

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereIsometryMap
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

section RotationCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma skewFlow_apply (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) (x : E) :
    skewFlow A hA t x = NormedSpace.exp (t • A) x := rfl

lemma skewFlow_zero (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (x : E) :
    skewFlow A hA 0 x = x := by simp [skewFlow_apply]

lemma skewFlow_deriv (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (t : ℝ) (x : E) :
    HasDerivAt (fun u => skewFlow A hA u x) (A (skewFlow A hA t x)) t := by
  simpa only [skewFlow_apply,mul_apply_eq_comp,map_zero,
    add_zero] using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t x)

variable [MeasurableSpace E] [BorelSpace E]

lemma integrable_of_continuous_sphere_support (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) {f : E → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (hR.mono fun x hx =>
    hC x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

lemma invariant_skew_integral_zero (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (A : E →L[ℝ] E) (hA : A ∈ skewAdjoint (E →L[ℝ] E))
    (hμ : ∀ t, MeasurePreserving (skewFlow A hA t) μ μ) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x (A x) ∂μ = 0 := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hDf (t : ℝ) : Continuous (fun x => fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x))) :=
    ((hf.continuous_fderiv (by norm_num)).comp (skewFlow A hA t).continuous).clm_apply
      (A.continuous.comp (skewFlow A hA t).continuous)
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (x₀ := (0:ℝ))
    (F := fun t x => f (skewFlow A hA t x))
    (F' := fun t x => fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x)))
    (bound := fun _ => max C 0 * (‖A‖ * R)) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hf.continuous.comp (skewFlow A hA t).continuous).aestronglyMeasurable)
    (integrable_of_continuous_sphere_support μ hR (hf.continuous.comp (skewFlow A hA 0).continuous))
    ((hDf 0).aestronglyMeasurable) (hR.mono fun x hx t _ => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ =>
      (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (skewFlow_deriv A hA t x))).2
  · have hconst (t : ℝ) : (∫ x, f (skewFlow A hA t x) ∂μ) = ∫ x, f x ∂μ :=
      (hμ t).integral_comp (skewFlow A hA t).toHomeomorph.measurableEmbedding f
    have hc : HasDerivAt (fun t : ℝ => ∫ x, f (skewFlow A hA t x) ∂μ) 0 0 := by
      simp_rw [hconst]
      exact hasDerivAt_const _ _
    simpa only [skewFlow_zero] using hder.unique hc
  · have hb : ‖fderiv ℝ f (skewFlow A hA t x)‖ ≤ max C 0 :=
      (hC _ (by simpa only [Metric.mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map] using hx)).trans (le_max_left _ _)
    calc
      ‖fderiv ℝ f (skewFlow A hA t x) (A (skewFlow A hA t x))‖ ≤
          ‖fderiv ℝ f (skewFlow A hA t x)‖ * ‖A (skewFlow A hA t x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max C 0 * (‖A‖ * R) := mul_le_mul hb
        ((A.le_opNorm _).trans (by rw [LinearIsometryEquiv.norm_map]; gcongr)) (norm_nonneg _) (le_max_right _ _)

omit [MeasurableSpace E] [BorelSpace E] in
lemma planeSkew_mem (a y : E) : planeSkew a y ∈ skewAdjoint (E →L[ℝ] E) := by
  rw [skewAdjoint.mem_iff,planeSkew,star_sub,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne,InnerProductSpace.adjoint_rankOne]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma planeSkew_apply (a y x : E) : planeSkew a y x = inner ℝ y x • a - inner ℝ a x • y := by
  simp [planeSkew,InnerProductSpace.rankOne_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_product_deriv {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a y x : E) :
    fderiv ℝ (fun z => inner ℝ a z * f z) x (planeSkew a y x) =
      inner ℝ a (planeSkew a y x) * f x + inner ℝ a x * fderiv ℝ f x (planeSkew a y x) := by
  have hh := ((innerSL ℝ a).hasFDerivAt.mul (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have hh' : fderiv ℝ (fun z => inner ℝ a z * f z) x =
      (inner ℝ a x) • fderiv ℝ f x + f x • (innerSL ℝ a) := by
    simpa only [Pi.mul_def,coe_innerSL_apply,innerSL_apply_apply] using hh
  rw [hh']
  simp [mul_comm,add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sum_planeSkew (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x y : E) :
    ∑ i, inner ℝ (b i) x • planeSkew (b i) y x =
      inner ℝ y x • x - (‖x‖^2) • y := by
  have hn : ∑ i, (inner ℝ (b i) x)^2 = ‖x‖^2 := by
    simpa only [real_inner_comm x,pow_two,real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  simp_rw [planeSkew_apply,smul_sub,smul_smul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = ∑ i, inner ℝ y x • (inner ℝ (b i) x • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul,mul_comm]
      _ = _ := by rw [← Finset.smul_sum,b.sum_repr' x]
  · rw [← Finset.sum_smul,← hn]
    simp only [pow_two]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sum_planeSkew_divergence (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x y : E) :
    ∑ i, inner ℝ (b i) (planeSkew (b i) y x) = (Fintype.card ι - 1 : ℝ) * inner ℝ y x := by
  simp_rw [planeSkew_apply,inner_sub_right,inner_smul_right,b.inner_eq_one,mul_one]
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hb : (∑ i, inner ℝ (b i) x * inner ℝ (b i) y) = inner ℝ y x := by
    calc
      _ = ∑ i, inner ℝ y (b i) * inner ℝ (b i) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm y (b i),mul_comm]
      _ = _ := b.sum_inner_mul_inner y x
  rw [hb]
  ring

lemma invariant_tangent_integral (μ : Measure E) [IsFiniteMeasure μ] {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) (hμ : ∀ e : E ≃ₗᵢ[ℝ] E, MeasurePreserving e μ μ)
    (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ E) (y : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ x, fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) ∂μ =
      ∫ x, (Fintype.card ι - 1 : ℝ) * inner ℝ y x * f x ∂μ := by
  let F : ι → E → ℝ := fun i x => inner ℝ (b i) x * f x
  have hF (i) : ContDiff ℝ 1 (F i) := (innerSL ℝ (b i)).contDiff.mul hf
  have hI (i) : Integrable (fun x => fderiv ℝ (F i) x (planeSkew (b i) y x)) μ :=
    integrable_of_continuous_sphere_support μ hR
      (((hF i).continuous_fderiv (by norm_num)).clm_apply (planeSkew (b i) y).continuous)
  have hzero (i) := invariant_skew_integral_zero μ hR (planeSkew (b i) y) (planeSkew_mem _ _)
    (fun t => hμ (skewFlow _ (planeSkew_mem _ _) t)) (hF i)
  have halg (x) : (∑ i, fderiv ℝ (F i) x (planeSkew (b i) y x)) =
      (Fintype.card ι - 1 : ℝ) * inner ℝ y x * f x -
        fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) := by
    simp_rw [F,rotation_product_deriv hf,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,sum_planeSkew_divergence]
    have hh : (∑ i, inner ℝ (b i) x * fderiv ℝ f x (planeSkew (b i) y x)) =
        fderiv ℝ f x (inner ℝ y x • x - (‖x‖^2) • y) := by
      rw [← sum_planeSkew ι b x y,map_sum]
      simp only [map_smul,smul_eq_mul]
    rw [hh,map_sub,map_sub]
    ring
  have hi₁ := integrable_of_continuous_sphere_support μ hR
    (show Continuous (fun x => (Fintype.card ι - 1 : ℝ)*inner ℝ y x*f x) by fun_prop)
  have hi₂ := integrable_of_continuous_sphere_support μ hR
    (show Continuous (fun x => fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x)) from
      (hf.continuous_fderiv (by norm_num)).clm_apply (by fun_prop))
  have he : (∫ x, (Fintype.card ι - 1 : ℝ)*inner ℝ y x*f x ∂μ) -
      (∫ x, fderiv ℝ f x ((‖x‖^2) • y - inner ℝ y x • x) ∂μ) = 0 := by
    rw [← integral_sub hi₁ hi₂]
    simp_rw [← halg]
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp only [hzero,Finset.sum_const_zero]
  linarith

end RotationCalculus

open Matrix
open scoped RealInnerProductSpace MatrixOrder

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

lemma replicaMean_bound {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hG : Measurable G) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hHA : ∀ x, |H x| ≤ A) (hGD : ∀ x, |G x| ≤ D) : |gibbsReplicaMean μ H n G| ≤ D :=
  tilt_mean_bound _ (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) hD (replicaPotential_bound hHA n) hGD 1

lemma replicaMean_sum {ι : Type*} (t : Finset ι) {H : S → ℝ} {n : ℕ}
    {G : ι → (Fin n → S) → ℝ} (hH : Measurable H)
    (hG : ∀ i ∈ t, Measurable (G i)) {A : ℝ} {D : ι → ℝ}
    (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A)
    (hGD : ∀ i ∈ t, ∀ x, |G i x| ≤ D i) :
    gibbsReplicaMean μ H n (fun x => ∑ i ∈ t, G i x) = ∑ i ∈ t, gibbsReplicaMean μ H n (G i) :=
  tilt_mean_sum _ t (replicaPotential_measurable hH n) hG
    (mul_nonneg (Nat.cast_nonneg n) hA) (replicaPotential_bound hHA n) hGD 1

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

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma measurable_tiltMean_param {Ω : Type*} [MeasurableSpace Ω] {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => tiltMean μ (H ω) (Y ω) 1) := by
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
  exact ((hH.exp.mul hY).stronglyMeasurable.integral_prod_right'.measurable).div
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_replicaMean_param {Ω : Type*} [MeasurableSpace Ω]
    {H : Ω → S → ℝ} {n : ℕ} {Y : Ω → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) :
    Measurable (fun ω => gibbsReplicaMean μ (H ω) n (Y ω)) := by
  apply measurable_tiltMean_param _ _ hY
  change Measurable (fun p : Ω×(Fin n → S) => ∑ i, H p.1 (p.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

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

lemma gibbsReplicaMean_bound_of_integrable {H : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hG : Measurable G) {D : ℝ}
    (hi : Integrable (fun x => Real.exp (H x)) μ) (hGD : ∀ x, |G x| ≤ D) :
    |gibbsReplicaMean μ H n G| ≤ D :=
  tiltMean_bound_of_integrable _ (replicaPotential_measurable hH n) hG
    (replica_exp_integrable μ (by simpa only [one_mul] using hi) n) hGD

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

lemma kernel_replicaMean_bounded_integrable (P : Measure A) [IsFiniteMeasure P]
    {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ a x, |G a x| ≤ B) :
    Integrable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) P := by
  apply Integrable.of_bound (kernel_replicaMean_measurable κ hH hG).aestronglyMeasurable B
  exact ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin n => κ a)
      (replicaPotential_measurable hH.of_uncurry_left n) hG.of_uncurry_left hB (hGB a)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
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

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end

end

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

lemma ambientTensorFeature_inner (N p : ℕ) (x y : Spin N) :
    inner ℝ (ambientTensorFeature N p x) (ambientTensorFeature N p y) = inner ℝ x y ^ p := by
  change (∑ i : SpinTensorIndex N p, (∏ j, y (i j))*(∏ j, x (i j))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (i : Fin N) => y i*x i)]
  change (∏ _ : Fin p, inner ℝ x y)=inner ℝ x y^p
  simp

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

lemma ambientBulkFeature_inner (N : ℕ) (v : ℕ→ℝ) (x y : Spin N) :
    inner ℝ (ambientBulkFeature N v x) (ambientBulkFeature N v y)=
      ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ x y^(j.val+1) := by
  change (∑ i : EnrichedIndex N N bulkDegree,
    ambientBulkFeature N v y i*ambientBulkFeature N v x i)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [ambientBulkFeature,mul_zero,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ambientTensorFeature_inner N (j.val+1) x y]
  change (∑ i, bulkAmplitude N v j*ambientTensorFeature N _ y i*
    (bulkAmplitude N v j*ambientTensorFeature N _ x i)) =
    bulkAmplitude N v j^2*(∑ i, ambientTensorFeature N _ y i*ambientTensorFeature N _ x i)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by dsimp [bulkDegree]; ring

lemma ambientBulkFeature_deriv_inner (N : ℕ) (v : ℕ→ℝ) (x y z : Spin N) :
    inner ℝ (fderiv ℝ (ambientBulkFeature N v) x z) (ambientBulkFeature N v y)=
      bulkCovarianceDerivative N v (inner ℝ x y)*inner ℝ z y := by
  have hd := ((innerSL ℝ (ambientBulkFeature N v y)).hasFDerivAt.comp x
    ((ambientBulkFeature_contDiff N v).differentiable (by norm_num) x).hasFDerivAt).fderiv
  have he : (fun x => inner ℝ (ambientBulkFeature N v y) (ambientBulkFeature N v x))=
      (fun x => ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ y x^(j.val+1)) := by
    funext x; exact ambientBulkFeature_inner N v y x
  have hh : HasFDerivAt (fun x : Spin N => ∑ j : Fin N, bulkAmplitude N v j^2*inner ℝ y x^(j.val+1))
      (∑ j : Fin N, (bulkAmplitude N v j^2*((j.val+1:ℕ):ℝ)*inner ℝ y x^j.val) • innerSL ℝ y) x := by
    have ht (j : Fin N) : HasFDerivAt (fun x : Spin N => bulkAmplitude N v j^2*inner ℝ y x^(j.val+1))
        ((bulkAmplitude N v j^2*((j.val+1:ℕ):ℝ)*inner ℝ y x^j.val) • innerSL ℝ y) x := by
      simpa only [Nat.add_sub_cancel,nsmul_eq_mul,smul_smul,smul_eq_mul,coe_innerSL_apply,mul_assoc] using
        (((innerSL ℝ y).hasFDerivAt (x:=x)).pow (j.val+1)).const_mul (bulkAmplitude N v j^2)
    exact HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => ht j)
  simp only [Function.comp_def,coe_innerSL_apply] at hd
  rw [he,hh.fderiv] at hd
  have hx := congrArg (fun L : Spin N→L[ℝ]ℝ => L z) hd
  simpa only [sum_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,coe_innerSL_apply,bulkCovarianceDerivative,Finset.sum_mul,
    real_inner_comm y x,real_inner_comm y z,real_inner_comm (ambientBulkFeature N v y),Nat.cast_add,Nat.cast_one] using hx.symm

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

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkFreshRestore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma bulkSeparateLast_preserving (N M : ℕ) :
    MeasurePreserving (bulkSeparateLast N M) (bulkDisorderLaw N (M+1))
      ((bulkDisorderLaw N M).prod (stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
  let ρ : Measure (Fin N→ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let R := finitePatternRowsLaw N M
  let G := stdGaussian (EuclideanSpace ℝ (Fin N))
  let B := stdGaussian (BulkMark N)
  have hrow : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N)) ρ G :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hp := (((MeasurePreserving.id R).prod hrow).comp
    (Measure.measurePreserving_swap (μ:=ρ) (ν:=R))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => ρ) (Fin.last M))
  have hr : MeasurePreserving (fun a : ((Fin M→Fin N→ℝ)×EuclideanSpace ℝ (Fin N))×BulkMark N =>
      ((a.1.1,a.2),a.1.2)) ((R.prod G).prod B) ((R.prod B).prod G) :=
    (measurePreserving_prodAssoc R B G).symm.comp
      (((MeasurePreserving.id R).prod (Measure.measurePreserving_swap (μ:=G) (ν:=B))).comp
        (measurePreserving_prodAssoc R G B))
  convert hr.comp (hp.prod (MeasurePreserving.id B)) using 1
  · funext a
    simp only [bulkSeparateLast,Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply]
    apply Prod.ext
    · apply Prod.ext
      · funext i j; simp [Fin.init]
      · rfl
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_last (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder N (M+1)) (x : NormalizedSpin N) :
    bulkHamiltonian N (M+1) f v a.1 a.2 x =
      bulkHamiltonian N M f v (bulkSeparateLast N M a).1.1 (bulkSeparateLast N M a).1.2 x+
        f (inner ℝ x.val (bulkSeparateLast N M a).2) := by
  unfold bulkHamiltonian normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  simp only [bulkSeparateLast,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  ring

lemma bulkPermutePatterns_preserving (N M : ℕ) (e : Equiv.Perm (Fin M)) :
    MeasurePreserving (bulkPermutePatterns N M e) (bulkDisorderLaw N M) (bulkDisorderLaw N M) := by
  have h := (measurePreserving_piCongrLeft
    (fun _ : Fin M => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) e.symm).prod
    (MeasurePreserving.id (stdGaussian (BulkMark N)))
  convert h using 1
  · funext a
    apply Prod.ext
    · funext i
      have he := MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin M => Fin N→ℝ) e.symm a.1 (e i)
      change a.1 (e i) = (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Fin N→ℝ) e.symm) a.1 i
      simpa only [Equiv.symm_apply_apply] using he.symm
    · rfl
  · rfl
  · rfl

lemma bulkHamiltonian_permute (N M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (e : Equiv.Perm (Fin M)) (a : BulkDisorder N M) :
    bulkHamiltonian N M f v (bulkPermutePatterns N M e a).1 (bulkPermutePatterns N M e a).2 =
      bulkHamiltonian N M f v a.1 a.2 := by
  funext x
  unfold bulkHamiltonian normalizedPatternEnergy bulkPermutePatterns
  congr 1
  exact Equiv.sum_comp e (fun j => f (∑ i, a.1 j i*x.val i))

lemma bulkReplicaMean_permute (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (e : Equiv.Perm (Fin M))
    (F : BulkDisorder (n+1) M → (Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n M f v r (fun a => F (bulkPermutePatterns (n+1) M e a)) =
      bulkReplicaMean n M f v r F := by
  have hm := kernel_replicaMean_measurable (bulkSpinKernel n M)
    (H:=fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (bulkHamiltonian_continuous (n+1) M f v).measurable hF
  have h := integral_map (μ:=bulkDisorderLaw (n+1) M) (bulkPermutePatterns_preserving (n+1) M e).measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [(bulkPermutePatterns_preserving (n+1) M e).map_eq] at h
  change (∫ a, gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a) ∂bulkDisorderLaw (n+1) M) = _ at h
  unfold bulkReplicaMean
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    change gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r _ =
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v (bulkPermutePatterns (n+1) M e a).1 (bulkPermutePatterns (n+1) M e a).2) r _
    rw [bulkHamiltonian_permute]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedGibbsDerivative
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

lemma bounded_gibbs_integral_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltIntegral μ (H u) (F u) 1)
      (∫ x, Real.exp (H t x) * (H' t x * F t x + F' t x) ∂μ) t := by
  simp only [tiltIntegral, one_mul]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u x => Real.exp (H u x)*F u x)
    (s := univ) (bound := fun _ => Real.exp A * (B*C+D))
    (F' := fun u x => Real.exp (H u x) * (H' u x * F u x+F' u x))
    (Filter.univ_mem) (Eventually.of_forall fun u =>
      ((hH.comp (measurable_const.prodMk measurable_id)).exp.mul
        (hF.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (by
      simpa only [one_mul, Function.comp_def, Function.uncurry_def, id_eq, Pi.mul_apply] using tilt_integrable μ
        (hH.comp (measurable_const.prodMk measurable_id))
        (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA t) (hFC t) 1)
    (by fun_prop) (ae_of_all _ fun x u _ => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm (Real.exp (H u x)), mul_comm (Real.exp A)]
    apply mul_le_mul _ (Real.exp_le_exp.mpr ((le_abs_self _).trans (hHA u x)))
      (Real.exp_pos _).le (add_nonneg (mul_nonneg hB hC) hD)
    exact (abs_add_le _ _).trans (add_le_add (by
      rw [abs_mul]; exact mul_le_mul (hHB u x) (hFC u x) (abs_nonneg _) hB) (hFD u x))
  · convert! ((hdH u x).exp.mul (hdF u x)) using 1
    all_goals try with_reducible_and_instances rfl
    ring

lemma bounded_gibbs_mean_deriv
    {H H' F F' : ℝ → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ t x, |H t x| ≤ A) (hHB : ∀ t x, |H' t x| ≤ B)
    (hFC : ∀ t x, |F t x| ≤ C) (hFD : ∀ t x, |F' t x| ≤ D)
    (hdH : ∀ t x, HasDerivAt (fun u => H u x) (H' t x) t)
    (hdF : ∀ t x, HasDerivAt (fun u => F u x) (F' t x) t) (t : ℝ) :
    HasDerivAt (fun u => tiltMean μ (H u) (F u) 1)
      (tiltMean μ (H t) (fun x => H' t x * F t x+F' t x) 1 -
        tiltMean μ (H t) (F t) 1 * tiltMean μ (H t) (H' t) 1) t := by
  have hnum := bounded_gibbs_integral_deriv μ hH hH' hF hF' hA hB hC hD
    hHA hHB hFC hFD hdH hdF t
  have hden := bounded_gibbs_integral_deriv μ hH hH' (F := fun _ _ => 1)
    (F' := fun _ _ => 0) (C := 1) (D := 0) measurable_const measurable_const hA hB (by norm_num)
    (by norm_num) hHA hHB (by simp) (by simp) hdH (by intro t x; exact hasDerivAt_const _ _) t
  simp only [mul_one, add_zero, tiltIntegral, one_mul] at hden
  have hp := (tilt_partition_pos μ (hH.comp (measurable_const.prodMk measurable_id))
    hA (hHA t) 1).ne'
  have hp' : (∫ x, Real.exp (H t x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition, one_mul, Function.comp_def, Function.uncurry_def, id_eq] using hp
  convert! hnum.div hden hp' using 1
  · simp only [tiltMean, tiltPartition, one_mul, Pi.div_def]
  · simp only [tiltMean, tiltIntegral, tiltPartition, one_mul]
    field_simp [hp']

lemma bounded_gaussian_gibbs_coordinate_ibp {n : ℕ} (i : Fin (n+1))
    {H H' F F' : (Fin (n+1) → ℝ) → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * tiltMean μ (H g) (F g) 1 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, tiltMean μ (H g) (fun x => H' g x*F g x+F' g x) 1 -
        tiltMean μ (H g) (F g) 1 * tiltMean μ (H g) (H' g) 1
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hm := measurable_tiltMean_param μ hH hF
  have hmm := measurable_tiltMean_param μ (Y := fun g x => H' g x*F g x+F' g x) hH ((hH'.mul hF).add hF')
  have hm' := measurable_tiltMean_param μ hH hH'
  have hb (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hF.comp (measurable_const.prodMk measurable_id)) hA hC (hHA g) (hFC g) 1
  have hb' (g) := tilt_mean_bound μ
    (hH.comp (measurable_const.prodMk measurable_id))
    (hH'.comp (measurable_const.prodMk measurable_id)) hA hB (hHA g) (hHB g) 1
  apply gaussian_pi_coordinate_integrationByParts n i hm (hmm.sub (hm.mul hm'))
    (C := C) (B := 2*B*C+D) hb
  · intro g
    have hab (x) : |H' g x*F g x+F' g x| ≤ B*C+D :=
      (abs_add_le _ _).trans (add_le_add (by
        rw [abs_mul]; exact mul_le_mul (hHB g x) (hFC g x) (abs_nonneg _) hB) (hFD g x))
    have hj := tilt_mean_bound μ
      (hH.comp (measurable_const.prodMk measurable_id))
      (((hH'.mul hF).add hF').comp (measurable_const.prodMk measurable_id))
      hA (by positivity) (hHA g) hab 1
    exact (abs_sub _ _).trans (by
      simp only [Pi.mul_apply, abs_mul]
      have hp := mul_le_mul (hb g) (hb' g) (abs_nonneg _) hC
      simp only [Function.comp_def, Function.uncurry_def, id_eq, Pi.add_apply, Pi.mul_apply] at hj hp
      nlinarith)
  · intro g t
    have he : Measurable (fun p : ℝ×S => ((i.insertNth p.1 g : Fin (n+1) → ℝ),p.2)) := by
      fun_prop
    exact bounded_gibbs_mean_deriv μ
      (H := fun t x => H (i.insertNth t g) x)
      (H' := fun t x => H' (i.insertNth t g) x)
      (F := fun t x => F (i.insertNth t g) x)
      (F' := fun t x => F' (i.insertNth t g) x)
      (hH.comp he) (hH'.comp he) (hF.comp he) (hF'.comp he)
      hA hB hC hD (fun u => hHA _) (fun u => hHB _) (fun u => hFC _) (fun u => hFD _)
      (hdH g) (hdF g) t

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_NonlinearReplicaIBP
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

lemma bounded_gaussian_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1))
    {H H' : (Fin (m+1) → ℝ) → S → ℝ}
    {F F' : (Fin (m+1) → ℝ) → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hH' : Measurable (Function.uncurry H'))
    (hF : Measurable (Function.uncurry F)) (hF' : Measurable (Function.uncurry F'))
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHA : ∀ g x, |H g x| ≤ A) (hHB : ∀ g x, |H' g x| ≤ B)
    (hFC : ∀ g x, |F g x| ≤ C) (hFD : ∀ g x, |F' g x| ≤ D)
    (hdH : ∀ g t x, HasDerivAt (fun u => H (i.insertNth u g) x) (H' (i.insertNth t g) x) t)
    (hdF : ∀ g t x, HasDerivAt (fun u => F (i.insertNth u g) x) (F' (i.insertNth t g) x) t) :
    (∫ g, g i * gibbsReplicaMean μ (H g) n (F g)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => replicaPotential (H' g) n x*F g x+F' g x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => H' g (x 0)*F g (fun j => x j.succ))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hr (J : (Fin (m+1) → ℝ) → S → ℝ)
      (hJ : Measurable (Function.uncurry J)) :
      Measurable (Function.uncurry (fun g => replicaPotential (J g) n)) := by
    change Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => ∑ j : Fin n, J p.1 (p.2 j))
    exact Finset.measurable_sum _ fun j _ => hJ.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have he := bounded_gaussian_gibbs_coordinate_ibp (Measure.pi (fun _ : Fin n => μ)) i
    (hr H hH) (hr H' hH') hF hF' (by positivity) (by positivity) hC hD
    (fun g => replicaPotential_bound (hHA g) n)
    (fun g => replicaPotential_bound (hHB g) n) hFC hFD
    (fun g t x => HasDerivAt.fun_sum fun j _ => hdH g t (x j)) hdF
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  have hm : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  have hm' : Measurable (H' g) := hH'.comp (measurable_const.prodMk measurable_id)
  have fm : Measurable (F g) := hF.comp (measurable_const.prodMk measurable_id)
  rw [tilt_replica_sum μ hm hm' hA (hHA g) (hHB g) n 1]
  simp only [gibbsReplicaMean]
  rw [tilt_replica_new_product μ hm hm' fm hA (hHA g) (hHB g) (hFC g) 1]
  change _ - _ * ((n:ℝ)*_) = _ - (n:ℝ)*(_*_)
  ring

lemma nonlinear_pattern_replica_coordinate_ibp {m n : ℕ} (i : Fin (m+1)) (j : Fin n)
    (f : Jet3) {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {U : (Fin n → S) → ℝ}
    (hv : ∀ l, Measurable (v l)) (hh : Measurable h) (hU : Measurable U)
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ l x, |v l x| ≤ C) (hUD : ∀ x, |U x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    (∫ g, g i*gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*U x)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
        (fun x => ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
          f.d2 (b g (x j))*v i (x j))*U x) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*v i (x 0)*
          (f.d1 (b g (x j.succ))*U (fun l => x l.succ)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let H' := fun g x => f.d1 (b g x)*v i x
  let F := fun g (x : Fin n → S) => f.d1 (b g (x j))*U x
  let F' := fun g (x : Fin n → S) => f.d2 (b g (x j))*v i (x j)*U x
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hb' : Measurable (fun p : (Fin (m+1) → ℝ)×(Fin n → S) => b p.1 (p.2 j)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hHm : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hH'm : Measurable (Function.uncurry H') :=
    (f.d1.continuous.measurable.comp hb).mul ((hv i).comp measurable_snd)
  have hFm : Measurable (Function.uncurry F) :=
    (f.d1.continuous.measurable.comp hb').mul (hU.comp measurable_snd)
  have hF'm : Measurable (Function.uncurry F') :=
    ((f.d2.continuous.measurable.comp hb').mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd))).mul (hU.comp measurable_snd)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have hHB (g x) : |H' g x| ≤ ‖f.d1‖*C := by
    dsimp only [H']
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i x) (abs_nonneg _) (norm_nonneg _)
  have hFC (g x) : |F g x| ≤ ‖f.d1‖*D := by
    dsimp only [F]
    rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hUD x) (abs_nonneg _) (norm_nonneg _)
  have hFD (g x) : |F' g x| ≤ ‖f.d2‖*C*D := by
    dsimp only [F']
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _)
      (abs_nonneg _) (norm_nonneg _)) (hUD _) (abs_nonneg _) (by positivity)
  have hdH (g t x) : HasDerivAt (fun s => H (i.insertNth s g) x)
      (H' (i.insertNth t g) x) t := by
    dsimp [H,H',b]
    simp_rw [gaussianField_insertNth]
    convert! ((f.has1 _).comp t (((hasDerivAt_id t).mul_const (v i x)).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g x))).const_add (h x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]
  have hdF (g t x) : HasDerivAt (fun s => F (i.insertNth s g) x)
      (F' (i.insertNth t g) x) t := by
    dsimp [F,F',b]
    simp_rw [gaussianField_insertNth]
    convert! (((f.has2 _).comp t (((hasDerivAt_id t).mul_const (v i (x j))).add_const
      (gaussianField m (fun l => v (i.succAbove l)) g (x j)))).mul_const (U x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]
  have he := bounded_gaussian_replica_coordinate_ibp μ i hHm hH'm hFm hF'm
    (by positivity) (by positivity) (by positivity) (by positivity) hHA hHB hFC hFD hdH hdF
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  funext x
  dsimp only [H', F, F', replicaPotential, b]
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NonlinearDirectionIBP
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
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma nonlinear_pattern_direction_ibp {m n : ℕ} (j : Fin n) (f : Jet3)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {w : Fin (m+1) → (Fin n → S) → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) (hw : ∀ i, Measurable (w i))
    {A C D : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhA : ∀ x, |h x| ≤ A) (hvC : ∀ i x, |v i x| ≤ C) (hwD : ∀ i x, |w i x| ≤ D) :
    let b := gaussianField (m+1) v
    let H := fun g x => h x+f.f (b g x)
    let K := fun (x : Fin n→S) y => ∑ i, w i x*v i y
    (∫ g, gibbsReplicaMean μ (H g) n
      (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) n
      (fun x => (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*K x (x l))+
        f.d2 (b g (x j))*K x (x j)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*K (fun l => x l.succ) (x 0))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let b := gaussianField (m+1) v
  let H := fun g x => h x+f.f (b g x)
  let F := fun i g (x : Fin n→S) => f.d1 (b g (x j))*w i x
  let U := fun i g (x : Fin n→S) =>
    ((∑ l, f.d1 (b g (x l))*v i (x l))*f.d1 (b g (x j))+
      f.d2 (b g (x j))*v i (x j))*w i x
  let V := fun i g (x : Fin (n+1)→S) =>
    f.d1 (b g (x 0))*v i (x 0)*(f.d1 (b g (x j.succ))*w i (fun l => x l.succ))
  have hb : Measurable (Function.uncurry b) := gaussianField_measurable hv
  have hH : Measurable (Function.uncurry H) :=
    (hh.comp measurable_snd).add (f.f.continuous.measurable.comp hb)
  have hHA (g x) : |H g x| ≤ A+‖f.f‖ :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (f.f.norm_coe_le_norm _))
  have he (r : ℕ) (i : Fin r) : Measurable
      (fun p : (Fin (m+1)→ℝ)×(Fin r→S) => b p.1 (p.2 i)) :=
    hb.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hFm (i) : Measurable (Function.uncurry (F i)) :=
    (f.d1.measurable.comp (he n j)).mul ((hw i).comp measurable_snd)
  have hUm (i) : Measurable (Function.uncurry (U i)) := by
    exact (((Finset.measurable_sum _ fun l _ => (f.d1.measurable.comp (he n l)).mul
      ((hv i).comp ((measurable_pi_apply l).comp measurable_snd))).mul
      (f.d1.measurable.comp (he n j))).add ((f.d2.measurable.comp (he n j)).mul
      ((hv i).comp ((measurable_pi_apply j).comp measurable_snd)))).mul ((hw i).comp measurable_snd)
  have hVm (i) : Measurable (Function.uncurry (V i)) := by
    exact ((f.d1.measurable.comp (he (n+1) 0)).mul
      ((hv i).comp ((measurable_pi_apply 0).comp measurable_snd))).mul
      ((f.d1.measurable.comp (he (n+1) j.succ)).mul
        ((hw i).comp ((Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ).comp measurable_snd)))
  have hFB (i g x) : |F i g x| ≤ ‖f.d1‖*D := by
    dsimp [F]; rw [abs_mul]
    exact mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i x) (abs_nonneg _) (norm_nonneg _)
  have hsB (i g) (x : Fin n→S) : |∑ l, f.d1 (b g (x l))*v i (x l)| ≤ n*(‖f.d1‖*C) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin n, ‖f.d1‖*C := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hUB (i g x) : |U i g x| ≤ ((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D := by
    dsimp only [U]; rw [abs_mul]
    apply mul_le_mul _ (hwD i x) (abs_nonneg _) (by positivity)
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]; exact mul_le_mul (hsB i g x) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul (f.d2.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _)
  have hVB (i g x) : |V i g x| ≤ (‖f.d1‖*C)*(‖f.d1‖*D) := by
    dsimp only [V]; rw [abs_mul,abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (f.d1.norm_coe_le_norm _) (hvC i _) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (f.d1.norm_coe_le_norm _) (hwD i _) (abs_nonneg _) (norm_nonneg _)) (by positivity) (by positivity)
  have hiU (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hUm i)).aestronglyMeasurable
      (((n:ℝ)*(‖f.d1‖*C)*‖f.d1‖+‖f.d2‖*C)*D)
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hUm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hUB i g)
  have hiV (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i g)) γ := by
    apply Integrable.of_bound (replicaMean_varying_measurable μ hH (hVm i)).aestronglyMeasurable
      ((‖f.d1‖*C)*(‖f.d1‖*D))
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hVm i).of_uncurry_left
        (by positivity) (by positivity) (hHA g) (hVB i g)
  have hiF (i) : Integrable (fun g => g i*gibbsReplicaMean μ (H g) n (F i g)) γ := by
    have hg : Integrable (fun g : Fin (m+1)→ℝ => g i) γ :=
      ((measurePreserving_eval (fun _ : Fin (m+1) => gaussianReal 0 1) i).integrable_comp
        measurable_id.aestronglyMeasurable).mpr
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hg.mul_bdd (replicaMean_varying_measurable μ hH (hFm i)).aestronglyMeasurable
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using replicaMean_bound μ hH.of_uncurry_left (hFm i).of_uncurry_left
          (by positivity) (by positivity) (hHA g) (hFB i g))
  have hl (g) : gibbsReplicaMean μ (H g) n (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) =
      ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) := by
    rw [show (fun x => f.d1 (b g (x j))*(∑ i, g i*w i x)) = (fun x => ∑ i, g i*F i g x) by
      funext x; simp only [Finset.mul_sum,F]; apply Finset.sum_congr rfl; intros; ring]
    rw [replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hFm i).of_uncurry_left.const_mul (g i))
      (by positivity) (hHA g) (D := fun i => |g i| *(‖f.d1‖*D)) (fun i _ x => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFB i g x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hr (g) : (∑ i, (gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))) =
      gibbsReplicaMean μ (H g) n (fun x =>
        (∑ l, f.d1 (b g (x l))*f.d1 (b g (x j))*(∑ i, w i x*v i (x l)))+
        f.d2 (b g (x j))*(∑ i, w i x*v i (x j))) -
      n*gibbsReplicaMean μ (H g) (n+1) (fun x =>
        f.d1 (b g (x 0))*f.d1 (b g (x j.succ))*(∑ i, w i (fun l => x l.succ)*v i (x 0))) := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hUm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hUB i g),
      ←replicaMean_sum μ Finset.univ hH.of_uncurry_left (fun i _ => (hVm i).of_uncurry_left)
        (by positivity) (hHA g) (fun i _ => hVB i g)]
    congr 1
    · congr 1; funext x
      simp only [U,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _)
      · apply Finset.sum_congr rfl; intros; ring
      · ring
    · congr 1; congr 1; funext x
      simp only [V,Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
  calc
    _ = ∫ g, ∑ i, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ := integral_congr_ae (ae_of_all _ hl)
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => hiF i]
      simp_rw [show ∀ i, (∫ g, g i*gibbsReplicaMean μ (H g) n (F i g) ∂γ) =
          ∫ g, gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g) ∂γ
        from fun i => nonlinear_pattern_replica_coordinate_ibp μ i j f hv hh (hw i) hA hC hD hhA hvC (hwD i)]
      rw [←integral_finsetSum Finset.univ (f := fun i g =>
        gibbsReplicaMean μ (H g) n (U i g)-n*gibbsReplicaMean μ (H g) (n+1) (V i g))
        (fun i _ => (hiU i).sub ((hiV i).const_mul n))]
      exact integral_congr_ae (ae_of_all _ hr)
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_SphericalPatternDirection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma spinOverlap_self {N : ℕ} (x : NormalizedSpin N) : spinOverlap x x = 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simp [spinOverlap,hx]

lemma spinOverlap_sum {N : ℕ} (x y : NormalizedSpin N) :
    spinOverlap x y = ∑ i, x.val i*y.val i := by
  simp [spinOverlap,PiLp.inner_apply,mul_comm]

lemma normalizedSpin_coord_bound {N : ℕ} (x : NormalizedSpin N) (i : Fin N) : |x.val i| ≤ 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simpa only [Real.norm_eq_abs,hx] using PiLp.norm_apply_le x.val i

lemma spherical_pattern_direction_ibp {n : ℕ}
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (f : Jet3) (G : ℝ →ᵇ ℝ) {h : NormalizedSpin (n+1) → ℝ}
    (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hhA : ∀ x, |h x|≤A) :
    let b := gaussianField (n+1) (fun i (x : NormalizedSpin (n+1)) => x.val i)
    let H := fun g x => h x+f.f (b g x)
    (∫ g, gibbsReplicaMean μ (H g) 2 (fun x =>
      G (spinOverlap (x 0) (x 1))*f.d1 (b g (x 0))*
        (b g (x 1)-spinOverlap (x 0) (x 1)*b g (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) 2 (fun x =>
      G (spinOverlap (x 0) (x 1))*f.d1 (b g (x 0))*f.d1 (b g (x 1))*
        (1-spinOverlap (x 0) (x 1)^2)) -
      2*gibbsReplicaMean μ (H g) 3 (fun x =>
        G (spinOverlap (x 1) (x 2))*f.d1 (b g (x 1))*f.d1 (b g (x 0))*
          (spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let v := fun i (x : NormalizedSpin (n+1)) => x.val i
  let w := fun i (x : Fin 2→NormalizedSpin (n+1)) =>
    G (spinOverlap (x 0) (x 1))*(v i (x 1)-spinOverlap (x 0) (x 1)*v i (x 0))
  have hv : ∀ i, Measurable (v i) := fun i => by dsimp [v]; fun_prop
  have hw : ∀ i, Measurable (w i) := fun i => by dsimp [w,v,spinOverlap]; fun_prop
  have hwB (i x) : |w i x| ≤ ‖G‖*2 := by
    dsimp [w]; rw [abs_mul]
    apply mul_le_mul (G.norm_coe_le_norm _) _ (abs_nonneg _) (norm_nonneg _)
    apply (abs_sub _ _).trans
    have h1 := normalizedSpin_coord_bound (x 1) i
    have h0 := normalizedSpin_coord_bound (x 0) i
    have hr := spinOverlap_abs_le (x 0) (x 1)
    dsimp [v]; rw [abs_mul]
    have := mul_le_mul hr h0 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith
  have hK (x : Fin 2→NormalizedSpin (n+1)) (y : NormalizedSpin (n+1)) :
      (∑ i, w i x*v i y) = G (spinOverlap (x 0) (x 1))*
        (spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y) := by
    simp only [w,v,spinOverlap_sum,Finset.mul_sum,Finset.sum_sub_distrib,sub_mul,mul_sub]
    congr 1 <;> (apply Finset.sum_congr rfl; intros; ring)
  have hb (g : Fin (n+1)→ℝ) (x : Fin 2→NormalizedSpin (n+1)) :
      (∑ i, g i*w i x) = G (spinOverlap (x 0) (x 1))*
        (gaussianField (n+1) v g (x 1)-spinOverlap (x 0) (x 1)*gaussianField (n+1) v g (x 0)) := by
    simp only [w,gaussianField,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
    congr 1 <;> (apply Finset.sum_congr rfl; intros; ring)
  have he := nonlinear_pattern_direction_ibp μ (0:Fin 2) f hv hh hw hA
    (by norm_num : (0:ℝ)≤1) (by positivity : 0≤‖G‖*2) hhA
    (fun i x => normalizedSpin_coord_bound x i) hwB
  dsimp only at he
  simp_rw [hK,hb] at he
  convert he using 1
  · congr 1; funext g; congr 1; funext x; ring
  · congr 1; funext g
    congr 1
    · congr 1; funext x
      simp only [Fin.sum_univ_two,spinOverlap_self]
      rw [show spinOverlap (x 1) (x 0) = spinOverlap (x 0) (x 1) from real_inner_comm _ _]
      ring
    · congr 1; congr 1; funext x
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkReplicaDominated
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma replicaMean_param_integrable_dominated {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure Ω) (r : ℕ)
    {H : Ω→S→ℝ} {F : Ω→(Fin r→S)→ℝ}
    (hH : Measurable (Function.uncurry H)) (hF : Measurable (Function.uncurry F))
    {D : Ω→ℝ} (hD : Integrable D ν) (hD0 : ∀ a,0≤D a) (hb : ∀ a x,|F a x|≤D a) :
    Integrable (fun a => gibbsReplicaMean μ (H a) r (F a)) ν := by
  apply hD.mono' (measurable_replicaMean_param μ hH hF).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_eq_abs]
    exact tiltMean_bound_general _ (replicaPotential_measurable hH.of_uncurry_left r)
      hF.of_uncurry_left (hD0 a) (hb a)

lemma bulkReplicaMean_sum_dominated (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {ι : Type*} (s : Finset ι)
    (F : ι→BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : ∀ i∈s,Measurable (Function.uncurry (F i)))
    (D : ι→BulkDisorder (n+1) M→ℝ) (hD : ∀ i∈s,Integrable (D i) (bulkDisorderLaw (n+1) M))
    (hD0 : ∀ i∈s,∀ a,0≤D i a) (hb : ∀ i∈s,∀ a x,|F i a x|≤D i a) :
    bulkReplicaMean n M f v r (fun a x => ∑ i∈s,F i a x)=
      ∑ i∈s,bulkReplicaMean n M f v r (F i) := by
  have hH := (bulkHamiltonian_continuous (n+1) M f v).measurable
  unfold bulkReplicaMean
  have he (a : BulkDisorder (n+1) M) := gibbsReplicaMean_sum_of_integrable
    (unitSphereLaw (n+1)) s (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkHamiltonian_exp_integrable n M f v a)
    (fun i hi => (hF i hi).of_uncurry_left) (fun i hi x => hb i hi a x)
  simp_rw [he]
  exact integral_finsetSum s fun i hi => replicaMean_param_integrable_dominated _ _ r hH
    (hF i hi) (hD i hi) (hD0 i hi) (hb i hi)

lemma bulkPatternSize_integrable (N M : ℕ) (j : Fin M) :
    Integrable (bulkPatternSize (N:=N) j) (bulkDisorderLaw N M) := by
  apply (integrable_finsetSum _ fun i _ => ?_)
  have hr : Integrable (fun b : Fin N→ℝ => |b i|) (Measure.pi fun _ => gaussianReal 0 1) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      measurable_id.norm.aestronglyMeasurable).mpr
        (((memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)).norm)
  have ha := ((measurePreserving_eval (fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) j).integrable_comp
    ((measurable_pi_apply i).norm.aestronglyMeasurable)).mpr hr
  exact ha.comp_fst _

lemma bulkPatternFields_bound {N M r : ℕ} (j : Fin M) (a : BulkDisorder N M)
    (x : Fin r→NormalizedSpin N) (i : Fin r) : |bulkPatternFields j a x i|≤bulkPatternSize j a := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (normalizedSpin_coord_bound (x i) t) (abs_nonneg (a.1 j t))

lemma bulkTangentPattern_measurable (N M : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M) :
    Measurable (Function.uncurry (bulkTangentPattern (N:=N) f G j)) := by
  have hc : Continuous (Function.uncurry (bulkTangentPattern (N:=N) f G j)) := by
    unfold bulkTangentPattern bulkPatternFields spinOverlap Function.uncurry
    fun_prop
  exact hc.measurable

lemma bulkTangentPattern_bound {N M : ℕ} (f : Jet3) (G : ℝ→ᵇℝ) (j : Fin M)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) :
    |bulkTangentPattern f G j a x|≤2*‖G‖*‖f.d1‖*bulkPatternSize j a := by
  have hD : 0≤bulkPatternSize j a := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hd : |bulkPatternFields j a x 1-spinOverlap (x 0) (x 1)*bulkPatternFields j a x 0|≤2*bulkPatternSize j a := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (bulkPatternFields_bound j a x 0) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [bulkPatternFields_bound j a x 1]
  unfold bulkTangentPattern
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma freshTangent_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangent N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangent N f G)) := by
    unfold freshTangent spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshTangentPair_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangentPair N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangentPair N f G)) := by
    unfold freshTangentPair spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma freshTangentTriple_measurable (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (freshTangentTriple N f G)) := by
  have hc : Continuous (Function.uncurry (freshTangentTriple N f G)) := by
    unfold freshTangentTriple spinOverlap Function.uncurry; fun_prop
  exact hc.measurable

lemma normalizedSpin_inner_bound {N : ℕ} (x : NormalizedSpin N) (b : Spin N) :
    |inner ℝ x.val b|≤‖b‖ := by
  have hx : ‖x.val‖=1 := by simp
  simpa only [hx,one_mul] using abs_real_inner_le_norm x.val b

lemma freshTangent_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshTangent N f G b x|≤2*‖G‖*‖f.d1‖*‖b‖ := by
  have hd : |inner ℝ (x 1).val b-spinOverlap (x 0) (x 1)*inner ℝ (x 0).val b|≤2*‖b‖ := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (normalizedSpin_inner_bound (x 0) b)
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [normalizedSpin_inner_bound (x 1) b]
  unfold freshTangent
  rw [abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma freshTangentPair_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 2→NormalizedSpin N) :
    |freshTangentPair N f G b x|≤2*‖G‖*‖f.d1‖^2 := by
  have hd : |1-spinOverlap (x 0) (x 1)^2|≤2 := by
    apply (abs_sub _ _).trans
    have := pow_le_pow_left₀ (abs_nonneg _) (spinOverlap_abs_le (x 0) (x 1)) 2
    simp only [abs_one,abs_pow,one_pow] at this ⊢
    linarith
  unfold freshTangentPair
  rw [abs_mul,abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _))
    (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma freshTangentTriple_bound (N : ℕ) (f : Jet3) (G : ℝ→ᵇℝ) (b : Spin N) (x : Fin 3→NormalizedSpin N) :
    |freshTangentTriple N f G b x|≤2*‖G‖*‖f.d1‖^2 := by
  have hd : |spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)|≤2 := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 1) (x 2)) (spinOverlap_abs_le (x 1) (x 0))
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [spinOverlap_abs_le (x 2) (x 0)]
  unfold freshTangentTriple
  rw [abs_mul,abs_mul,abs_mul]
  apply (mul_le_mul (mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) (f.d1.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _))
    (f.d1.norm_coe_le_norm _) (abs_nonneg _) (by positivity)) hd (abs_nonneg _) (by positivity)).trans_eq
  ring

lemma bulkFreshReplicaMean_integrable (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    Integrable (fun p : BulkDisorder (n+1) M×Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1))
        (fun x => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)) r (F p.2))
      ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) := by
  apply replicaMean_param_integrable_dominated _ _ r _ _ (hD.comp_snd _) (fun p => hD0 p.2) (fun p x => hb p.2 x)
  · exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  · exact hF.comp (measurable_fst.snd.prodMk measurable_snd)

lemma bulkReplicaMean_last_integral (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hF : Measurable (Function.uncurry F)) {D : Spin (n+1)→ℝ}
    (hD : Integrable D (stdGaussian (Spin (n+1)))) (hD0 : ∀ b,0≤D b) (hb : ∀ b x,|F b x|≤D b) :
    bulkReplicaMean n (M+1) f v r (fun a x => F (bulkSeparateLast (n+1) M a).2 x)=
      ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1))
          (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x+f (inner ℝ x.val b)) r (F b)
          ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
  let H := fun p : BulkDisorder (n+1) M×Spin (n+1) =>
    fun x : NormalizedSpin (n+1) => bulkHamiltonian (n+1) M f v p.1.1 p.1.2 x+f (inner ℝ x.val p.2)
  have hH : Measurable (Function.uncurry H) := by
    exact ((bulkHamiltonian_continuous (n+1) M f v).measurable.comp (measurable_fst.fst.prodMk measurable_snd)).add
      (f.continuous.measurable.comp (measurable_snd.subtype_val.inner measurable_fst.snd))
  have hFm : Measurable (Function.uncurry (fun p : BulkDisorder (n+1) M×Spin (n+1) => F p.2)) :=
    hF.comp (measurable_fst.snd.prodMk measurable_snd)
  have hm := measurable_replicaMean_param (unitSphereLaw (n+1)) hH hFm
  have hi := bulkFreshReplicaMean_integrable n M r f v F hF hD hD0 hb
  have he := integral_map (μ := bulkDisorderLaw (n+1) (M+1)) (bulkSeparateLast_preserving (n+1) M).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(bulkSeparateLast_preserving (n+1) M).map_eq] at he
  change (∫ a : BulkDisorder (n+1) (M+1),
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) (M+1) f v a.1 a.2) r
      (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1))=_
  calc
    _ = ∫ a : BulkDisorder (n+1) (M+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H (bulkSeparateLast (n+1) M a)) r
          (F (bulkSeparateLast (n+1) M a).2) ∂bulkDisorderLaw (n+1) (M+1) := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        have hham : bulkHamiltonian (n+1) (M+1) f v a.1 a.2 = H (bulkSeparateLast (n+1) M a) := by
          funext x
          exact bulkHamiltonian_last (n+1) M f v a x
        exact congrArg (fun h => gibbsReplicaMean (unitSphereLaw (n+1)) h r (F (bulkSeparateLast (n+1) M a).2)) hham
    _ = ∫ p : BulkDisorder (n+1) M×Spin (n+1),
        gibbsReplicaMean (unitSphereLaw (n+1)) (H p) r (F p.2)
          ∂(bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1))) := he.symm
    _ = _ := integral_prod _ hi

lemma fresh_tangent_ibp (n : ℕ) (f : Jet3) (G : ℝ→ᵇℝ)
    {h : NormalizedSpin (n+1)→ℝ} (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hb : ∀ x,|h x|≤A) :
    (∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangent (n+1) f G b) ∂stdGaussian (Spin (n+1))) =
    ∫ b : Spin (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangentPair (n+1) f G b)-
      2*gibbsReplicaMean (unitSphereLaw (n+1))
      (fun x => h x+f.f (inner ℝ x.val b)) 3 (freshTangentTriple (n+1) f G b) ∂stdGaussian (Spin (n+1)) := by
  have hH : Measurable (Function.uncurry (fun b : Spin (n+1) => fun x : NormalizedSpin (n+1) => h x+f.f (inner ℝ x.val b))) :=
    (hh.comp measurable_snd).add (f.f.measurable.comp (measurable_snd.subtype_val.inner measurable_fst))
  have h1 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangent_measurable (n+1) f G)
  have h2 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangentPair_measurable (n+1) f G)
  have h3 := measurable_replicaMean_param (unitSphereLaw (n+1)) hH (freshTangentTriple_measurable (n+1) f G)
  have h23 : AEStronglyMeasurable (fun b : Spin (n+1) =>
      gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 2 (freshTangentPair (n+1) f G b)-
      2*gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => h x+f.f (inner ℝ x.val b)) 3 (freshTangentTriple (n+1) f G b))
      (Measure.map (WithLp.toLp 2) (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    (h2.sub (h3.const_mul 2)).aestronglyMeasurable
  rw [←map_pi_eq_stdGaussian,integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h1.aestronglyMeasurable,
    integral_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable h23]
  have he := spherical_pattern_direction_ibp (unitSphereLaw (n+1)) f G hh hA hb
  unfold freshTangent freshTangentPair freshTangentTriple
  convert he using 1 <;>
    simp only [gaussianField,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,mul_comm]

lemma bulk_tangent_last_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangent (n+1) f G (bulkSeparateLast (n+1) M a).2) =
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangentPair (n+1) f G (bulkSeparateLast (n+1) M a).2)-
      2*bulkReplicaMean n (M+1) f.f v 3 (fun a => freshTangentTriple (n+1) f G (bulkSeparateLast (n+1) M a).2) := by
  have hD : Integrable (fun b : Spin (n+1) => 2*‖G‖*‖f.d1‖*‖b‖) (stdGaussian (Spin (n+1))) :=
    ((((IsGaussian.memLp_id (stdGaussian (Spin (n+1))) 2 (by simp)).norm).integrable (by norm_num))).const_mul _
  have hC : (0:ℝ)≤2*‖G‖*‖f.d1‖^2 := by positivity
  rw [bulkReplicaMean_last_integral n M 2 f.f v _ (freshTangent_measurable _ _ _) hD (fun _ => by positivity) (freshTangent_bound _ _ _),
    bulkReplicaMean_last_integral n M 2 f.f v _ (freshTangentPair_measurable _ _ _) (integrable_const _) (fun _ => hC) (freshTangentPair_bound _ _ _),
    bulkReplicaMean_last_integral n M 3 f.f v _ (freshTangentTriple_measurable _ _ _) (integrable_const _) (fun _ => hC) (freshTangentTriple_bound _ _ _)]
  let P := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 2
      (freshTangentPair (n+1) f G p.2)
  let T := fun p : BulkDisorder (n+1) M×Spin (n+1) => gibbsReplicaMean (unitSphereLaw (n+1))
    (fun x => bulkHamiltonian (n+1) M f.f v p.1.1 p.1.2 x+f.f (inner ℝ x.val p.2)) 3
      (freshTangentTriple (n+1) f G p.2)
  have hiP : Integrable P ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 2 f.f v _ (freshTangentPair_measurable _ _ _)
      (integrable_const _) (fun _ => hC) (freshTangentPair_bound _ _ _)
  have hiT : Integrable T ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
    bulkFreshReplicaMean_integrable n M 3 f.f v _ (freshTangentTriple_measurable _ _ _)
      (integrable_const _) (fun _ => hC) (freshTangentTriple_bound _ _ _)
  calc
    _ = ∫ a : BulkDisorder (n+1) M, ∫ b : Spin (n+1), P (a,b)-2*T (a,b)
        ∂stdGaussian (Spin (n+1)) ∂bulkDisorderLaw (n+1) M := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => fresh_tangent_ibp n f G
        (bulkHamiltonian_section_measurable _ _ _ _ a)
        (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ by unfold bulkFeatureBound; positivity)
        (bulkHamiltonian_bound (n+1) M f.f v a)
    _ = _ := by
      have hiPT : Integrable (fun p => P p-2*T p) ((bulkDisorderLaw (n+1) M).prod (stdGaussian (Spin (n+1)))) :=
        hiP.sub (hiT.const_mul 2)
      rw [←integral_prod _ hiPT,integral_sub hiP (hiT.const_mul 2),integral_const_mul,
        integral_prod _ hiP,integral_prod _ hiT]

lemma bulkReplicaMean_row_eq_last (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (j : Fin (M+1))
    (F : Spin (n+1)→(Fin r→NormalizedSpin (n+1))→ℝ) (hF : Measurable (Function.uncurry F)) :
    bulkReplicaMean n (M+1) f v r (fun a => F (WithLp.toLp 2 (a.1 j))) =
      bulkReplicaMean n (M+1) f v r (fun a => F (bulkSeparateLast (n+1) M a).2) := by
  classical
  have hm : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) (M+1) => F (bulkSeparateLast (n+1) M a).2)) :=
    hF.comp (((bulkSeparateLast_preserving (n+1) M).measurable.snd.comp measurable_fst).prodMk measurable_snd)
  have he := bulkReplicaMean_permute n (M+1) f v r (Equiv.swap j (Fin.last M))
    (fun a => F (bulkSeparateLast (n+1) M a).2) hm
  simpa only [bulkSeparateLast,bulkPermutePatterns,Equiv.swap_apply_right] using he

lemma bulk_tangent_row_ibp (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (j : Fin (M+1)) :
    bulkReplicaMean n (M+1) f.f v 2 (bulkTangentPattern f G j) =
      bulkReplicaMean n (M+1) f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
      2*bulkReplicaMean n (M+1) f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
  have he : (bulkTangentPattern (N:=n+1) f G j)=
    (fun a : BulkDisorder (n+1) (M+1) => freshTangent (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
    funext a x
    simp only [bulkTangentPattern,bulkPatternFields,freshTangent,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [he,bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangent_measurable _ _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangentPair_measurable _ _ _),
    bulkReplicaMean_row_eq_last _ _ _ _ _ _ _ (freshTangentTriple_measurable _ _ _)]
  exact bulk_tangent_last_ibp n M f v G

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_UnitSphereTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemSpinHAddNatOfNatSphereRealUnitSphereLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSpinHAddNatOfNatSphereLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma unitSphereAmbientLaw_norm (N : ℕ) : ∀ᵐ x ∂unitSphereAmbientLaw N, ‖x‖=1 := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_eq_fun continuous_norm.measurable measurable_const)).mpr
  exact ae_of_all _ fun x => by simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma unitSphereAmbientLaw_preserving {N : ℕ} (e : Spin N≃ₗᵢ[ℝ]Spin N) :
    MeasurePreserving e (unitSphereAmbientLaw N) (unitSphereAmbientLaw N) := by
  refine ⟨e.continuous.measurable,?_⟩
  rw [unitSphereAmbientLaw,Measure.map_map e.continuous.measurable measurable_subtype_coe]
  have he : e ∘ (fun x : NormalizedSpin N => x.val) =
      (fun x : NormalizedSpin N => x.val) ∘ sphereIsometryMap e := rfl
  rw [he,← Measure.map_map measurable_subtype_coe (sphereIsometryMap_measurable e),
    (unitSphereLaw_isometry_preserving e).map_eq]

lemma unitSphere_tangent_integral (n : ℕ) (y : Spin (n+1)) {F : Spin (n+1)→ℝ}
    (hF : ContDiff ℝ 1 F) :
    (∫ x : NormalizedSpin (n+1), fderiv ℝ F x.val (y-inner ℝ y x.val • x.val) ∂unitSphereLaw (n+1)) =
      (n:ℝ)*(∫ x : NormalizedSpin (n+1), inner ℝ y x.val*F x.val ∂unitSphereLaw (n+1)) := by
  have he := invariant_tangent_integral (unitSphereAmbientLaw (n+1))
    ((unitSphereAmbientLaw_norm (n+1)).mono fun _ h => h.le)
    (fun e => unitSphereAmbientLaw_preserving e) (Fin (n+1))
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ) y hF
  have hleft : AEStronglyMeasurable (fun x : Spin (n+1) => fderiv ℝ F x ((‖x‖^2) • y-inner ℝ y x • x))
      (unitSphereAmbientLaw (n+1)) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply (by fun_prop)).aestronglyMeasurable
  have hright : AEStronglyMeasurable (fun x : Spin (n+1) => ((Fintype.card (Fin (n+1)):ℝ)-1)*inner ℝ y x*F x)
      (unitSphereAmbientLaw (n+1)) := (by fun_prop : Continuous _).aestronglyMeasurable
  rw [unitSphereAmbientLaw,integral_map measurable_subtype_coe.aemeasurable hleft,
    integral_map measurable_subtype_coe.aemeasurable hright] at he
  have hn (x : NormalizedSpin (n+1)) : ‖x.val‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using x.property
  simpa only [hn,one_pow,one_smul,Fintype.card_fin,Nat.cast_add,Nat.cast_one,
    add_sub_cancel_right,mul_assoc,integral_const_mul] using he

lemma unitSphere_gibbs_tangent_integral (n : ℕ) (y : NormalizedSpin (n+1))
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*(∫ x : NormalizedSpin (n+1), spinOverlap y x*(G (spinOverlap y x)*Real.exp (H x.val))
      ∂unitSphereLaw (n+1)) =
    ∫ x : NormalizedSpin (n+1),
      (deriv G (spinOverlap y x)*(1-spinOverlap y x^2)+G (spinOverlap y x)*
        fderiv ℝ H x.val (y.val-spinOverlap y x • x.val))*Real.exp (H x.val) ∂unitSphereLaw (n+1) := by
  let F : Spin (n+1)→ℝ := fun x => G (inner ℝ y.val x)*Real.exp (H x)
  have hF : ContDiff ℝ 1 F := (hG.comp (innerSL ℝ y.val).contDiff).mul hH.exp
  change (n:ℝ)*(∫ x : NormalizedSpin (n+1), inner ℝ y.val x.val*F x.val ∂unitSphereLaw (n+1)) = _
  rw [← unitSphere_tangent_integral n y.val hF]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hd := (((hG.differentiable (by norm_num) (inner ℝ y.val x.val)).hasDerivAt.comp_hasFDerivAt x.val
      (innerSL ℝ y.val).hasFDerivAt).mul (hH.differentiable (by norm_num) x.val).hasFDerivAt.exp).fderiv
    change fderiv ℝ F x.val (y.val-spinOverlap y x • x.val)=_
    have he : fderiv ℝ F x.val = G (spinOverlap y x) • (Real.exp (H x.val) • fderiv ℝ H x.val)+
        Real.exp (H x.val) • (deriv G (spinOverlap y x) • innerSL ℝ y.val) := by
      simpa only [F,spinOverlap,Function.comp_def,Pi.mul_def] using hd
    rw [he]
    have hy : ‖y.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using y.property
    simp only [add_apply,smul_apply,smul_eq_mul,
      coe_innerSL_apply,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hy,one_pow,spinOverlap]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TerminalReplicaRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

section
section
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma gibbsReplicaMean_pair_integral (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (F : S×S→ℝ) (hF : Measurable F) :
    gibbsReplicaMean μ H 2 (fun x => F (x 0,x 1)) =
      ∫ x, F x ∂(tiltLaw μ H 1).prod (tiltLaw μ H 1) := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  have hp := measurePreserving_finTwoArrow (tiltLaw μ H 1)
  have he := integral_map (μ:=Measure.pi fun _ : Fin 2 => tiltLaw μ H 1)
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

end

end

lemma continuous_integrable_compact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X→ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unitSphere_gibbs_tangent_mean (n : ℕ) (y : NormalizedSpin (n+1))
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*(∫ x : NormalizedSpin (n+1), spinOverlap x y*G (spinOverlap x y)
      ∂tiltLaw (unitSphereLaw (n+1)) (fun x => H x.val) 1) =
      ∫ x : NormalizedSpin (n+1),
        deriv G (spinOverlap x y)*(1-spinOverlap x y^2)+G (spinOverlap x y)*
          fderiv ℝ H x.val (y.val-spinOverlap x y • x.val)
        ∂tiltLaw (unitSphereLaw (n+1)) (fun x => H x.val) 1 := by
  have hHc : Continuous (fun x : NormalizedSpin (n+1) => H x.val) := hH.continuous.comp continuous_subtype_val
  have hi := continuous_integrable_compact (μ:=unitSphereLaw (n+1)) (Real.continuous_exp.comp hHc)
  have hi' : Integrable (fun x : NormalizedSpin (n+1) => Real.exp (1*H x.val)) (unitSphereLaw (n+1)) := by
    simpa only [one_mul,Function.comp_def] using hi
  rw [tilt_law_integral_of_integrable _ hHc.measurable hi',
    tilt_law_integral_of_integrable _ hHc.measurable hi']
  have he := unitSphere_gibbs_tangent_integral n y hH hG
  have hr (x : NormalizedSpin (n+1)) : spinOverlap y x=spinOverlap x y := real_inner_comm _ _
  simp_rw [hr] at he
  unfold tiltMean tiltIntegral
  simp only [one_mul]
  rw [←mul_div_assoc]
  congr 1
  convert he using 1
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by ring

lemma unitSphere_gibbs_replica_tangent (n : ℕ)
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => H x.val) 2
      (fun x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) =
    gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => H x.val) 2
      (fun x => deriv G (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)+
        G (spinOverlap (x 0) (x 1))*fderiv ℝ H (x 0).val
          ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val)) := by
  let L : NormalizedSpin (n+1)×NormalizedSpin (n+1)→ℝ :=
    fun x => spinOverlap x.1 x.2*G (spinOverlap x.1 x.2)
  let R : NormalizedSpin (n+1)×NormalizedSpin (n+1)→ℝ :=
    fun x => deriv G (spinOverlap x.1 x.2)*(1-spinOverlap x.1 x.2^2)+
      G (spinOverlap x.1 x.2)*fderiv ℝ H x.1.val (x.2.val-spinOverlap x.1 x.2 • x.1.val)
  have hLc : Continuous L := by dsimp [L,spinOverlap]; fun_prop
  have hRc : Continuous R := by
    have hdG := hG.continuous_deriv (by norm_num : 1≤(1:WithTop ℕ∞))
    have hdH := hH.continuous_fderiv (by norm_num)
    dsimp [R,spinOverlap]
    fun_prop
  have hHc : Continuous (fun x : NormalizedSpin (n+1) => H x.val) := hH.continuous.comp continuous_subtype_val
  have hi := continuous_integrable_compact (μ:=unitSphereLaw (n+1)) (Real.continuous_exp.comp hHc)
  have hi' : Integrable (fun x : NormalizedSpin (n+1) => Real.exp (1*H x.val)) (unitSphereLaw (n+1)) := by
    simpa only [one_mul,Function.comp_def] using hi
  let := tilt_law_probability_of_integrable (unitSphereLaw (n+1)) hi'
  change (n:ℝ)*gibbsReplicaMean _ _ 2 (fun x => L (x 0,x 1))=gibbsReplicaMean _ _ 2 (fun x => R (x 0,x 1))
  rw [gibbsReplicaMean_pair_integral _ hHc.measurable hi L hLc.measurable,
    gibbsReplicaMean_pair_integral _ hHc.measurable hi R hRc.measurable,
    integral_prod_symm _ (continuous_integrable_compact hLc),
    integral_prod_symm _ (continuous_integrable_compact hRc),←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y => unitSphere_gibbs_tangent_mean n y hH hG

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_VectorReplicaDirectionBound
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

lemma euclideanGaussian_replica_direction_bound {I : Type} [Fintype I] {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ)
    {H : S→ℝ} {V : S→EuclideanSpace ℝ I} {W : (Fin r→S)→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C D K : ℝ} (hC : 0≤C) (hD : 0≤D) (hK : 0≤K)
    (hA : ∀ x, |H x|≤A) (hVC : ∀ x, ‖V x‖≤C) (hWD : ∀ x, ‖W x‖≤D)
    (hWK : ∀ x y, |inner ℝ (W x) (V y)|≤K) :
    |∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => inner ℝ (W x) g) ∂stdGaussian (EuclideanSpace ℝ I)|≤2*r*K := by
  let ν := Measure.pi (fun _ : Fin r => μ)
  let HH := replicaPotential H r
  let VV := fun x : Fin r→S => ∑ l, V (x l)
  have hHH : Measurable HH := replicaPotential_measurable hH r
  have hVV : Measurable VV := Finset.measurable_sum _ fun l _ => hV.comp (measurable_pi_apply l)
  have hHHA (x : Fin r→S) : |HH x| ≤ r*A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin r, A := Finset.sum_le_sum fun l _ => hA (x l)
      _ = _ := by simp
  have hVVC (x : Fin r→S) : ‖VV x‖^2≤(r*C)^2 := by
    have hb : ‖VV x‖ ≤ r*C := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _ : Fin r, C := Finset.sum_le_sum fun l _ => hVC (x l)
        _ = _ := by simp
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg r) hC)).2 hb
  have hWWD (x : Fin r→S) : ‖W x‖^2≤D^2 :=
    (sq_le_sq₀ (norm_nonneg _) hD).2 (hWD x)
  have hc (x y : Fin r→S) : |inner ℝ (W x) (VV y)| ≤ r*K := by
    dsimp only [VV]
    rw [inner_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin r, K := Finset.sum_le_sum fun l _ => hWK x (y l)
      _ = _ := by simp
  have he := euclideanGaussian_tiltMean_ibp ν hHH hVV hW hHHA hVVC hWWD
  have hham (g : EuclideanSpace ℝ I) : (fun x => HH x+inner ℝ (VV x) g)=
      replicaPotential (fun x => H x+inner ℝ (V x) g) r := by
    funext x
    simp only [HH,VV,replicaPotential,sum_inner,Finset.sum_add_distrib]
  have hl (g : EuclideanSpace ℝ I) :
      gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r (fun x => inner ℝ (W x) g)=
        tiltMean ν (fun x => HH x+inner ℝ (VV x) g) (fun x => inner ℝ (W x) g) 1 := by
    rw [hham]
    rfl
  simp_rw [hl]
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ I, (2*r*K:ℝ) ∂stdGaussian (EuclideanSpace ℝ I) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
      apply ae_of_all
      intro g
      have hm : Measurable (fun x => HH x+inner ℝ (VV x) g) := hHH.add (hVV.inner measurable_const)
      have hm1 : Measurable (fun x => inner ℝ (W x) (VV x)) := hW.inner hVV
      have hm2 : Measurable (fun x : Fin 2→(Fin r→S) => inner ℝ (W (x 1)) (VV (x 0))) :=
        (hW.comp (measurable_pi_apply 1)).inner (hVV.comp (measurable_pi_apply 0))
      have hb1 := tiltMean_bound_general ν hm hm1 (t:=1) (by positivity : 0≤(r:ℝ)*K) (fun x => hc x x)
      have hb2 : |gibbsReplicaMean ν (fun x => HH x+inner ℝ (VV x) g) 2
          (fun x => inner ℝ (W (x 1)) (VV (x 0)))|≤(r:ℝ)*K :=
        tiltMean_bound_general (Measure.pi (fun _ : Fin 2 => ν))
          (replicaPotential_measurable hm 2) hm2 (by positivity)
          (fun x => hc (x 1) (x 0))
      exact (abs_sub _ _).trans (by linarith)
    _ = _ := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkTangentError
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
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

lemma bulkTangentDirection_continuous (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    Continuous (bulkTangentDirection N v G) := by
  have hr : Continuous (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 0) (x 1)) := by
    unfold spinOverlap; fun_prop
  apply (G.continuous.comp hr).smul
  have h0 : Continuous (fun x : Fin 2→NormalizedSpin N => (x 0).val) := by fun_prop
  have h1 : Continuous (fun x : Fin 2→NormalizedSpin N => (x 1).val) := by fun_prop
  exact (((ambientBulkFeature_contDiff N v).continuous_fderiv (by norm_num)).comp h0).clm_apply
    (h1.sub (hr.smul h0))

lemma bulkTangentDirection_cross (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (x : Fin 2→NormalizedSpin N) (y : NormalizedSpin N) :
    inner ℝ (bulkTangentDirection N v G x) (bulkFeature N v y)=
      G (spinOverlap (x 0) (x 1))*bulkCovarianceDerivative N v (spinOverlap (x 0) y)*
        (spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y) := by
  unfold bulkTangentDirection
  rw [← ambientBulkFeature_eq,inner_smul_left,starRingEnd_apply,star_trivial,ambientBulkFeature_deriv_inner]
  simp only [inner_sub_left,inner_smul_left,starRingEnd_apply,star_trivial,spinOverlap]
  ring

lemma bulkTangentDirection_cross_bound (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) {C : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C)
    (x : Fin 2→NormalizedSpin N) (y : NormalizedSpin N) :
    |inner ℝ (bulkTangentDirection N v G x) (bulkFeature N v y)|≤2*‖G‖*C^2*bulkScale N^2 := by
  rw [bulkTangentDirection_cross,abs_mul,abs_mul]
  have hb : |spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y|≤2 := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul (spinOverlap_abs_le (x 0) (x 1)) (spinOverlap_abs_le (x 0) y) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith [spinOverlap_abs_le (x 1) y]
  have hc := bulkCovarianceDerivative_bound N v hC hv (spinOverlap_abs_le (x 0) y)
  calc
    _ ≤ (‖G‖*(C^2*bulkScale N^2))*2 :=
      mul_le_mul (mul_le_mul (G.norm_coe_le_norm _) hc (abs_nonneg _) (norm_nonneg _)) hb (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma bulk_tangent_perturbation_bound (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1)→ℝ) {C : ℝ} (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) :
    |∫ g, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => inner ℝ (bulkTangentDirection (n+1) v G x) g) ∂stdGaussian (BulkMark (n+1))|≤
        8*‖G‖*C^2*bulkScale (n+1)^2 := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 2→NormalizedSpin (n+1)))).bddAbove_image
    (bulkTangentDirection_continuous (n+1) v G).norm.continuousOn
  have hWD (x : Fin 2→NormalizedSpin (n+1)) : ‖bulkTangentDirection (n+1) v G x‖≤ max D 0 :=
    (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)
  have he := euclideanGaussian_replica_direction_bound (unitSphereLaw (n+1)) 2
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (bulkFeature_continuous (n+1) v).measurable
    (bulkTangentDirection_continuous (n+1) v G).measurable
    (Real.sqrt_nonneg _) (le_max_right D 0) (by positivity : 0≤2*‖G‖*C^2*bulkScale (n+1)^2)
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => le_of_eq (by simpa only [bulkFeatureBound] using bulkFeature_norm (n+1) v x))
    hWD (bulkTangentDirection_cross_bound (n+1) v G hC hv)
  apply he.trans_eq
  norm_num
  ring

lemma bulkPatternLinear_apply {N : ℕ} (a : Fin N→ℝ) (x : Spin N) :
    bulkPatternLinear a x=∑ i,a i*x i := by
  simp only [bulkPatternLinear,sum_apply,smul_apply,
    smul_eq_mul]
  rfl

lemma ambientBulkHamiltonian_eq (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x : NormalizedSpin N) :
    ambientBulkHamiltonian N M f v a g x.val=bulkHamiltonian N M f.f v a g x := by
  simp only [ambientBulkHamiltonian,bulkHamiltonian,normalizedPatternEnergy,
    bulkPatternLinear_apply,ambientBulkFeature_eq,real_inner_comm g]

lemma ambientBulkHamiltonian_contDiff (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) :
    ContDiff ℝ 1 (ambientBulkHamiltonian N M f v a g) := by
  apply (ContDiff.sum (fun j _ => (f.contDiff.of_le (by norm_num)).comp (bulkPatternLinear (a j)).contDiff)).add
  exact (innerSL ℝ g).contDiff.comp ((ambientBulkFeature_contDiff N v).of_le (by norm_num))

lemma ambientBulkHamiltonian_deriv (N M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin N→ℝ) (g : BulkMark N) (x z : Spin N) :
    fderiv ℝ (ambientBulkHamiltonian N M f v a g) x z =
      (∑ j,f.d1 (bulkPatternLinear (a j) x)*bulkPatternLinear (a j) z)+
        inner ℝ (fderiv ℝ (ambientBulkFeature N v) x z) g := by
  have hd := HasFDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin M))) =>
    (f.has1 (bulkPatternLinear (a j) x)).comp_hasFDerivAt x (bulkPatternLinear (a j)).hasFDerivAt)
  have hg := (innerSL ℝ g).hasFDerivAt.comp x
    (((ambientBulkFeature_contDiff N v).differentiable (by norm_num)) x).hasFDerivAt
  have he := (hd.add hg).fderiv
  change fderiv ℝ (ambientBulkHamiltonian N M f v a g) x z=_
  rw [show fderiv ℝ (ambientBulkHamiltonian N M f v a g) x = _ from he]
  simp only [add_apply,sum_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,coe_innerSL_apply]
  rw [real_inner_comm g]

lemma bulk_gibbs_replica_tangent (n M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (g : BulkMark (n+1))
    (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    (n:ℝ)*gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2
      (fun x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) =
    gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2
      (fun x => deriv (G : ℝ→ℝ) (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)+
        (∑ j,G (spinOverlap (x 0) (x 1))*f.d1 (∑ i,a j i*(x 0).val i)*
          ((∑ i,a j i*(x 1).val i)-spinOverlap (x 0) (x 1)*(∑ i,a j i*(x 0).val i)))+
        inner ℝ (bulkTangentDirection (n+1) v G x) g) := by
  have he := unitSphere_gibbs_replica_tangent n (ambientBulkHamiltonian_contDiff (n+1) M f v a g) hG
  simp only [ambientBulkHamiltonian_eq] at he
  rw [he]
  apply congrArg (gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a g) 2)
  funext x
  rw [ambientBulkHamiltonian_deriv]
  have hs : (∑ j,G (spinOverlap (x 0) (x 1))*
      (f.d1 (bulkPatternLinear (a j) (x 0).val)*
        bulkPatternLinear (a j) ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val))) =
      ∑ j,G (spinOverlap (x 0) (x 1))*f.d1 (∑ i,a j i*(x 0).val i)*
        ((∑ i,a j i*(x 1).val i)-spinOverlap (x 0) (x 1)*(∑ i,a j i*(x 0).val i)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_sub,map_smul,smul_eq_mul,bulkPatternLinear_apply]
    ring
  simp only [bulkTangentDirection,inner_smul_left,starRingEnd_apply,star_trivial]
  rw [mul_add,Finset.mul_sum,hs]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkAnnealedTangent
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction ContDiff

lemma bulkReplicaMean_add_dominated (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {F G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ}
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {D E : BulkDisorder (n+1) M→ℝ}
    (hD : Integrable D (bulkDisorderLaw (n+1) M)) (hE : Integrable E (bulkDisorderLaw (n+1) M))
    (hD0 : ∀ a,0≤D a) (hE0 : ∀ a,0≤E a)
    (hbF : ∀ a x,|F a x|≤D a) (hbG : ∀ a x,|G a x|≤E a) :
    bulkReplicaMean n M f v r (fun a x => F a x+G a x)=
      bulkReplicaMean n M f v r F+bulkReplicaMean n M f v r G := by
  have he (a : BulkDisorder (n+1) M) :
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (fun x => F a x+G a x)=
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (F a)+
        gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G a) := by
    let := tilt_law_probability_of_integrable (unitSphereLaw (n+1))
      (show Integrable (fun x => Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x)) (unitSphereLaw (n+1)) from
        by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v a)
    simp_rw [gibbsReplicaMean_integral_of_integrable (unitSphereLaw (n+1))
      (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkHamiltonian_exp_integrable n M f v a)]
    exact integral_add
      (Integrable.of_bound hF.of_uncurry_left.aestronglyMeasurable (D a) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbF a x))
      (Integrable.of_bound hG.of_uncurry_left.aestronglyMeasurable (E a) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbG a x))
  unfold bulkReplicaMean
  simp_rw [he]
  exact integral_add
    (replicaMean_param_integrable_dominated _ _ r (bulkHamiltonian_continuous _ _ _ _).measurable hF hD hD0 hbF)
    (replicaMean_param_integrable_dominated _ _ r (bulkHamiltonian_continuous _ _ _ _).measurable hG hE hE0 hbG)

lemma bulkTangentDirection_bounded (N : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ x,‖bulkTangentDirection N v G x‖≤D := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 2→NormalizedSpin N))).bddAbove_image
    (bulkTangentDirection_continuous N v G).norm.continuousOn
  exact ⟨max D 0,le_max_right _ _,fun x => (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)⟩

lemma bulkTangentPerturbation_measurable (N M : ℕ) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkTangentPerturbation (N:=N) (M:=M) v G)) :=
  (((bulkTangentDirection_continuous N v G).comp continuous_snd).inner continuous_fst.snd).measurable

lemma bulkTangentPerturbation_bound {N M : ℕ} (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    {D : ℝ} (hb : ∀ x,‖bulkTangentDirection N v G x‖≤D)
    (a : BulkDisorder N M) (x : Fin 2→NormalizedSpin N) :
    |bulkTangentPerturbation v G a x|≤D*‖a.2‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

lemma bulkMarkNorm_integrable (N M : ℕ) :
    Integrable (fun a : BulkDisorder N M => ‖a.2‖) (bulkDisorderLaw N M) :=
  ((((IsGaussian.memLp_id (stdGaussian (BulkMark N)) 2 (by simp)).norm).integrable (by norm_num))).comp_snd _

lemma bulkTangentPerturbation_integrable (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2 (bulkTangentPerturbation v G a)) (bulkDisorderLaw (n+1) M) := by
  obtain ⟨D,hD,hb⟩ := bulkTangentDirection_bounded (n+1) v G
  exact replicaMean_param_integrable_dominated _ _ 2 (bulkHamiltonian_continuous _ _ _ _).measurable
    (bulkTangentPerturbation_measurable _ _ _ _) ((bulkMarkNorm_integrable (n+1) M).const_mul D)
    (fun a => mul_nonneg hD (norm_nonneg _)) (bulkTangentPerturbation_bound v G hb)

lemma bulk_tangent_annealed_perturbation_bound (n M : ℕ) (f G : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    |bulkReplicaMean n M f v 2 (bulkTangentPerturbation v G)|≤8*‖G‖*C^2*bulkScale (n+1)^2 := by
  unfold bulkReplicaMean
  rw [show bulkDisorderLaw (n+1) M =
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1).prod (stdGaussian (BulkMark (n+1))) from rfl]
  rw [integral_prod _ (bulkTangentPerturbation_integrable n M f G v)]
  have hb : ∀ a : Fin M→Fin (n+1)→ℝ,
      ‖∫ b : BulkMark (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
        (bulkHamiltonian (n+1) M f v a b) 2 (bulkTangentPerturbation v G (a,b))
          ∂stdGaussian (BulkMark (n+1))‖≤8*‖G‖*C^2*bulkScale (n+1)^2 := by
    intro a
    rw [Real.norm_eq_abs]
    change |∫ b : BulkMark (n+1), gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a b) 2 (fun x => inner ℝ (bulkTangentDirection (n+1) v G x) b)
        ∂stdGaussian (BulkMark (n+1))|≤_
    exact bulk_tangent_perturbation_bound n M f G v a hC hv
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) hb)

lemma continuous_real_compact_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : X→ℝ} (hF : Continuous F) : ∃ D : ℝ,0≤D ∧ ∀ x,|F x|≤D := by
  obtain ⟨D,hD⟩ := (isCompact_univ : IsCompact (univ : Set X)).bddAbove_image hF.abs.continuousOn
  exact ⟨max D 0,le_max_right _ _,fun x => (hD (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)⟩

lemma tangentDerivTest_continuous (N : ℕ) (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    Continuous (tangentDerivTest N G) := by
  have hr : Continuous (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 0) (x 1)) := by
    unfold spinOverlap; fun_prop
  exact ((hG.continuous_deriv (by norm_num)).comp hr).mul (continuous_const.sub (hr.pow 2))

lemma bulk_tangent_row_ibp_any (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (j : Fin M) :
    bulkReplicaMean n M f.f v 2 (bulkTangentPattern f G j) =
      bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
      2*bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))) := by
  cases M with
  | zero => exact Fin.elim0 j
  | succ M => exact bulk_tangent_row_ibp n M f v G j

lemma bulk_tangent_annealed (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    |(n:ℝ)*bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1)))-
      bulkReplicaMean n M f.f v 2 (fun _ => tangentDerivTest (n+1) G)-
      ∑ j : Fin M, (bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))-
        2*bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))))|≤
      8*‖G‖*C^2*bulkScale (n+1)^2 := by
  let T := fun a : BulkDisorder (n+1) M => fun x : Fin 2→NormalizedSpin (n+1) => ∑ j,bulkTangentPattern f G j a x
  let D := fun a : BulkDisorder (n+1) M => ∑ j : Fin M,2*‖G‖*‖f.d1‖*bulkPatternSize j a
  have hT : Measurable (Function.uncurry T) := Finset.measurable_sum _ fun j _ => bulkTangentPattern_measurable _ _ _ _ j
  have hD : Integrable D (bulkDisorderLaw (n+1) M) := integrable_finsetSum _ fun j _ =>
    (bulkPatternSize_integrable (n+1) M j).const_mul (2*‖G‖*‖f.d1‖)
  have hD0 (a : BulkDisorder (n+1) M) : 0≤D a := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hbT (a : BulkDisorder (n+1) M) (x : Fin 2→NormalizedSpin (n+1)) : |T a x|≤D a :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => bulkTangentPattern_bound f G j a x)
  obtain ⟨E,hE,hbE⟩ := continuous_real_compact_bound (tangentDerivTest_continuous (n+1) G hG)
  have hEme : Measurable (Function.uncurry (fun _ : BulkDisorder (n+1) M => tangentDerivTest (n+1) G)) :=
    (tangentDerivTest_continuous (n+1) G hG).measurable.comp measurable_snd
  obtain ⟨K,hK,hbK⟩ := bulkTangentDirection_bounded (n+1) v G
  have hP := bulkTangentPerturbation_measurable (n+1) M v G
  have hbP := bulkTangentPerturbation_bound (M:=M) v G hbK
  have hiP := (bulkMarkNorm_integrable (n+1) M).const_mul K
  have he : (n:ℝ)*bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1)))=
      bulkReplicaMean n M f.f v 2 (fun a x => tangentDerivTest (n+1) G x+T a x+bulkTangentPerturbation v G a x) := by
    unfold bulkReplicaMean
    rw [←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun a => bulk_gibbs_replica_tangent n M f v a.1 a.2 G hG)
  have hET : Measurable (Function.uncurry (fun a x => tangentDerivTest (n+1) G x+T a x)) := hEme.add hT
  have hadd := bulkReplicaMean_add_dominated n M 2 f.f v hET hP
    ((integrable_const E).add hD) hiP (fun a => add_nonneg hE (hD0 a)) (fun a => mul_nonneg hK (norm_nonneg _))
    (fun a x => (abs_add_le _ _).trans (add_le_add (hbE x) (hbT a x))) hbP
  have hadd' := bulkReplicaMean_add_dominated n M 2 f.f v hEme hT (integrable_const E) hD
    (fun _ => hE) hD0 (fun _ x => hbE x) hbT
  rw [he,hadd,hadd']
  have hsum : bulkReplicaMean n M f.f v 2 T=∑ j : Fin M,bulkReplicaMean n M f.f v 2 (bulkTangentPattern f G j) :=
    bulkReplicaMean_sum_dominated n M 2 f.f v Finset.univ _
      (fun j _ => bulkTangentPattern_measurable _ _ _ _ j)
      (fun j a => 2*‖G‖*‖f.d1‖*bulkPatternSize j a)
      (fun j _ => (bulkPatternSize_integrable (n+1) M j).const_mul (2*‖G‖*‖f.d1‖))
      (fun j _ a => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _))
      (fun j _ => bulkTangentPattern_bound f G j)
  rw [hsum]
  simp_rw [bulk_tangent_row_ibp_any n M f v G]
  convert bulk_tangent_annealed_perturbation_bound n M f.f G v hC hv using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkRestorationLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma bulkReplicaMean_sum (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {ι : Type*} (s : Finset ι)
    (G : ι→BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : ∀ i∈s,Measurable (Function.uncurry (G i)))
    (D : ι→ℝ) (hD : ∀ i∈s,0≤D i) (hb : ∀ i∈s,∀ a x,|G i a x|≤D i) :
    bulkReplicaMean n M f v r (fun a x => ∑ i∈s,G i a x)=
      ∑ i∈s,bulkReplicaMean n M f v r (G i) := by
  unfold bulkReplicaMean
  have hH : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => bulkHamiltonian (n+1) M f v a.1 a.2)) :=
    (bulkHamiltonian_continuous (n+1) M f v).measurable
  have he (a : BulkDisorder (n+1) M) :
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r
        (fun x => ∑ i∈s,G i a x)=
      ∑ i∈s,gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G i a) :=
    gibbsReplicaMean_sum_of_integrable (unitSphereLaw (n+1)) s
      (show Measurable (fun x => bulkHamiltonian (n+1) M f v a.1 a.2 x) from hH.of_uncurry_left)
      (bulkHamiltonian_exp_integrable n M f v a) (fun i hi => (hG i hi).of_uncurry_left)
      (fun i hi x => hb i hi a x)
  simp_rw [he]
  exact integral_finsetSum s fun i hi => kernel_replicaMean_bounded_integrable (bulkSpinKernel n M)
    (bulkDisorderLaw (n+1) M) hH (hG i hi) (hD i hi) (hb i hi)

lemma bulkReplicaMean_const_mul (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ) (c : ℝ) :
    bulkReplicaMean n M f v r (fun a x => c*G a x)=c*bulkReplicaMean n M f v r G := by
  unfold bulkReplicaMean
  simp_rw [replicaMean_const_mul]
  exact integral_const_mul _ _

lemma bulkReplicaMean_bound (n M r : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (G : BulkDisorder (n+1) M→(Fin r→NormalizedSpin (n+1))→ℝ)
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (_hC : 0≤C) (hb : ∀ a x,|G a x|≤C) :
    |bulkReplicaMean n M f v r G|≤C := by
  have hb' : ∀ᵐ a ∂bulkDisorderLaw (n+1) M,
      ‖gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2) r (G a)‖≤C := by
    refine ae_of_all _ fun a => ?_
    rw [Real.norm_eq_abs]
    exact gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
      ((bulkHamiltonian_continuous _ _ _ _).measurable.comp (measurable_const.prodMk measurable_id))
      hG.of_uncurry_left (bulkHamiltonian_exp_integrable n M f v a) (hb a)
  simpa [bulkReplicaMean] using
    norm_integral_le_of_norm_le_const hb'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_AnnealedMarkedReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SphericalPerceptronFreeEnergy
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_marked_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : A→(Fin r→S)→ℝ}
    (hG : Measurable (Function.uncurry G)) {B : ℝ} (hGB : ∀ a x,|G a x|≤B) :
    (∫ a,G a.1 (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH)=
      ∫ a,gibbsReplicaMean (κ a) (H a) r (G a) ∂P := by
  let := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val)) :=
    hG.comp (measurable_fst.prodMk (by fun_prop))
  have hi : Integrable (fun a : A×(ℕ→S) => G a.1 (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using hGB a.1 (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  rw [kernelInfiniteReplica_prefix_integral _ a r hG.of_uncurry_left]
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r (G a)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff

lemma bulkMarkedArray_block (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :
    (∫ Q,F (compactBlock r Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
      bulkReplicaMean n M f.f v r (fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j))) := by
  change (∫ Q,F (compactBlock r Q) ∂Measure.map (bulkMarkedArray n M f K hK)
    (annealedInfiniteReplicaMeasure (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
      (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)))=_
  have hm : Measurable (fun Q : CompactArray (BulkPairRange K) => F (compactBlock r Q)) :=
    F.measurable.comp (compactBlock_continuous r).measurable
  rw [integral_map (bulkMarkedArray_measurable n M f K hK).aemeasurable hm.aestronglyMeasurable]
  unfold bulkReplicaMean
  apply annealedInfiniteReplica_marked_prefix (bulkSpinKernel n M) (bulkDisorderLaw (n+1) M)
    (bulkGibbsHamiltonian n M f.f v) (bulkGibbsHamiltonian_measurable n M f.f v)
    (ae_of_all _ (bulkHamiltonian_exp_integrable n M f.f v)) r
    (G := fun a x => F (fun i j => bulkMarkedEntry n M f K hK a (x i) (x j)))
  · apply F.measurable.comp
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    have hm : Measurable (fun p : BulkDisorder (n+1) M×(Fin r→NormalizedSpin (n+1)) => (p.2 i,p.2 j)) := by fun_prop
    exact ((bulkOverlap_measurable _).comp hm).prodMk
      (((bulkB_measurable _ _ _).comp (measurable_fst.prodMk hm)).subtype_mk)
  · intro a x
    exact F.norm_coe_le_norm _

lemma bulk_tangent_pair_sum (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (∑ j : Fin M,bulkReplicaMean n M f.f v 2 (fun a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j))))=
      (n+1:ℕ)*(∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)) := by
  have hm (j : Fin M) : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
    have hc : Continuous (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
      unfold Function.uncurry freshTangentPair spinOverlap
      fun_prop
    exact hc.measurable
  have hs := bulkReplicaMean_sum n M 2 f.f v Finset.univ
    (fun j a => freshTangentPair (n+1) f G (WithLp.toLp 2 (a.1 j)))
    (fun j _ => hm j)
    (fun _ => 2*‖G‖*‖f.d1‖^2) (by intros; positivity)
    (fun j _ a x => freshTangentPair_bound _ _ _ _ x)
  rw [←hs,bulkMarkedArray_block,←bulkReplicaMean_const_mul]
  apply congrArg (bulkReplicaMean n M f.f v 2)
  funext a x
  change (∑ j : Fin M,G (spinOverlap (x 0) (x 1))*f.d1 (inner ℝ (x 0).val (WithLp.toLp 2 (a.1 j)))*
    f.d1 (inner ℝ (x 1).val (WithLp.toLp 2 (a.1 j)))*(1-spinOverlap (x 0) (x 1)^2))=
    ((n+1:ℕ):ℝ)*(G (spinOverlap (x 0) (x 1))*bulkB (n+1) M f a.1 (x 0) (x 1)*(1-spinOverlap (x 0) (x 1)^2))
  have he (z : NormalizedSpin (n+1)) (j : Fin M) : inner ℝ z.val (WithLp.toLp 2 (a.1 j))=∑ i,a.1 j i*z.val i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  simp_rw [he]
  unfold bulkB
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  simp_rw [mul_assoc (G _)]
  rw [←Finset.mul_sum,←Finset.sum_mul]
  field_simp

lemma bulk_tangent_triple_sum (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ) (K : ℝ)
    (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K) :
    (∑ j : Fin M,bulkReplicaMean n M f.f v 3 (fun a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j))))=
      (n+1:ℕ)*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)) := by
  have hm (j : Fin M) : Measurable (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
    have hc : Continuous (Function.uncurry (fun a : BulkDisorder (n+1) M => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))) := by
      unfold Function.uncurry freshTangentTriple spinOverlap
      fun_prop
    exact hc.measurable
  have hs := bulkReplicaMean_sum n M 3 f.f v Finset.univ
    (fun j a => freshTangentTriple (n+1) f G (WithLp.toLp 2 (a.1 j)))
    (fun j _ => hm j)
    (fun _ => 2*‖G‖*‖f.d1‖^2) (by intros; positivity)
    (fun j _ a x => freshTangentTriple_bound _ _ _ _ x)
  rw [←hs,bulkMarkedArray_block,←bulkReplicaMean_const_mul]
  apply congrArg (bulkReplicaMean n M f.f v 3)
  funext a x
  change (∑ j : Fin M,G (spinOverlap (x 1) (x 2))*f.d1 (inner ℝ (x 1).val (WithLp.toLp 2 (a.1 j)))*
    f.d1 (inner ℝ (x 0).val (WithLp.toLp 2 (a.1 j)))*(spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))=
    ((n+1:ℕ):ℝ)*(G (spinOverlap (x 1) (x 2))*bulkB (n+1) M f a.1 (x 1) (x 0)*(spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))
  have he (z : NormalizedSpin (n+1)) (j : Fin M) : inner ℝ z.val (WithLp.toLp 2 (a.1 j))=∑ i,a.1 j i*z.val i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  simp_rw [he]
  unfold bulkB
  have hn : ((n+1:ℕ):ℝ)≠0 := by positivity
  simp_rw [mul_assoc (G _)]
  rw [←Finset.mul_sum,←Finset.sum_mul]
  field_simp

lemma bulk_marked_tangent_bound (n M : ℕ) (f : Jet3) (v : ℕ→ℝ) (G : ℝ→ᵇℝ)
    (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (K : ℝ) (hK : M/(n+1:ℕ)*‖f.d1‖^2≤K)
    {D : ℝ} (hD : 0≤D) (hbD : ∀ r : CompactOverlap,|deriv (G : ℝ→ℝ) r.val*(1-r.val^2)|≤D) :
    |(∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))-
        (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))+
        2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))|≤
      (‖G‖+D+8*‖G‖*C^2*bulkScale (n+1)^2)/(n+1:ℕ) := by
  have ht := bulk_tangent_annealed n M f v G hG hC hv
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,bulk_tangent_pair_sum n M f v G K hK,bulk_tangent_triple_sum n M f v G K hK] at ht
  have hr := bulkMarkedArray_block n M f v K hK 2 (markedTangentR K G)
  change (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _))=
    bulkReplicaMean n M f.f v 2 (fun _ x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) at hr
  rw [←hr] at ht
  have hdb := bulkReplicaMean_bound n M 2 f.f v (fun _ => tangentDerivTest (n+1) G)
    ((tangentDerivTest_continuous (n+1) G hG).measurable.comp measurable_snd) hD (fun _ x => hbD (bulkOverlap (x 0) (x 1)))
  have hrb : |∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw n M f v K hK : Measure _)|≤‖G‖ := by
    have hb : ∀ Q : CompactArray (BulkPairRange K),‖markedTangentR K G (compactBlock 2 Q)‖≤‖G‖ := by
      intro Q
      change |(Q 0 1).1.val*G (Q 0 1).1.val|≤‖G‖
      rw [abs_mul]
      exact (mul_le_mul (abs_le.mpr (Q 0 1).1.property) (G.norm_coe_le_norm _) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans (by simp)
    simpa [Real.norm_eq_abs,Measure.real] using norm_integral_le_of_norm_le_const (ae_of_all (bulkMarkedArrayLaw n M f v K hK : Measure _) hb)
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  rw [le_div_iff₀ hn,←abs_of_pos hn,←abs_mul]
  have halg (X Y Z W : ℝ) : (X-Y+2*Z)*(n+1:ℕ)=X+W+((n:ℝ)*X-W-((n+1:ℕ)*Y-2*((n+1:ℕ)*Z))) := by push_cast; ring
  rw [halg]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hrb hdb)) ht)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkMarkedTangentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology BoundedContinuousFunction ContDiff

lemma bulkScale_sq_div (n : ℕ) : bulkScale (n+1)^2/(n+1:ℕ)=((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  unfold bulkScale
  rw [←Real.rpow_mul_natCast hn.le]
  calc
    _ = ((n+1:ℕ):ℝ)^((3:ℝ)/8*(2:ℕ))/((n+1:ℕ):ℝ)^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [←Real.rpow_sub hn]; norm_num

lemma bulk_tangent_error_tendsto (A D C : ℝ) :
    Tendsto (fun n : ℕ => (A+D+8*A*C^2*bulkScale (n+1)^2)/(n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi := tendsto_inv_atTop_zero.comp hN
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have he (n : ℕ) : (A+D+8*A*C^2*bulkScale (n+1)^2)/(n+1:ℕ)=
      (A+D)*((n+1:ℕ):ℝ)⁻¹+8*A*C^2*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [add_div,mul_div_assoc,bulkScale_sq_div,div_eq_mul_inv]
  simp_rw [he]
  convert (hi.const_mul (A+D)).add (hp.const_mul (8*A*C^2)) using 1 <;>
    simp only [mul_zero,add_zero,Function.comp_def,neg_div]

lemma marked_tangent_continuous (K : ℝ) (G : ℝ→ᵇℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray (BulkPairRange K)) =>
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
        (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
        2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))) := by
  have hh (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (F.compContinuous ⟨compactBlock r,compactBlock_continuous r⟩)
  exact ((hh 2 (markedTangentR K G)).sub (hh 2 (markedTangentPair K G))).add
    (continuous_const.mul (hh 3 (markedTangentTriple K G)))

lemma bulk_marked_tangent_limit_oai (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ n j,|v n (j+1)|≤C)
    (K : ℝ) {s : ℕ→ℕ} (hs : StrictMono s)
    (hK : ∀ n,M (s n)/(s n+1:ℕ)*‖f.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ))
    (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0 := by
  have hc : Continuous (fun r : CompactOverlap=>deriv (G : ℝ→ℝ) r.val*(1-r.val^2)) :=
    ((hG.continuous_deriv (by norm_num)).comp continuous_subtype_val).mul
      (continuous_const.sub (continuous_subtype_val.pow 2))
  obtain ⟨D,hD,hbD⟩ := continuous_real_compact_bound hc
  have hzero : Tendsto (fun n =>
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun n => (‖G‖+D+8*‖G‖*C^2*bulkScale (s n+1)^2)/(s n+1:ℕ))
    · intro n
      simpa only [Real.norm_eq_abs] using bulk_marked_tangent_bound (s n) (M (s n)) f (v (s n)) G hG hC (hv (s n)) K (hK n) hD hbD
    · exact (bulk_tangent_error_tendsto ‖G‖ D C).comp hs.tendsto_atTop
  exact tendsto_nhds_unique ((marked_tangent_continuous K G).continuousAt.tendsto.comp hlim) hzero

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit_oai := @OAI.SphericalPerceptronFreeEnergy.bulk_marked_tangent_limit_oai
