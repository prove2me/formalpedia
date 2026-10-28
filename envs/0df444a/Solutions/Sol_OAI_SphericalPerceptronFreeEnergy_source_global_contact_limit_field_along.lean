-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.source_global_contact_limit_field_along
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:58:14.338611+00:00
-- url     : https://prove2.me/submissions/41400e88-c36c-48b4-8f1b-8c67097a9f1b

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceKernelPressure_memLp

section
-- module Solutions.OAIQ061_PF.Compat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
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

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

open TopologicalSpace

open scoped Polynomial

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
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

section
variable {V I : Type} [Countable V] [Fintype I]

lemma countableGaussianVectors_measurable : Measurable (countableGaussianVectors (V := V) (I := I)) := by
  apply Measurable.of_eval
  intro v
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  fun_prop

lemma countableGaussianVectors_law :
    countableGaussianLaw.map (countableGaussianVectors (V := V) (I := I)) =
      Measure.infinitePi (fun _ : V => stdGaussian (EuclideanSpace ℝ I)) := by
  let c : (ℕ → ℝ) → V×I → ℝ := fun g p => g (countableCoordinate p)
  have hc : Measurable c := by fun_prop
  have hl : countableGaussianLaw.map c = Measure.infinitePi (fun _ : V×I => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj countableCoordinate_injective
  let e := MeasurableEquiv.curry V I ℝ
  have he : countableGaussianVectors (V := V) (I := I) =
      ((fun f v => WithLp.toLp 2 (f v)) ∘ e) ∘ c := rfl
  have hm : Measurable (fun f : V → I → ℝ => fun v => WithLp.toLp 2 (f v)) := by fun_prop
  rw [he,← Measure.map_map (hm.comp e.measurable) hc,hl,
    ← Measure.map_map hm e.measurable]
  rw [show e = MeasurableEquiv.curry V I ℝ from rfl,Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1),
    Measure.infinitePi_map_pi _ (fun _ => (PiLp.continuous_toLp 2 _).measurable)]
  simp only [Measure.infinitePi_eq_pi,map_pi_eq_stdGaussian]

end

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
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

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

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
variable {I : Type} [Fintype I]

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

variable {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_field (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g x =
      ∑ d : Fin (n+1), ∑ i : I,
        g (countableCoordinate (indexedLeafSharedVertex n x.2 d,i))* (B d i * V x.1 i) := by
  rw [countableGaussianField,gaussianPrefixField]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    g i.val * finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val) = _
  rw [finiteGaussianRow_field (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type]
  rfl

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) =
      ∑ i : I, (∑ d : Fin (n+1), B d i^2) * V x.1 i^2 := by
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val^2) = _
  rw [finiteGaussianRow_norm (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_pow]
  rw [Finset.sum_mul]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm_le (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    {C D : ℝ} (hC : ∀ i, (∑ d, B d i^2) ≤ C) (hC0 : 0 ≤ C)
    (hD : ∀ x, (∑ i, V x i^2) ≤ D) (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) ≤ C*D := by
  rw [indexedGaussianRow_norm]
  calc
    _ ≤ ∑ i, C*V x.1 i^2 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)
    _ = C*∑ i, V x.1 i^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ C*D := mul_le_mul_of_nonneg_left (hD x.1) hC0

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedDiagonalField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

lemma sourceEnrichedFeature_norm (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (x : NormalizedSpin N) : ‖sourceEnrichedFeature N p u x‖=enrichedFeatureBound N u := by
  rw [sourceEnrichedFeature,enrichedFeature_norm,Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

lemma profileGaussian_coefficient_squares {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (i : I) :
    (∑ l : Fin (k+1), hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2) =
      q (Fin.last k) i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (by simp [Fin.le_iff_val_le_val])))
  simp_rw [he]
  exact finite_profile_telescope (fun l => q l i)

lemma enrichedCoordinateLevel_nonneg {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : ∀ l, 0 ≤ h l) (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    0 ≤ enrichedCoordinateLevel p d h l i := by
  cases i with
  | inl i => exact mul_nonneg (by norm_num) (hh l)
  | inr i => exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma enrichedCoordinateLevel_monotone {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : Monotone h) (i : EnrichedIndex N N p) :
    Monotone (fun l => enrichedCoordinateLevel p d h l i) := by
  intro a b hab
  cases i with
  | inl i => exact mul_le_mul_of_nonneg_left (hh hab) (by norm_num)
  | inr i =>
    apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg _)

lemma enrichedCoordinateLevel_le {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} {H : ℝ} (hH : 0 ≤ H) (hh : ∀ l, h l ≤ H)
    (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    enrichedCoordinateLevel p d h l i ≤ 2*H+1 := by
  cases i with
  | inl i => dsimp [enrichedCoordinateLevel]; linarith [hh l]
  | inr i =>
    have ht : ((l.val:ℝ)/(k+1:ℕ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast l.isLt.le
    have ht0 : 0 ≤ ((l.val:ℝ)/(k+1:ℕ)) := by positivity
    exact (pow_le_one₀ ht0 ht).trans (by linarith)

lemma sourceGaussianRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ}
    (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H) (x : NormalizedSpin N × IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianRow p d h u i.val x^2) ≤ (2*H+1)*(enrichedFeatureBound N u:ℝ)^2 := by
  apply indexedGaussianRow_norm_le
  · intro i
    rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
      (enrichedCoordinateLevel_monotone p d hh)]
    exact enrichedCoordinateLevel_le p d hH hhH _ i
  · positivity
  · intro y
    have he := congrArg (fun t : ℝ => t^2) (sourceEnrichedFeature_norm N p u y)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
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
variable {S : Type*} [MeasurableSpace S]
variable (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_integrable_of_integer_endpoints {H Y : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ k : ℕ, Integrable (fun x => Real.exp (H x+(k:ℝ)*Y x)) μ ∧
      Integrable (fun x => Real.exp (H x-(k:ℝ)*Y x)) μ) (a : ℝ) :
    Integrable (fun x => Real.exp (H x+a*Y x)) μ := by
  obtain ⟨k,hk⟩ := exists_nat_gt |a|
  refine ((he k).1.add (he k).2).mono' ((hH.add (hY.const_mul a)).exp.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hy : 0 ≤ Y x
  · have ha : a ≤ (k:ℝ) := (le_abs_self a).trans hk.le
    exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_right ha hy) _)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have ha : -(k:ℝ) ≤ a := by linarith [neg_abs_le a]
    have hh : H x+a*Y x ≤ H x-(k:ℝ)*Y x := by
      have h := mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)
      nlinarith
    exact (Real.exp_le_exp.mpr hh).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
include hW hv hw hL hA hD hE

lemma countableGaussian_coupling_exp_ae (a : ℝ) :
    ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)) μ := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2) ≤ 2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  have he := (countableGaussianHamiltonian_exp_joint_integrable μ hW hm hL hA hb 1).prod_left_ae
  filter_upwards [he] with g hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [one_mul,countableGaussianHamiltonian,countableGaussianField_add,
    countableGaussianField_smul]
  congr 1
  ring

lemma countableGaussian_all_coupling_exp_ae :
    ∀ᵐ g ∂countableGaussianLaw, ∀ a : ℝ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)) μ := by
  have hp : ∀ᵐ g ∂countableGaussianLaw, ∀ k : ℕ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+(k:ℝ)*countableGaussianField w L g x)) μ :=
    ae_all_iff.mpr fun k => countableGaussian_coupling_exp_ae μ hW hv hw hL hA hD hE k
  have hn : ∀ᵐ g ∂countableGaussianLaw, ∀ k : ℕ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x-(k:ℝ)*countableGaussianField w L g x)) μ := by
    apply ae_all_iff.mpr
    intro k
    simpa only [neg_mul,sub_eq_add_neg] using
      countableGaussian_coupling_exp_ae μ hW hv hw hL hA hD hE (-(k:ℝ))
  filter_upwards [hp,hn] with g hgp hgn a
  exact coupling_integrable_of_integer_endpoints μ
    ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
    ((countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id))
    (fun k => ⟨hgp k,hgn k⟩) a

end

lemma enrichedIndexedBoundedEnergy_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (enrichedIndexedBoundedEnergy n M k f a h) :=
  ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp
    (measurable_const.prodMk measurable_fst)).sub measurable_const

lemma enrichedIndexedBoundedEnergy_bound (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :
    |enrichedIndexedBoundedEnergy n M k f a h x| ≤ (M:ℝ)*‖f‖+|(n+1:ℕ)*h (Fin.last k)| :=
  (abs_sub _ _).trans (add_le_add (normalizedPatternEnergy_bound (n+1) M f a x.1) le_rfl)

lemma sourceEnrichedFeature_measurable (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ) :
    Measurable (sourceEnrichedFeature N p u) :=
  (enrichedFeature_continuous N N p (Real.sqrt N) (perturbationAmplitude N u)).measurable

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

lemma indexedCommonDepth_self (n : ℕ) (l : IndexedLeaf n) :
    indexedCommonDepth n l l = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indexedCommonDepth,ih]

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
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
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UnboundedContact
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
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A)
variable {W : A → S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable (Function.uncurry W)) (hv : ∀ i, Measurable (v i))
variable (hw : ∀ i, Measurable (w i)) (hL : Measurable L)
variable {B : A → ℝ} {D E : ℝ} (hB : ∀ a x, |W a x| ≤ B a)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)

include hW hv hw hL

lemma kernelGaussian_coupling_joint_measurable (r : ℝ) :
    Measurable (fun a : (A × (ℕ → ℝ)) × S =>
      countableGaussianHamiltonian (W a.1.1) v L a.1.2 a.2+
        r*countableGaussianField w L a.1.2 a.2) := by
  apply (hW.comp (measurable_fst.fst.prodMk measurable_snd) |>.add
    ((countableGaussianField_measurable hv hL).comp (measurable_fst.snd.prodMk measurable_snd))).add
  exact ((countableGaussianField_measurable hw hL).comp
    (measurable_fst.snd.prodMk measurable_snd)).const_mul r

include hB hD hE

lemma kernelGaussian_coupling_exp_ae (r : ℝ) :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  let κ' : Kernel (A × (ℕ → ℝ)) S := κ.comap (Prod.fst : A × (ℕ → ℝ) → A) measurable_fst
  have hm : MeasurableSet {a : A × (ℕ → ℝ) | Integrable
      (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ' a)} :=
    measurableSet_kernel_integrable (kernelGaussian_coupling_joint_measurable hW hv hw hL r).exp.stronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact ae_of_all _ fun a => countableGaussian_coupling_exp_ae (κ a)
    (hW.comp (measurable_const.prodMk measurable_id)) hv hw hL (hB a) hD hE r

lemma kernelGaussian_all_coupling_exp_ae :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  have hp := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (j:ℝ))
  have hn := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (-(j:ℝ)))
  filter_upwards [hp,hn] with a hp hn r
  apply coupling_integrable_of_integer_endpoints (κ a.1)
    ((hW.comp (measurable_const.prodMk measurable_id)).add
      ((countableGaussianField_measurable hv hL).comp (measurable_const.prodMk measurable_id)))
    ((countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)) _ r
  intro j
  exact ⟨hp j,by simpa only [neg_mul,sub_eq_add_neg,Function.comp_apply,Function.uncurry_apply_pair,
    id_eq,Pi.add_apply,countableGaussianHamiltonian] using hn j⟩

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGaussianTestRow_measurable {N k : ℕ} (p d : Fin N → ℕ)
    (h : Fin (k+1) → ℝ) (j : Fin N) (i : ℕ) :
    Measurable (sourceGaussianTestRow p d h j i) :=
  indexedGaussianRow_measurable _ _ (enrichedFeature_continuous _ _ _ _ _).measurable i

lemma sourceGaussianTestRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ} (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H)
    (j : Fin N) (x : NormalizedSpin N×IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianTestRow p d h j i.val x^2) ≤ 2*H+1 := by
  have hb (y : NormalizedSpin N) : (∑ i, sourceGaussianTestFeature N p j y i^2) ≤ (1:ℝ) := by
    have he := enrichedFeature_norm_sq N N p 0 (Pi.single j 1) y
    have hsum : (∑ i : Fin N, ((Pi.single j (1:ℝ) : Fin N → ℝ) i)^2) = (1:ℝ) := by
      classical
      simp [Pi.single_apply]
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,hsum] at he
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,sourceGaussianTestFeature] using he.le
  have ht := indexedGaussianRow_norm_le k
    (hierarchyRowCoefficients k (profileGaussianRoot (enrichedCoordinateLevel p d h))
      (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceGaussianTestFeature N p j)
    (C := 2*H+1) (D := 1)
    (fun i => by
      rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
        (enrichedCoordinateLevel_monotone p d hh)]
      exact enrichedCoordinateLevel_le p d hH hhH _ i)
    (by positivity) hb x
  simpa only [mul_one,sourceGaussianTestRow] using ht

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceCoupling_all_exp_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x+
        r*sourceCouplingEnergy n k p d h j a x)) (sourceSpinLeafKernel n k a.1) := by
  have he := kernelGaussian_all_coupling_exp_ae (sourceSpinLeafKernel n k) (sourceBaseDataLaw n k z t)
    (sourceBaseEnergy_measurable n k f h) (sourceGaussianRow_measurable p d h u)
    (sourceGaussianTestRow_measurable p d h j) (indexedGaussianRowLength_measurable k)
    (fun a => enrichedIndexedBoundedEnergy_bound n a.1 k f (patternPrefix (n+1) a.1 a.2.1) h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)) j)
  filter_upwards [he] with a ha r
  simpa only [sourceCouplingHamiltonian,enrichedIndexedHamiltonian,sourceBaseEnergy,
    sourceCouplingEnergy,mul_assoc] using ha (r*perturbationAmplitude (n+1) (fun _ => 1) j)

lemma sourceCouplingHamiltonian_section (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (a : SourceBaseData n k × (ℕ → ℝ)) :
    Measurable (sourceCouplingHamiltonian n k f p d h u a) :=
  (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
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
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_prefix_integral (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) ∂P := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val)) :=
    hG.comp (by fun_prop)
  have hi : Integrable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hGB (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => kernelInfiniteReplica_prefix_integral _ a r hG

lemma annealedInfiniteReplica_gibbs_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P := by
  rw [annealedInfiniteReplica_prefix_integral κ P H hH r hG hGB]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r G

end

lemma sourceGibbsArray_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : CompactArray CompactJointOverlap → ℝ} (hF : Measurable F) :
    (∫ Q, F Q ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, F (sourceJointArray a.2) ∂annealedInfiniteReplicaMeasure (sourceFullSpinLeafKernel n k)
        ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
        (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) := by
  exact integral_map ((sourceJointArray_measurable (n+1) k).comp measurable_snd).aemeasurable hF.aestronglyMeasurable

lemma sourceGibbsArray_block_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (r : ℕ)
    {F : CompactBlock CompactJointOverlap r → ℝ} (hF : Measurable F)
    {B : ℝ} (hFB : ∀ Q, |F Q|≤B) :
    (∫ Q, F (compactBlock r Q) ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, gibbsReplicaMean (sourceFullSpinLeafKernel n k a)
        (sourceCouplingHamiltonian n k f p d h u a) r
        (fun x => F (fun i j => sourceJointOverlap (x i) (x j)))
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw := by
  rw [sourceGibbsArray_integral n k f p d h u z t (F:=fun Q => F (compactBlock r Q))
    (hF.comp (compactBlock_continuous r).measurable)]
  have he := sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t
  have he0 : ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
    filter_upwards [he] with a ha
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  exact annealedInfiniteReplica_gibbs_prefix (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) _
    (sourceCouplingHamiltonian_measurable n k f p d h u) he0 r
    (hF.comp (Measurable.of_eval fun row => Measurable.of_eval fun column =>
      (sourceJointOverlap_measurable (n+1) k).comp
        ((measurable_pi_apply row).prodMk (measurable_pi_apply column))))
    (fun x => hFB _)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
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

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

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

lemma abs_log_le_self_add_inv {x : ℝ} (hx : 0<x) : |Real.log x|≤x+x⁻¹ := by
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at hh
    linarith
  · exact (Real.log_le_sub_one_of_pos hx).trans (by linarith [inv_nonneg.mpr hx.le])

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x|≤A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E)

include hW hv hL hA hD in
lemma gaussianLogPartition_integrable :
    Integrable (fun g => Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)) countableGaussianLaw := by
  have hi : Integrable (fun g => tiltPartition μ (countableGaussianHamiltonian W v L g) 1) countableGaussianLaw := by
    simpa only [tiltPartition,one_mul] using
      (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).integral_prod_right
  have hj : Integrable (fun g => (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹) countableGaussianLaw := by
    simpa only [pow_one] using gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 1
  refine (hi.add hj).mono' ((gaussianHamiltonianPartition_measurable μ hW hv hL).log.aestronglyMeasurable) ?_
  filter_upwards [gaussianHamiltonianPartition_pos_ae μ hW hv hL hA hD] with g hg
  simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_log_le_self_add_inv hg

include hW hv hw hL hA hD hE

lemma gaussianCouplingLog_integrable (a : ℝ) :
    Integrable (fun g => Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1)) countableGaussianLaw := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  convert gaussianLogPartition_integrable μ hW hm hL hA hb using 1
  all_goals try with_reducible_and_instances rfl
  ext g
  congr 3
  ext x
  simp only [countableGaussianHamiltonian,countableGaussianField_add,countableGaussianField_smul]
  ring

lemma gaussianCouplingMean_derivative (a : ℝ) :
    HasDerivAt (fun b => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      (∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (countableGaussianField w L g) 1 ∂countableGaussianLaw) a := by
  let H := countableGaussianHamiltonian W v L
  let Y := countableGaussianField w L
  have hH : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have hY : Measurable (Function.uncurry Y) := countableGaussianField_measurable hw hL
  have hi := gaussianCouplingLog_integrable μ hW hv hw hL hA hD hE
  apply (annealed_convex_hasDerivAt countableGaussianLaw (fun b => (hi b).aestronglyMeasurable) _ hi _ a).2
  · intro b
    exact (kernel_tiltMean_measurable (Kernel.const _ μ) (hH.add (hY.const_mul b)) hY).aestronglyMeasurable
  · filter_upwards [countableGaussian_all_coupling_exp_ae μ hW hv hw hL hA hD hE] with g hg
    have hHg : Measurable (H g) := hH.of_uncurry_left
    have hYg : Measurable (Y g) := hY.of_uncurry_left
    exact ⟨coupling_log_convex μ hHg hYg hg,fun b => coupling_log_hasDerivAt μ hHg hYg hg b⟩

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

lemma gaussianCouplingMean_derivative_covariance (a : ℝ) :
    HasDerivAt (fun b => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      (∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => countableGaussianCovariance (fun i x => v i x+a*w i x) w L x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => countableGaussianCovariance (fun i x => v i x+a*w i x) w L (x 1) (x 0)) ∂countableGaussianLaw) a := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  have he (g) : countableGaussianHamiltonian W (fun i x => v i x+a*w i x) L g =
      fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x := by
    funext x
    simp only [countableGaussianHamiltonian,countableGaussianField_add,countableGaussianField_smul]
    ring
  have hi := annealedGaussianTiltMean_ibp μ hW hm hw hL hA hb hE
  simp_rw [he] at hi
  exact hi ▸ gaussianCouplingMean_derivative μ hW hv hw hL hA hD hE a

lemma gaussianCouplingMean_difference_bound {B : ℝ} (hB : 0≤B)
    (hC : ∀ a ∈ Icc (0:ℝ) 1, ∀ x y,
      |countableGaussianCovariance (fun i x => v i x+a*w i x) w L x y|≤B) :
    |(∫ g, Real.log (tiltPartition μ (fun x => countableGaussianHamiltonian W v L g x+
      countableGaussianField w L g x) 1) ∂countableGaussianLaw)-
    ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1) ∂countableGaussianLaw|≤2*B := by
  let F := fun a => ∫ g, Real.log (tiltPartition μ (fun x =>
    countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1) ∂countableGaussianLaw
  let C := fun a => countableGaussianCovariance (fun i x => v i x+a*w i x) w L
  let D' := fun a => ∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => C a x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => C a (x 1) (x 0)) ∂countableGaussianLaw
  have hd (a : ℝ) : HasDerivAt F (D' a) a :=
    gaussianCouplingMean_derivative_covariance μ hW hv hw hL hA hD hE a
  have hb (a) (ha : a ∈ Icc (0:ℝ) 1) : ‖D' a‖≤2*B := by
    have hm : Measurable (Function.uncurry (C a)) := countableGaussianCovariance_measurable
      (fun i => (hv i).add ((hw i).const_mul a)) hw hL
    have hH (g) : Measurable (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) :=
      (countableGaussianHamiltonian_measurable hW hv hL).of_uncurry_left.add
        ((countableGaussianField_measurable hw hL).of_uncurry_left.const_mul a)
    have hdiag (g) : |tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => C a x x) 1|≤B := tiltMean_bound_general μ (hH g)
          (hm.comp (measurable_id.prodMk measurable_id)) hB (fun x => hC a ha x x)
    have hpair (g) : |gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => C a (x 1) (x 0))|≤B := tiltMean_bound_general _
          (replicaPotential_measurable (hH g) 2)
          (hm.comp ((measurable_pi_apply 1).prodMk (measurable_pi_apply 0))) hB (fun x => hC a ha _ _)
    simpa only [D',probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := countableGaussianLaw) (C := 2*B) (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hdiag g,hpair g]))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun a (_ : a ∈ Icc (0:ℝ) 1) => (hd a).hasDerivWithinAt) hb (convex_Icc (0:ℝ) 1)
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  simpa only [F,one_mul,zero_mul,add_zero,sub_zero,norm_one,mul_one,Real.norm_eq_abs] using hm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianComparison
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma countableGaussianCovariance_cs {S : Type*} [MeasurableSpace S]
    (v w : ℕ → S → ℝ) (L : S → ℕ) {D E : ℝ} (hD0 : 0≤D) (hE0 : 0≤E)
    (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E) (x y : S) :
    |countableGaussianCovariance v w L x y|≤Real.sqrt D*Real.sqrt E := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin (L x))))
    (fun i => maskedGaussianCoefficient w L i.val x) (fun i => maskedGaussianCoefficient v L i.val y)
  have hm : countableGaussianCovariance v w L x y^2≤E*D := hs.trans
    (mul_le_mul (maskedGaussianCoefficient_sq_bound w L hE (L x) x)
      (maskedGaussianCoefficient_sq_bound v L hD (L x) y) (by positivity) hE0)
  calc
    _ = Real.sqrt (countableGaussianCovariance v w L x y^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (E*D) := Real.sqrt_le_sqrt hm
    _ = _ := by rw [mul_comm E D, Real.sqrt_mul hD0]

lemma countableGaussian_log_comparison {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) {A D E : ℝ} (hD0 : 0≤D) (hE0 : 0≤E)
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E) :
    |(∫ g, Real.log (tiltPartition μ (fun x => countableGaussianHamiltonian W v L g x+
      countableGaussianField w L g x) 1) ∂countableGaussianLaw)-
    ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1) ∂countableGaussianLaw|≤
      2*(Real.sqrt (2*D+2*E)*Real.sqrt E) := by
  apply gaussianCouplingMean_difference_bound μ hW hv hw hL hA hD hE (by positivity)
  intro a ha x y
  apply countableGaussianCovariance_cs _ _ _ (by positivity) hE0 _ hE
  intro z
  have hb : (∑ i : Fin (L z), (v i.val z+a*w i.val z)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 z
  have ha2 : a^2≤1 := by nlinarith [ha.1,ha.2]
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right ha2 hE0])

variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S] (n : ℕ)

lemma indexedCoefficientSquare_nonneg (B : Fin (n+1)→I→ℝ) : 0 ≤ indexedCoefficientSquare n B := by
  unfold indexedCoefficientSquare
  positivity

lemma indexedCoefficientSquare_continuous : Continuous (indexedCoefficientSquare (I := I) n) := by
  unfold indexedCoefficientSquare
  fun_prop

omit [MeasurableSpace S] in
lemma indexedGaussianRow_sub (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I) (j : ℕ) (x : S×IndexedLeaf n) :
    indexedGaussianRow n (fun l i => B l i-C l i) V j x =
      indexedGaussianRow n B V j x-indexedGaussianRow n C V j x := by
  unfold indexedGaussianRow finiteGaussianRow
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

omit [MeasurableSpace S] in
lemma indexedGaussianRow_square_total (B : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    {D : ℝ} (hD : ∀ x, (∑ i, V x i^2)≤D) (x : S×IndexedLeaf n) :
    (∑ j : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V j.val x^2)≤
      indexedCoefficientSquare n B*D := by
  apply indexedGaussianRow_norm_le _ _ _ _ (indexedCoefficientSquare_nonneg n B) hD
  intro i
  unfold indexedCoefficientSquare
  exact Finset.single_le_sum (f := fun i => ∑ l, B l i^2) (fun j _ => by positivity) (Finset.mem_univ i)

lemma indexedGaussianMean_comparison (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0≤D)
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i, V x i^2)≤D) (B C : Fin (n+1)→I→ℝ) :
    |indexedGaussianMean n μ W V B-indexedGaussianMean n μ W V C|≤
      2*(Real.sqrt (2*(indexedCoefficientSquare n C*D)+
        2*(indexedCoefficientSquare n (fun l i => B l i-C l i)*D))*
      Real.sqrt (indexedCoefficientSquare n (fun l i => B l i-C l i)*D)) := by
  have hb := countableGaussian_log_comparison μ hW (indexedGaussianRow_measurable n C hV)
    (indexedGaussianRow_measurable n (fun l i => B l i-C l i) hV)
    (indexedGaussianRowLength_measurable n)
    (mul_nonneg (indexedCoefficientSquare_nonneg n C) hD0)
    (mul_nonneg (indexedCoefficientSquare_nonneg n _) hD0)
    hA (indexedGaussianRow_square_total n C V hD) (indexedGaussianRow_square_total n _ V hD)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  unfold indexedGaussianMean
  congr 3
  funext g
  congr 2
  funext x
  simp only [countableGaussianHamiltonian,countableGaussianField,countableGaussianField,
    gaussianPrefixField,indexedGaussianRow_sub]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma indexedGaussianMean_add_const (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ}
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i, V x i^2)≤D)
    (B : Fin (n+1)→I→ℝ) (c : ℝ) :
    indexedGaussianMean n μ (fun x => W x+c) V B = indexedGaussianMean n μ W V B+c := by
  have hrow := indexedGaussianRow_measurable n B hV
  have hlen := indexedGaussianRowLength_measurable (S := S) (I := I) n
  have hb := indexedGaussianRow_square_total n B V hD
  have hi := gaussianLogPartition_integrable μ hW hrow hlen hA hb
  have he : ∀ᵐ g ∂countableGaussianLaw,
      Real.log (tiltPartition μ (countableGaussianHamiltonian (fun x => W x+c) (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1) =
      Real.log (tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1)+c := by
    filter_upwards [gaussianHamiltonianPartition_pos_ae μ hW hrow hlen hA hb] with g hg
    have hf : tiltPartition μ (countableGaussianHamiltonian (fun x => W x+c) (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1 =
        tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
          (indexedGaussianRowLength (I := I) n) g) 1*Real.exp c := by
      unfold tiltPartition countableGaussianHamiltonian
      simp only [one_mul]
      simp_rw [show ∀ x, W x+c+countableGaussianField (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g x =
        (W x+countableGaussianField (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g x)+c by intro x; ring,Real.exp_add]
      exact integral_mul_const _ _
    rw [hf,Real.log_mul hg.ne' (Real.exp_ne_zero c),Real.log_exp]
  unfold indexedGaussianMean
  rw [integral_congr_ae he,integral_add hi (integrable_const c),integral_const,probReal_univ,one_smul]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldContinuity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceFieldCoefficients_continuous {N k : ℕ} (p d : Fin N→ℕ) :
    Continuous (@sourceFieldCoefficients N k p d) := by
  have hc (l : Fin (k+1)) (i : EnrichedIndex N N p) :
      Continuous (fun h : Fin (k+1)→ℝ => enrichedCoordinateLevel p d h l i) := by
    cases i <;> simp only [enrichedCoordinateLevel] <;> fun_prop
  apply continuous_pi
  intro l
  apply continuous_pi
  intro i
  simp only [sourceFieldCoefficients,profileGaussian_coefficient]
  induction l using Fin.cases with
  | zero => simpa only [Fin.cases_zero] using (hc 0 i).sqrt
  | succ l => simpa only [Fin.cases_succ, Pi.sub_apply] using ((hc l.succ i).sub (hc l.castSucc i)).sqrt

lemma sourceFieldDistance_continuous {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h : Fin (k+1)→ℝ) : Continuous (fun h' => sourceFieldDistance p d u h' h) := by
  have hc := sourceFieldCoefficients_continuous (k := k) p d
  have he : Continuous (fun h' => indexedCoefficientSquare k
      (fun l i => sourceFieldCoefficients p d h' l i-sourceFieldCoefficients p d h l i)) := by
    simpa only [Function.comp_def,Pi.sub_def] using
      (indexedCoefficientSquare_continuous (I := EnrichedIndex N N p) k).comp
        (hc.sub (continuous_const (y := sourceFieldCoefficients p d h)))
  unfold sourceFieldDistance
  exact (continuous_const.mul (continuous_const.mul
    ((continuous_const.add (continuous_const.mul (he.mul continuous_const))).sqrt.mul
      (he.mul continuous_const).sqrt))).add ((continuous_apply _).sub continuous_const).abs

lemma sourceFieldDistance_self {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h : Fin (k+1)→ℝ) : sourceFieldDistance p d u h h=0 := by
  simp [sourceFieldDistance,indexedCoefficientSquare]

lemma sourceKernelPressure_gaussianMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    (∫ g, sourceKernelPressure n k f p d u h (a,g) ∂countableGaussianLaw) =
      (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
        (fun x => normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1)
        (sourceEnrichedFeature (n+1) p u) (sourceFieldCoefficients p d h)-h (Fin.last k) := by
  let W : NormalizedSpin (n+1)×IndexedLeaf k→ℝ := fun x =>
    normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1
  have hW : Measurable W := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have hA (x) : |W x|≤(a.1:ℝ)*‖f‖ := normalizedPatternEnergy_bound (n+1) a.1 f _ x.1
  have hD (x) : (∑ i, sourceEnrichedFeature (n+1) p u x i^2)≤(enrichedFeatureBound (n+1) u:ℝ)^2 := by
    have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm (n+1) p u x)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le
  have he := indexedGaussianMean_add_const k (sourceSpinLeafKernel n k a) hW
    (sourceEnrichedFeature_measurable (n+1) p u) hA hD (sourceFieldCoefficients p d h)
    (-((n+1:ℕ)*h (Fin.last k)))
  simp only [sourceKernelPressure,integral_const_mul]
  change (1/(n+1:ℕ):ℝ)*indexedGaussianMean k (sourceSpinLeafKernel n k a)
    (fun x => W x + -((n+1:ℕ)*h (Fin.last k))) (sourceEnrichedFeature (n+1) p u) (sourceFieldCoefficients p d h) = _
  rw [he]
  dsimp only [W]
  field_simp
  ring

lemma sourceConditional_field_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h' h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    |(∫ g, sourceKernelPressure n k f p d u h' (a,g) ∂countableGaussianLaw)-
      ∫ g, sourceKernelPressure n k f p d u h (a,g) ∂countableGaussianLaw| ≤
        sourceFieldDistance p d u h' h := by
  have hW : Measurable (fun x : NormalizedSpin (n+1)×IndexedLeaf k =>
      normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1) := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have H := indexedGaussianMean_comparison k (sourceSpinLeafKernel n k a)
    hW (sourceEnrichedFeature_measurable (n+1) p u)
    (sq_nonneg (enrichedFeatureBound (n+1) u:ℝ))
    (fun x => normalizedPatternEnergy_bound (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1)
    (fun x => show (∑ i, sourceEnrichedFeature (n+1) p u x i^2)≤(enrichedFeatureBound (n+1) u:ℝ)^2 from by
      have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm (n+1) p u x)
      simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le)
    (sourceFieldCoefficients p d h') (sourceFieldCoefficients p d h)
  rw [sourceKernelPressure_gaussianMean,sourceKernelPressure_gaussianMean]
  rw [show ∀ a b c e : ℝ, a-b-(c-e)=(a-c)-(b-e) by intros; ring]
  apply (abs_sub _ _).trans
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(n+1:ℕ))]
  exact add_le_add (mul_le_mul_of_nonneg_left H (by positivity : (0:ℝ)≤1/(n+1:ℕ))) le_rfl

lemma sourceDirectionProfile_nonneg {N k : ℕ} (p : Fin N→ℕ) {a : Fin (k+1)→ℝ}
    (ha0 : ∀ l, 0 ≤ a l) (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    0 ≤ sourceDirectionProfile p a l i := by
  cases i with
  | inl i => exact mul_nonneg (by norm_num) (ha0 l)
  | inr i => exact le_rfl

lemma sourceDirectionProfile_monotone {N k : ℕ} (p : Fin N→ℕ) {a : Fin (k+1)→ℝ}
    (ha : Monotone a) (i : EnrichedIndex N N p) :
    Monotone (fun l => sourceDirectionProfile p a l i) := by
  cases i with
  | inl i => exact fun l m hlm => mul_le_mul_of_nonneg_left (ha hlm) (by norm_num)
  | inr i => exact monotone_const

lemma sourceFieldCoefficients_affine_covariance {N k : ℕ} (p d : Fin N→ℕ)
    {h a : Fin (k+1)→ℝ} (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) {t : ℝ} (ht : 0 ≤ t)
    (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    sourceFieldCoefficients p d (fun l => h l+t*a l) l i^2 =
      sourceFieldCoefficients p d h l i^2+t*sourceDirectionCoefficients p a l i^2 := by
  have hv (r : Fin (k+1)) : enrichedCoordinateLevel p d (fun l => h l+t*a l) r i =
      enrichedCoordinateLevel p d h r i+t*sourceDirectionProfile p a r i := by
    cases i <;> simp [enrichedCoordinateLevel,sourceDirectionProfile]
    ring
  have hq0 := enrichedCoordinateLevel_nonneg p d hh0
  have hqm := enrichedCoordinateLevel_monotone p d hh
  have hr0 := sourceDirectionProfile_nonneg p ha0
  have hrm := sourceDirectionProfile_monotone p ha
  simp only [sourceFieldCoefficients,sourceDirectionCoefficients,profileGaussian_coefficient]
  induction l using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero,hv,Real.sq_sqrt (hq0 0 i),Real.sq_sqrt (hr0 0 i)]
    rw [Real.sq_sqrt (add_nonneg (hq0 0 i) (mul_nonneg ht (hr0 0 i)))]
  | succ l =>
    have hb := sub_nonneg.mpr (hqm i (Fin.castSucc_le_succ l))
    have hc := sub_nonneg.mpr (hrm i (Fin.castSucc_le_succ l))
    simp only [Fin.cases_succ,hv,Real.sq_sqrt hb,Real.sq_sqrt hc]
    have hd : 0 ≤ enrichedCoordinateLevel p d h l.succ i+t*sourceDirectionProfile p a l.succ i-
        (enrichedCoordinateLevel p d h l.castSucc i+t*sourceDirectionProfile p a l.castSucc i) := by
      nlinarith [mul_nonneg ht hc]
    rw [Real.sq_sqrt hd]
    ring

lemma sourceDirection_feature_cross {N k : ℕ} (p : Fin N→ℕ)
    (u : Fin N→ℝ) (a : Fin (k+1)→ℝ) (l : Fin (k+1)) (x y : NormalizedSpin N) :
    (∑ i : EnrichedIndex N N p, sourceDirectionProfile p a l i*
      sourceEnrichedFeature N p u x i*sourceEnrichedFeature N p u y i) =
      2*(N:ℝ)*a l*spinOverlap x y := by
  rw [Fintype.sum_sum_type]
  simp only [sourceDirectionProfile,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,add_zero]
  change (∑ i : Fin N, 2*a l*(Real.sqrt (N:ℝ)*x.val i)*(Real.sqrt (N:ℝ)*y.val i)) =
    2*(N:ℝ)*a l*(∑ i : Fin N, y.val i*x.val i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = 2*a l*(Real.sqrt (N:ℝ))^2*(y.val i*x.val i) := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring

lemma sourceDirection_covariance {N k : ℕ} (p : Fin N→ℕ)
    (u : Fin N→ℝ) {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (x y : NormalizedSpin N×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature N p u))
      (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature N p u))
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) x y =
      2*(N:ℝ)*a (indexedCommonDepth k y.2 x.2)*spinOverlap x.1 y.1 := by
  unfold sourceDirectionCoefficients
  rw [profileGaussianRow_covariance _ (sourceDirectionProfile_nonneg p ha0 0)
    (sourceDirectionProfile_monotone p ha),sourceDirection_feature_cross]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianGibbsContinuity
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
section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_tiltIntegral_continuous {H Y G : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => tiltIntegral μ (fun x => H x+a*Y x) G 1) := by
  rw [continuous_iff_continuousAt]
  intro a
  simp only [tiltIntegral,one_mul]
  change Tendsto (fun b => ∫ x, Real.exp (H x+b*Y x)*G x ∂μ) (𝓝 a)
    (𝓝 (∫ x, Real.exp (H x+a*Y x)*G x ∂μ))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (Real.exp (H x+(a-1)*Y x)+Real.exp (H x+(a+1)*Y x))*B)
  · exact Eventually.of_forall fun b => ((hH.add (hY.const_mul b)).exp.mul hG).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (by linarith : a-1<a) (by linarith : a<a+1)] with b hb
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),
      mul_comm (Real.exp (H x+b*Y x)) |G x|,mul_comm (_+_) B]
    apply mul_le_mul (hGB x) _ (Real.exp_pos _).le hB
    by_cases hy : 0 ≤ Y x
    · exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_right hb.2.le hy) _)).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonpos_right hb.1.le (le_of_not_ge hy)) _)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact ((he (a-1)).add (he (a+1))).mul_const B
  · exact ae_of_all _ fun x => (show Continuous (fun b : ℝ => Real.exp (H x+b*Y x)*G x) from by fun_prop).continuousAt

lemma coupling_tiltMean_continuous {H Y G : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => tiltMean μ (fun x => H x+a*Y x) G 1) := by
  have hp : Continuous (fun a => tiltPartition μ (fun x => H x+a*Y x) 1) := by
    simpa only [tiltIntegral,tiltPartition,mul_one] using
      coupling_tiltIntegral_continuous μ hH hY measurable_const he (by norm_num : (0:ℝ) ≤ 1)
        (fun _ => by norm_num : ∀ x : S, |(fun _ : S => (1:ℝ)) x| ≤ 1)
  exact (coupling_tiltIntegral_continuous μ hH hY hG he hB hGB).div hp
    (fun a => (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he a)).ne')

lemma coupling_gibbsReplicaMean_continuous {H Y : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => gibbsReplicaMean μ (fun x => H x+a*Y x) n G) := by
  have hr (a : ℝ) : replicaPotential (fun x => H x+a*Y x) n =
      fun x => replicaPotential H n x+a*replicaPotential Y n x := by
    funext x
    simp [replicaPotential,Finset.sum_add_distrib,Finset.mul_sum]
  have hi (a : ℝ) : Integrable (fun x => Real.exp (replicaPotential H n x+a*replicaPotential Y n x))
      (Measure.pi (fun _ : Fin n => μ)) := by
    simpa only [one_mul,hr] using replica_exp_integrable μ (H := fun x => H x+a*Y x) (t := 1) (by simpa only [one_mul] using he a) n
  simpa only [gibbsReplicaMean,hr] using coupling_tiltMean_continuous (Measure.pi (fun _ : Fin n => μ))
    (replicaPotential_measurable hH n) (replicaPotential_measurable hY n) hG hi hB hGB

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (P : Measure A) [IsFiniteMeasure P] (μ : Measure S) [IsProbabilityMeasure μ]

lemma annealedCoupling_tiltMean_continuous {H Y : A → S → ℝ} {G : S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ g ∂P, ∀ a : ℝ, Integrable (fun x => Real.exp (H g x+a*Y g x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => ∫ g, tiltMean μ (fun x => H g x+a*Y g x) G 1 ∂P) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun b => (kernel_tiltMean_measurable (Kernel.const A μ) (H := fun g x => H g x+b*Y g x) (Y := fun _ => G)
      (hH.add (hY.const_mul b)) (hG.comp measurable_snd)).aestronglyMeasurable
  · exact Eventually.of_forall fun b => ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using tiltMean_bound_general μ (H := fun x => H g x+b*Y g x)
        (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul b)) hG hB hGB
  · exact integrable_const _
  · filter_upwards [he] with g hg
    exact (coupling_tiltMean_continuous μ hH.of_uncurry_left hY.of_uncurry_left hG hg hB hGB).continuousAt

lemma annealedCoupling_replicaMean_continuous {H Y : A → S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ g ∂P, ∀ a : ℝ, Integrable (fun x => Real.exp (H g x+a*Y g x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => ∫ g, gibbsReplicaMean μ (fun x => H g x+a*Y g x) n G ∂P) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun b => (kernel_replicaMean_measurable (Kernel.const A μ) (H := fun g x => H g x+b*Y g x) (G := fun _ => G)
      (hH.add (hY.const_mul b)) (hG.comp measurable_snd)).aestronglyMeasurable
  · exact Eventually.of_forall fun b => ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean,Pi.add_apply] using tiltMean_bound_general
        (Measure.pi (fun _ : Fin n => μ))
        (replicaPotential_measurable (v := fun x => H g x+b*Y g x) (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul b)) n) hG hB hGB
  · exact integrable_const _
  · filter_upwards [he] with g hg
    exact (coupling_gibbsReplicaMean_continuous μ hH.of_uncurry_left hY.of_uncurry_left hG hg hB hGB).continuousAt

lemma sqrt_coupling_derivative {M C : ℝ → ℝ}
    (hd : ∀ a, HasDerivAt M (a*C a) a) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s => M (Real.sqrt s)) (C (Real.sqrt t)/2) t := by
  have hh := (hd (Real.sqrt t)).comp t (Real.hasDerivAt_sqrt ht.ne')
  have hp := (Real.sqrt_pos.mpr ht).ne'
  have he : Real.sqrt t*C (Real.sqrt t)*(1/(2*Real.sqrt t))=C (Real.sqrt t)/2 := by
    field_simp [hp]
  simpa only [Function.comp_def,he] using hh

lemma sqrt_coupling_right_derivative {M C : ℝ → ℝ}
    (hd : ∀ a, HasDerivAt M (a*C a) a) (hC : Continuous C) :
    HasDerivWithinAt (fun s => M (Real.sqrt s)) (C 0/2) (Ici 0) 0 := by
  have hm : Continuous M := continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · intro t ht
    exact (sqrt_coupling_derivative hd ht).differentiableAt.differentiableWithinAt
  · exact (hm.comp Real.continuous_sqrt).continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hh : Tendsto (fun t => C (Real.sqrt t)/2) (𝓝[>] 0) (𝓝 (C 0/2)) := by
      simpa only [Function.comp_def,Real.sqrt_zero] using
        (((hC.comp Real.continuous_sqrt).div_const 2).continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sqrt_coupling_derivative hd ht).deriv.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovarianceLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {I : Type} [Fintype I] [DecidableEq I]

lemma doubledGaussianRows_gram (B C D : I → ℝ) (h : ∀ i, D i^2=B i^2+C i^2) :
    Matrix.gram ℝ (doubledGaussianRows B C) = Matrix.gram ℝ (diagonalGaussianRows D) := by
  ext i j
  change inner ℝ (doubledGaussianRows B C i) (doubledGaussianRows B C j) =
    inner ℝ (diagonalGaussianRows D i) (diagonalGaussianRows D j)
  simp only [doubledGaussianRows,diagonalGaussianRows,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,EuclideanSpace.basisFun_inner]
  by_cases hij : i=j
  · subst j; simp [← sq,h]
  · simp [hij]

lemma doubledGaussianRows_law (B C D : I → ℝ) (h : ∀ i, D i^2=B i^2+C i^2) :
    (stdGaussian (EuclideanSpace ℝ (I ⊕ I))).map (gaussianRows (doubledGaussianRows B C)) =
      (stdGaussian (EuclideanSpace ℝ I)).map (gaussianRows (diagonalGaussianRows D)) := by
  rw [gaussianRows_map_stdGaussian,gaussianRows_map_stdGaussian,doubledGaussianRows_gram B C D h]

omit [DecidableEq I] in
lemma doubledGaussianRows_apply (B C : I → ℝ) (g : EuclideanSpace ℝ (I ⊕ I)) (i : I) :
    gaussianRows (doubledGaussianRows B C) g i = B i*g (Sum.inl i)+C i*g (Sum.inr i) := by
  simp only [gaussianRows_apply,doubledGaussianRows,inner_add_left,real_inner_smul_left,
    EuclideanSpace.basisFun_inner]

omit [DecidableEq I] in
lemma diagonalGaussianRows_apply (D : I → ℝ) (g : EuclideanSpace ℝ I) (i : I) :
    gaussianRows (diagonalGaussianRows D) g i = D i*g i := by
  simp only [gaussianRows_apply,diagonalGaussianRows,real_inner_smul_left,EuclideanSpace.basisFun_inner]

end
variable {V I : Type} [Countable V] [Fintype I] [DecidableEq I]

theorem countableGaussian_covariance_addition_law (B C D : V → I → ℝ)
    (h : ∀ v i, D v i^2=B v i^2+C v i^2) :
    countableGaussianLaw.map (fun g v => gaussianRows (doubledGaussianRows (B v) (C v))
      (countableGaussianVectors (I := I ⊕ I) g v)) =
    countableGaussianLaw.map (fun g v => gaussianRows (diagonalGaussianRows (D v))
      (countableGaussianVectors (I := I) g v)) := by
  have hm : Measurable (fun f : V → EuclideanSpace ℝ (I ⊕ I) => fun v =>
      gaussianRows (doubledGaussianRows (B v) (C v)) (f v)) := by fun_prop
  have hn : Measurable (fun f : V → EuclideanSpace ℝ I => fun v =>
      gaussianRows (diagonalGaussianRows (D v)) (f v)) := by fun_prop
  rw [show (fun g v => gaussianRows (doubledGaussianRows (B v) (C v)) (countableGaussianVectors g v)) =
      (fun f v => gaussianRows (doubledGaussianRows (B v) (C v)) (f v)) ∘ countableGaussianVectors from rfl,
    ← Measure.map_map hm countableGaussianVectors_measurable,countableGaussianVectors_law,
    Measure.infinitePi_map_pi _ (fun v => (gaussianRows (doubledGaussianRows (B v) (C v))).measurable)]
  rw [show (fun g v => gaussianRows (diagonalGaussianRows (D v)) (countableGaussianVectors g v)) =
      (fun f v => gaussianRows (diagonalGaussianRows (D v)) (f v)) ∘ countableGaussianVectors from rfl,
    ← Measure.map_map hn countableGaussianVectors_measurable,countableGaussianVectors_law,
    Measure.infinitePi_map_pi _ (fun v => (gaussianRows (diagonalGaussianRows (D v))).measurable)]
  congr 1
  funext v
  exact doubledGaussianRows_law (B v) (C v) (D v) (h v)

variable {S : Type} [MeasurableSpace S]
variable (n : ℕ)

omit [DecidableEq I] in
lemma sharedMarksHamiltonian_measurable {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) :
    Measurable (Function.uncurry (sharedMarksHamiltonian n W V)) := by
  unfold Function.uncurry sharedMarksHamiltonian
  apply (hW.comp measurable_snd).add
  apply Finset.measurable_sum
  intro l hl
  apply Finset.measurable_sum
  intro i hi
  have he : Measurable (fun q : (SharedVertex n→EuclideanSpace ℝ I)×IndexedLeaf n =>
      q.1 (indexedLeafSharedVertex n q.2 l) i) := by
    apply measurable_from_prod_countable_left
    intro leaf
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp (measurable_pi_apply (indexedLeafSharedVertex n leaf l))
  exact (he.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
    ((EuclideanSpace.proj i).measurable.comp (hV.comp (measurable_fst.comp measurable_snd)))

omit [MeasurableSpace S] [DecidableEq I] in
lemma sharedMarks_diagonal_eq (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B : Fin (n+1)→I→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    sharedMarksHamiltonian n W V (fun v => gaussianRows (diagonalGaussianRows (B (indexedSharedVertexDepth n v)))
      (countableGaussianVectors g v)) x =
    countableGaussianHamiltonian W (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g x := by
  rw [countableGaussianHamiltonian,indexedGaussianRow_field]
  unfold sharedMarksHamiltonian
  simp only [indexedLeafSharedVertex_depth,diagonalGaussianRows_apply,countableGaussianVectors]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [MeasurableSpace S] [DecidableEq I] in
lemma sharedMarks_doubled_eq (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B C : Fin (n+1)→I→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    sharedMarksHamiltonian n W V (fun v => gaussianRows (doubledGaussianRows
      (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))
      (countableGaussianVectors g v)) x =
    countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x := by
  rw [countableGaussianHamiltonian,indexedGaussianRow_field]
  unfold sharedMarksHamiltonian
  simp only [indexedLeafSharedVertex_depth,doubledGaussianRows_apply,countableGaussianVectors]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [Fintype.sum_sum_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Sum.elim_inl,Sum.elim_inr]
  ring

theorem indexedGaussianMean_covariance_addition (μ : Measure (S×IndexedLeaf n)) [IsFiniteMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) (B C D : Fin (n+1)→I→ℝ)
    (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    indexedGaussianMean n μ W V D = indexedGaussianMean n μ W
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i)))
      (fun l => Sum.elim (B l) (C l)) := by
  let F := fun g : SharedVertex n→EuclideanSpace ℝ I =>
    Real.log (tiltPartition μ (sharedMarksHamiltonian n W V g) 1)
  have hF : Measurable F := by
    exact (kernel_tiltPartition_measurable (Kernel.const _ μ)
      (sharedMarksHamiltonian_measurable n hW hV)).log
  let b := fun g v => gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  let d := fun g v => gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  have hb : Measurable b := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have he := countableGaussian_covariance_addition_law
    (fun v => B (indexedSharedVertexDepth n v)) (fun v => C (indexedSharedVertexDepth n v))
    (fun v => D (indexedSharedVertexDepth n v)) (fun v => h (indexedSharedVertexDepth n v))
  have hi : (∫ g, F (d g) ∂countableGaussianLaw) = ∫ g, F (b g) ∂countableGaussianLaw := by
    rw [← integral_map hd.aemeasurable hF.aestronglyMeasurable,
      ← integral_map hb.aemeasurable hF.aestronglyMeasurable,he]
  have hf (g) : sharedMarksHamiltonian n W V (d g) =
      countableGaussianHamiltonian W (indexedGaussianRow n D V) (indexedGaussianRowLength (I := I) n) g :=
    funext (sharedMarks_diagonal_eq n W V D g)
  have hg (g) : sharedMarksHamiltonian n W V (b g) =
      countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g :=
    funext (sharedMarks_doubled_eq n W V B C g)
  unfold indexedGaussianMean
  change _ = _ at hi
  simp only [F,hf,hg] at hi
  exact hi

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCovarianceDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
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

lemma countableGaussianCovariance_add_smul {S : Type*}
    (v w z : ℕ → S → ℝ) (L : S → ℕ) (a : ℝ) (x y : S) :
    countableGaussianCovariance (fun i q => v i q+a*w i q) z L x y =
      countableGaussianCovariance v z L x y+a*countableGaussianCovariance w z L x y := by
  have hm (i : ℕ) (q : S) : maskedGaussianCoefficient (fun i q => v i q+a*w i q) L i q =
      maskedGaussianCoefficient v L i q+a*maskedGaussianCoefficient w L i q := by
    unfold maskedGaussianCoefficient
    split_ifs <;> ring
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [hm]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma tiltMean_const_mul_general {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H G : S → ℝ) (a t : ℝ) :
    tiltMean μ H (fun x => a*G x) t = a*tiltMean μ H G t := by
  unfold tiltMean tiltIntegral
  simp_rw [← mul_assoc, mul_comm (Real.exp _) a,mul_assoc,integral_const_mul]
  ring

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x|≤A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E)
variable {B : ℝ} (hB : 0 ≤ B) (hCB : ∀ x y, |countableGaussianCovariance w w L x y| ≤ B)
include hW hv hw hL hA hD hE hB hCB

lemma gaussianCoupling_covariance_continuous :
    Continuous (fun a => ∫ g,
      tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => countableGaussianCovariance w w L x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw) := by
  let H := countableGaussianHamiltonian W v L
  let Y := countableGaussianField w L
  have hH := countableGaussianHamiltonian_measurable hW hv hL
  have hY := countableGaussianField_measurable hw hL
  have he := countableGaussian_all_coupling_exp_ae μ hW hv hw hL hA hD hE
  have hm := countableGaussianCovariance_measurable hw hw hL
  have hdiag : Measurable (fun x => countableGaussianCovariance w w L x x) :=
    hm.comp (measurable_id.prodMk measurable_id)
  have hpair : Measurable (fun x : Fin 2 → S => countableGaussianCovariance w w L (x 1) (x 0)) :=
    hm.comp (show Measurable (fun x : Fin 2 → S => (x 1,x 0)) from by fun_prop)
  have hi (a : ℝ) : Integrable (fun g => tiltMean μ (fun x => H g x+a*Y g x)
      (fun x => countableGaussianCovariance w w L x x) 1) countableGaussianLaw := by
    apply Integrable.of_bound (kernel_tiltMean_measurable (Kernel.const _ μ)
      (H := fun g x => H g x+a*Y g x) (Y := fun _ x => countableGaussianCovariance w w L x x)
      (hH.add (hY.const_mul a)) (hdiag.comp measurable_snd)).aestronglyMeasurable B
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,Kernel.const_apply] using tiltMean_bound_general μ
        (H := fun x => H g x+a*Y g x) (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul a)) hdiag hB (fun x => hCB x x)
  have hj (a : ℝ) : Integrable (fun g => gibbsReplicaMean μ (fun x => H g x+a*Y g x) 2
      (fun x => countableGaussianCovariance w w L (x 1) (x 0))) countableGaussianLaw :=
    kernel_replicaMean_bounded_integrable (Kernel.const _ μ) countableGaussianLaw
      (H := fun g x => H g x+a*Y g x) (G := fun _ x => countableGaussianCovariance w w L (x 1) (x 0))
      (hH.add (hY.const_mul a)) (hpair.comp measurable_snd) hB (fun _ x => hCB _ _)
  change Continuous (fun a => ∫ g, tiltMean μ (fun x => H g x+a*Y g x) _ 1-
    gibbsReplicaMean μ (fun x => H g x+a*Y g x) 2 _ ∂countableGaussianLaw)
  simp_rw [integral_sub (hi _) (hj _)]
  exact (annealedCoupling_tiltMean_continuous countableGaussianLaw μ hH hY hdiag he hB (fun x => hCB x x)).sub
    (annealedCoupling_replicaMean_continuous countableGaussianLaw μ hH hY hpair he hB (fun x => hCB _ _))

theorem gaussianCovariance_right_derivative
    (horth : ∀ x y, countableGaussianCovariance v w L x y=0) :
    HasDerivWithinAt (fun t => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+Real.sqrt t*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      ((∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
          (fun x => countableGaussianCovariance w w L x x) 1 -
        gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
          (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let M := fun a => ∫ g, Real.log (tiltPartition μ (fun x =>
    countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1) ∂countableGaussianLaw
  let C := fun a => ∫ g,
    tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
      (fun x => countableGaussianCovariance w w L x x) 1 -
    gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
      (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw
  have hd (a : ℝ) : HasDerivAt M (a*C a) a := by
    have hh := gaussianCouplingMean_derivative_covariance μ hW hv hw hL hA hD hE a
    simp_rw [countableGaussianCovariance_add_smul,horth,zero_add,
      tiltMean_const_mul_general,gibbsReplicaMean,tiltMean_const_mul_general,← mul_sub,integral_const_mul] at hh
    exact hh
  have hc : Continuous C := gaussianCoupling_covariance_continuous μ hW hv hw hL hA hD hE hB hCB
  simpa only [M,C,zero_mul,add_zero] using sqrt_coupling_right_derivative hd hc

end
variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

omit [DecidableEq I] in
lemma duplicateFeature_measurable {V : S→EuclideanSpace ℝ I} (hV : Measurable V) :
    Measurable (duplicateFeature V) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i with
  | inl i => exact (EuclideanSpace.proj i).measurable.comp hV
  | inr i => exact (EuclideanSpace.proj i).measurable.comp hV

omit [DecidableEq I] [MeasurableSpace S] in
lemma duplicateFeature_square (V : S→EuclideanSpace ℝ I) (s : S) :
    (∑ i, duplicateFeature V s i^2) = 2*∑ i, V s i^2 := by
  rw [Fintype.sum_sum_type]
  simp only [duplicateFeature,Sum.elim_inl,Sum.elim_inr]
  ring

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_orthogonal (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) x y=0 := by
  rw [indexedGaussianRow_covariance,Fintype.sum_sum_type]
  simp [leftCoefficients,rightCoefficients]

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_add_smul (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (a : ℝ) (j : ℕ) (x : S×IndexedLeaf n) :
    indexedGaussianRow n (fun l i => B l i+a*C l i) V j x =
      indexedGaussianRow n B V j x+a*indexedGaussianRow n C V j x := by
  unfold indexedGaussianRow finiteGaussianRow
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedHamiltonian_independent_addition (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B C : Fin (n+1)→I→ℝ) (a : ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    countableGaussianHamiltonian W
      (indexedGaussianRow n (fun l => Sum.elim (B l) (fun i => a*C l i)) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x =
    countableGaussianHamiltonian W
      (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x +
    a*countableGaussianField (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x := by
  have he : (fun l => Sum.elim (B l) (fun i => a*C l i)) =
      fun l i => leftCoefficients n B l i+a*rightCoefficients n C l i := by
    funext l i
    cases i <;> simp [leftCoefficients,rightCoefficients]
  rw [he]
  unfold countableGaussianHamiltonian
  have hr : indexedGaussianRow n (fun l i => leftCoefficients n B l i+a*rightCoefficients n C l i) (duplicateFeature V) =
      fun j x => indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V) j x+
        a*indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V) j x := by
    funext j x
    exact indexedGaussianRow_add_smul n _ _ _ _ _ _
  rw [hr,countableGaussianField_add,countableGaussianField_smul]
  ring

theorem indexedGaussianMean_right_derivative (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0 ≤ D)
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i, V x i^2) ≤ D)
    (B C : Fin (n+1)→I→ℝ) (Q : ℝ→Fin (n+1)→I→ℝ)
    (hQ : ∀ t, 0 ≤ t → ∀ l i, Q t l i^2=B l i^2+t*C l i^2) :
    let v := indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V)
    let w := indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V)
    let L := indexedGaussianRowLength (I := I ⊕ I) (S := S) n
    HasDerivWithinAt (fun t => indexedGaussianMean n μ W V (Q t))
      ((∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
          (fun x => countableGaussianCovariance w w L x x) 1 -
        gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
          (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let v := indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V)
  let w := indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V)
  let L := indexedGaussianRowLength (I := I ⊕ I) (S := S) n
  let E := indexedCoefficientSquare n (rightCoefficients n C)*(2*D)
  have hE0 : 0 ≤ E := mul_nonneg (indexedCoefficientSquare_nonneg n _) (by positivity)
  have hDV (x : S) : (∑ i, duplicateFeature V x i^2) ≤ 2*D := by
    rw [duplicateFeature_square]
    exact mul_le_mul_of_nonneg_left (hD x) (by norm_num)
  have hv := indexedGaussianRow_measurable n (leftCoefficients n B) (duplicateFeature_measurable hV)
  have hw := indexedGaussianRow_measurable n (rightCoefficients n C) (duplicateFeature_measurable hV)
  have hEE : ∀ x, (∑ j : Fin (L x), w j.val x^2) ≤ E := indexedGaussianRow_square_total n _ _ hDV
  have hCB (x y) : |countableGaussianCovariance w w L x y| ≤ E := by
    have hh := gaussianPrefixCovariance_bound w w L hEE hEE (L x) x y
    simpa only [countableGaussianCovariance,add_self_div_two] using hh
  have hd := gaussianCovariance_right_derivative μ hW hv hw
    (indexedGaussianRowLength_measurable n) hA
    (indexedGaussianRow_square_total n (leftCoefficients n B) _ hDV)
    hEE hE0 hCB (indexedGaussianRow_orthogonal n B C V)
  apply hd.congr_of_mem _ (by simp)
  intro t ht
  have he := indexedGaussianMean_covariance_addition n μ hW hV B
    (fun l i => Real.sqrt t*C l i) (Q t) (fun l i => by rw [mul_pow,Real.sq_sqrt ht]; exact hQ t ht l i)
  rw [he]
  unfold indexedGaussianMean
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  funext x
  exact indexedHamiltonian_independent_addition n W V B C (Real.sqrt t) g x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedObservableTransport
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

omit [MeasurableSpace S] in
theorem indexedHamiltonian_integral_covariance_addition
    (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (Ψ : (S×IndexedLeaf n→ℝ)→ℝ)
    (hΨ : Measurable (fun g => Ψ (sharedMarksHamiltonian n W V g)))
    (B C D : Fin (n+1)→I→ℝ) (h : ∀ l i, D l i^2=B l i^2+C l i^2) :
    (∫ g, Ψ (countableGaussianHamiltonian W (indexedGaussianRow n D V)
      (indexedGaussianRowLength (I := I) n) g) ∂countableGaussianLaw) =
    ∫ g, Ψ (countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw := by
  let F := fun g : SharedVertex n→EuclideanSpace ℝ I => Ψ (sharedMarksHamiltonian n W V g)
  have hF : Measurable F := hΨ
  let b := fun g v => gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  let d := fun g v => gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))
    (countableGaussianVectors g v)
  have hb : Measurable b := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (doubledGaussianRows (B (indexedSharedVertexDepth n v)) (C (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro v
    exact (gaussianRows (diagonalGaussianRows (D (indexedSharedVertexDepth n v)))).measurable.comp ((measurable_pi_apply v).comp countableGaussianVectors_measurable)
  have he := countableGaussian_covariance_addition_law
    (fun v => B (indexedSharedVertexDepth n v)) (fun v => C (indexedSharedVertexDepth n v))
    (fun v => D (indexedSharedVertexDepth n v)) (fun v => h (indexedSharedVertexDepth n v))
  have hi : (∫ g, F (d g) ∂countableGaussianLaw) = ∫ g, F (b g) ∂countableGaussianLaw := by
    rw [← integral_map hd.aemeasurable hF.aestronglyMeasurable,
      ← integral_map hb.aemeasurable hF.aestronglyMeasurable,he]
  have hf (g) : sharedMarksHamiltonian n W V (d g) =
      countableGaussianHamiltonian W (indexedGaussianRow n D V) (indexedGaussianRowLength (I := I) n) g :=
    funext (sharedMarks_diagonal_eq n W V D g)
  have hg (g) : sharedMarksHamiltonian n W V (b g) =
      countableGaussianHamiltonian W (indexedGaussianRow n (fun l => Sum.elim (B l) (C l))
      (fun s => WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))))
      (indexedGaussianRowLength (I := I ⊕ I) n) g :=
    funext (sharedMarks_doubled_eq n W V B C g)
  change _ = _ at hi
  simp only [F,hf,hg] at hi
  exact hi


omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_right_covariance (C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf n) :
    countableGaussianCovariance
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) x y =
    countableGaussianCovariance (indexedGaussianRow n C V) (indexedGaussianRow n C V)
      (indexedGaussianRowLength (I := I) n) x y := by
  rw [indexedGaussianRow_covariance,indexedGaussianRow_covariance,Fintype.sum_sum_type]
  simp [rightCoefficients,duplicateFeature]

omit [DecidableEq I] in
lemma indexedResponse_measurable (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V)
    {K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ} (hK : Measurable (Function.uncurry K)) :
    Measurable (fun g => indexedResponse n μ K (sharedMarksHamiltonian n W V g)) := by
  have hKd : Measurable (fun x : S×IndexedLeaf n => K x x) :=
    hK.comp (measurable_id.prodMk measurable_id)
  have hpair : Measurable (fun x : Fin 2→S×IndexedLeaf n => (x 1,x 0)) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 0)
  have hKp : Measurable (fun x : Fin 2→S×IndexedLeaf n => K (x 1) (x 0)) := hK.comp hpair
  exact (kernel_tiltMean_measurable (Kernel.const _ μ)
    (H := sharedMarksHamiltonian n W V) (Y := fun _ x => K x x)
    (sharedMarksHamiltonian_measurable n hW hV) (hKd.comp measurable_snd)).sub
    (kernel_replicaMean_measurable (Kernel.const _ μ)
    (H := sharedMarksHamiltonian n W V) (G := fun _ x => K (x 1) (x 0))
    (sharedMarksHamiltonian_measurable n hW hV) (hKp.comp measurable_snd))

lemma indexedResponse_transport (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V)
    {K : (S×IndexedLeaf n)→(S×IndexedLeaf n)→ℝ} (hK : Measurable (Function.uncurry K))
    (B : Fin (n+1)→I→ℝ) :
    (∫ g, indexedResponse n μ K (countableGaussianHamiltonian W
      (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw) =
      ∫ g, indexedResponse n μ K (countableGaussianHamiltonian W
      (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) g) ∂countableGaussianLaw := by
  exact (indexedHamiltonian_integral_covariance_addition n W V (indexedResponse n μ K)
    (indexedResponse_measurable n μ hW hV hK) B (fun _ _ => 0) B (fun l i => by simp)).symm

theorem indexedGaussianMean_right_response (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0 ≤ D)
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i, V x i^2) ≤ D)
    (B C : Fin (n+1)→I→ℝ) (Q : ℝ→Fin (n+1)→I→ℝ)
    (hQ : ∀ t, 0 ≤ t → ∀ l i, Q t l i^2=B l i^2+t*C l i^2) :
    let v := indexedGaussianRow n B V
    let w := indexedGaussianRow n C V
    let L := indexedGaussianRowLength (I := I) (S := S) n
    HasDerivWithinAt (fun t => indexedGaussianMean n μ W V (Q t))
      ((∫ g, indexedResponse n μ (countableGaussianCovariance w w L)
        (countableGaussianHamiltonian W v L g) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let w := indexedGaussianRow n C V
  let L := indexedGaussianRowLength (I := I) (S := S) n
  have hK : Measurable (Function.uncurry (countableGaussianCovariance w w L)) :=
    countableGaussianCovariance_measurable (indexedGaussianRow_measurable n C hV)
      (indexedGaussianRow_measurable n C hV) (indexedGaussianRowLength_measurable n)
  have hd := indexedGaussianMean_right_derivative n μ hW hV hD0 hA hD B C Q hQ
  dsimp only at hd ⊢
  simp only [indexedGaussianRow_right_covariance] at hd
  change HasDerivWithinAt _ ((∫ g, indexedResponse n μ (countableGaussianCovariance w w L)
    (countableGaussianHamiltonian W (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
    (indexedGaussianRowLength (I := I ⊕ I) n) g) ∂countableGaussianLaw)/2) _ _ at hd
  rw [indexedResponse_transport n μ hW hV hK B] at hd
  exact hd

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceFeature_square_bound (N : ℕ) (p : Fin N→ℕ) (u : Fin N→ℝ) (x : NormalizedSpin N) :
    (∑ i, sourceEnrichedFeature N p u x i^2) ≤ (enrichedFeatureBound N u:ℝ)^2 := by
  have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm N p u x)
  simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le

lemma sourceKernelPressure_gaussianMean_base (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h' h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    (∫ g, sourceKernelPressure n k f p d u h' (a,g) ∂countableGaussianLaw) =
      (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
        (sourceBaseEnergy n k f h a) (sourceEnrichedFeature (n+1) p u)
        (sourceFieldCoefficients p d h')+h (Fin.last k)-h' (Fin.last k) := by
  let W : NormalizedSpin (n+1)×IndexedLeaf k→ℝ := fun x =>
    normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1
  have hW : Measurable W := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have he := indexedGaussianMean_add_const k (sourceSpinLeafKernel n k a) hW
    (sourceEnrichedFeature_measurable (n+1) p u)
    (fun x => normalizedPatternEnergy_bound (n+1) a.1 f _ x.1)
    (sourceFeature_square_bound (n+1) p u) (sourceFieldCoefficients p d h')
    (-((n+1:ℕ)*h (Fin.last k)))
  rw [sourceKernelPressure_gaussianMean]
  change _ = (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
    (fun x => W x+ -((n+1:ℕ)*h (Fin.last k))) (sourceEnrichedFeature (n+1) p u)
    (sourceFieldCoefficients p d h')+h (Fin.last k)-h' (Fin.last k)
  rw [he]
  dsimp only [W]
  field_simp
  ring

theorem sourceConditional_field_right_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    let w := indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u)
    let L := indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) (S := NormalizedSpin (n+1)) k
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      ((1/(n+1:ℕ))*((∫ g, indexedResponse k (sourceSpinLeafKernel n k b)
          (countableGaussianCovariance w w L) (sourceCouplingHamiltonian n k f p d h u (b,g))
        ∂countableGaussianLaw)/2)-a (Fin.last k)) (Ici 0) 0 := by
  have hW := (sourceBaseEnergy_measurable n k f h).of_uncurry_left (x := b)
  have hA := enrichedIndexedBoundedEnergy_bound n b.1 k f (patternPrefix (n+1) b.1 b.2.1) h
  have hd := indexedGaussianMean_right_response k (sourceSpinLeafKernel n k b)
    hW (sourceEnrichedFeature_measurable (n+1) p u) (sq_nonneg (enrichedFeatureBound (n+1) u:ℝ))
    hA (sourceFeature_square_bound (n+1) p u)
    (sourceFieldCoefficients p d h) (sourceDirectionCoefficients p a)
    (fun t => sourceFieldCoefficients p d (fun l => h l+t*a l))
    (fun t ht => sourceFieldCoefficients_affine_covariance p d hh0 hh ha0 ha ht)
  have he := (hd.const_mul (1/(n+1:ℕ):ℝ)).sub
    (((hasDerivAt_id (0:ℝ)).mul_const (a (Fin.last k))).hasDerivWithinAt (s := Ici 0))
  dsimp only at he ⊢
  simp only [one_mul] at he
  apply he.congr
  · intro t ht
    rw [sourceKernelPressure_gaussianMean_base n k f p d u _ h b]
    dsimp only [Pi.sub_apply,id_eq]
    ring
  · rw [sourceKernelPressure_gaussianMean_base n k f p d u _ h b]
    simp only [Pi.sub_apply,id_eq,zero_mul,add_zero,sub_zero]
    ring


lemma sourceFieldObservable_measurable {N k : ℕ} (a : Fin (k+1)→ℝ) :
    Measurable (sourceFieldObservable (N := N) a) := by
  have ht : Measurable (fun x : Fin 2→NormalizedSpin N×IndexedLeaf k => a (indexedCommonDepth k (x 0).2 (x 1).2)) :=
    (Measurable.of_discrete (f := fun x : IndexedLeaf k×IndexedLeaf k => a (indexedCommonDepth k x.1 x.2))).comp
      (((measurable_pi_apply 0).snd).prodMk ((measurable_pi_apply 1).snd))
  have hr : Measurable (fun x : Fin 2→NormalizedSpin N×IndexedLeaf k => spinOverlap (x 1).1 (x 0).1) :=
    (measurable_subtype_coe.comp ((measurable_pi_apply 1).fst)).inner
      (measurable_subtype_coe.comp ((measurable_pi_apply 0).fst))
  exact ht.mul hr

lemma sourceFieldObservable_bound {N k : ℕ} {a : Fin (k+1)→ℝ}
    (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) (x : Fin 2→NormalizedSpin N×IndexedLeaf k) :
    |sourceFieldObservable a x| ≤ a (Fin.last k) := by
  rw [sourceFieldObservable,abs_mul,abs_of_nonneg (ha0 _)]
  exact (mul_le_mul_of_nonneg_left (spinOverlap_abs_le _ _) (ha0 _)).trans
    (by simpa only [mul_one] using ha (Fin.le_last _))

lemma sourceConditional_field_observable_bound (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) (g : ℕ→ℝ) :
    |gibbsReplicaMean (sourceSpinLeafKernel n k b) (sourceCouplingHamiltonian n k f p d h u (b,g)) 2
      (sourceFieldObservable a)| ≤ a (Fin.last k) :=
  tiltMean_bound_general _
    (replicaPotential_measurable (sourceCouplingHamiltonian_section n k f p d h u (b,g)) 2)
    (sourceFieldObservable_measurable a) (ha0 _) (sourceFieldObservable_bound ha0 ha)

lemma sourceConditional_field_observable_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    Integrable (fun g => gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a)) countableGaussianLaw := by
  have hm : Measurable (Function.uncurry (fun g => sourceCouplingHamiltonian n k f p d h u (b,g))) :=
    (sourceCouplingHamiltonian_measurable n k f p d h u).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact kernel_replicaMean_bounded_integrable (Kernel.const _ (sourceSpinLeafKernel n k b)) countableGaussianLaw
    (H := fun g => sourceCouplingHamiltonian n k f p d h u (b,g)) (G := fun _ => sourceFieldObservable a)
    hm ((sourceFieldObservable_measurable a).comp measurable_snd) (ha0 _)
    (fun _ => sourceFieldObservable_bound ha0 ha)

lemma sourceConditional_partition_pos_ae (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    (b : SourceBaseData n k) :
    ∀ᵐ g ∂countableGaussianLaw,
      0 < tiltPartition (sourceSpinLeafKernel n k b) (sourceCouplingHamiltonian n k f p d h u (b,g)) 1 := by
  have he := (countableGaussianHamiltonian_exp_joint_integrable (sourceSpinLeafKernel n k b)
    ((sourceBaseEnergy_measurable n k f h).of_uncurry_left (x := b))
    (indexedGaussianRow_measurable k (sourceFieldCoefficients p d h) (sourceEnrichedFeature_measurable (n+1) p u))
    (indexedGaussianRowLength_measurable k)
    (enrichedIndexedBoundedEnergy_bound n b.1 k f (patternPrefix (n+1) b.1 b.2.1) h)
    (indexedGaussianRow_square_total k (sourceFieldCoefficients p d h) (sourceEnrichedFeature (n+1) p u)
      (sourceFeature_square_bound (n+1) p u)) 1).prod_left_ae
  exact he.mono fun g hg => tilt_partition_pos_of_integrable _ hg

lemma tiltMean_const_of_pos {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H : S→ℝ) (t c : ℝ) (hpos : 0 < tiltPartition μ H t) :
    tiltMean μ H (fun _ => c) t=c := by
  unfold tiltMean tiltIntegral
  rw [integral_mul_const]
  change tiltPartition μ H t*c/tiltPartition μ H t=c
  field_simp

lemma sourceConditional_response_eq (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) (b : SourceBaseData n k) :
    let w := indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u)
    let L := indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) (S := NormalizedSpin (n+1)) k
    (∫ g, indexedResponse k (sourceSpinLeafKernel n k b) (countableGaussianCovariance w w L)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) ∂countableGaussianLaw) =
      2*(n+1:ℕ)*a (Fin.last k)-2*(n+1:ℕ)*(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) ∂countableGaussianLaw) := by
  dsimp only
  have hd (x : NormalizedSpin (n+1)×IndexedLeaf k) : spinOverlap x.1 x.1=1 := by
    have hx : ‖x.1.val‖=1 := by simp
    simp [spinOverlap,hx]
  have he : ∀ᵐ g ∂countableGaussianLaw, indexedResponse k (sourceSpinLeafKernel n k b)
      (countableGaussianCovariance
        (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u))
        (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u))
        (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k))
      (sourceCouplingHamiltonian n k f p d h u (b,g)) =
      2*(n+1:ℕ)*a (Fin.last k)-2*(n+1:ℕ)*gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) := by
    filter_upwards [sourceConditional_partition_pos_ae n k f p d u h b] with g hg
    simp only [indexedResponse,sourceDirection_covariance p u ha0 ha,indexedCommonDepth_self,hd,mul_one]
    rw [tiltMean_const_of_pos _ _ _ _ hg]
    congr 1
    change tiltMean _ _ (fun x : Fin 2→NormalizedSpin (n+1)×IndexedLeaf k => 2*(n+1:ℕ)*a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1) 1 = _
    rw [show (fun x : Fin 2→NormalizedSpin (n+1)×IndexedLeaf k =>
      2*(n+1:ℕ)*a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1) =
      (fun x => (2*(n+1:ℕ))*sourceFieldObservable a x) from funext fun x => by
        unfold sourceFieldObservable
        ring,tiltMean_const_mul_general]
    rfl
  rw [integral_congr_ae he,integral_sub (integrable_const _)
    ((sourceConditional_field_observable_integrable n k f p d u h ha0 ha b).const_mul _),
    integral_const,probReal_univ,one_smul,integral_const_mul]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_FieldArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceFieldPolynomial_eval {k : ℕ} (a : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    (sourceFieldPolynomial a).eval ((l.val:ℝ)/(k+1:ℕ))=a l := by
  unfold sourceFieldPolynomial
  apply Lagrange.eval_interpolate_at_node (s := Finset.univ)
    (v := fun l : Fin (k+1) => (l.val:ℝ)/(k+1:ℕ)) (i := l) a
  · intro i hi j hj he
    apply Fin.ext
    have hv : (i.val:ℝ)=(j.val:ℝ) := (div_left_inj' (by positivity : ((k+1:ℕ):ℝ)≠0)).mp he
    exact_mod_cast hv
  · exact Finset.mem_univ l

lemma sourceGibbsArray_field_integral (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (a : Fin (k+1)→ℝ) :
    (∫ Q, sourceFieldArrayTest a Q ∂sourceGibbsArrayLaw n k f p d h u z t)=
      ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  let F : CompactBlock CompactJointOverlap 2→ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun Q => (sourceFieldPolynomial a).eval (Q 1 0).2.val*(Q 1 0).1.val,by fun_prop⟩
  have he := sourceGibbsArray_block_integral n k f p d h hh0 hh u z t 2 F.measurable
    (fun Q => F.norm_coe_le_norm Q)
  change (∫ Q, sourceFieldArrayTest a Q ∂sourceGibbsArrayLaw n k f p d h u z t)=_ at he
  rw [he]
  apply integral_congr_ae
  exact ae_of_all _ fun b => by
    change gibbsReplicaMean (sourceSpinLeafKernel n k b.1) _ 2 _ = _
    congr 1
    funext x
    dsimp [F,sourceJointOverlap,sourceFieldObservable]
    rw [sourceFieldPolynomial_eval]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RightDerivativeIntegral
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma rightDerivative_translate {F : ℝ→ℝ} {D s : ℝ}
    (hd : HasDerivWithinAt (fun t => F (s+t)) D (Ici 0) 0) :
    HasDerivWithinAt F D (Ici s) s := by
  have hd' : HasDerivWithinAt (fun t => F (s+t)) D (Ici 0) (s-s) := by simpa using hd
  have ht : HasDerivWithinAt (fun t : ℝ => t-s) 1 (Ici s) s := by
    simpa using ((hasDerivAt_id s).sub_const s).hasDerivWithinAt (s := Ici s)
  have hm : MapsTo (fun t : ℝ => t-s) (Ici s) (Ici 0) := by
    intro t ht
    change 0 ≤ t-s
    exact sub_nonneg.mpr (show s ≤ t from ht)
  have he := hd.comp_of_eq s ht hm (by simp)
  simpa only [Function.comp_def,show ∀ x : ℝ, s+(x-s)=x by intro x; ring,mul_one] using he

lemma integral_hasDerivWithinAt_right {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] {F : A→ℝ→ℝ} {D : A→ℝ} {C : ℝ}
    (hF : ∀ t, Integrable (fun a => F a t) μ)
    (hD : ∀ᵐ a ∂μ, HasDerivWithinAt (F a) (D a) (Ici 0) 0)
    (hC : ∀ t, 0 ≤ t → ∀ᵐ a ∂μ, |F a t-F a 0| ≤ C*t) :
    HasDerivWithinAt (fun t => ∫ a, F a t ∂μ) (∫ a, D a ∂μ) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have he (t : ℝ) : slope (fun t => ∫ a, F a t ∂μ) 0 t =
      ∫ a, slope (F a) 0 t ∂μ := by
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,integral_const_mul,integral_sub (hF t) (hF 0)]
  change Tendsto (fun t => slope (fun t => ∫ a, F a t ∂μ) 0 t) _ _
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact Eventually.of_forall fun t => by
      simpa only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,Pi.sub_apply] using ((hF t).sub (hF 0)).aestronglyMeasurable.const_mul t⁻¹
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht.2)
    filter_upwards [hC t ht0.le] with a ha
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos ht0]
    calc
      t⁻¹*|F a t-F a 0| ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr ht0.le)
      _ = C := by field_simp
  · exact integrable_const C
  · exact hD.mono fun a ha => hasDerivWithinAt_iff_tendsto_slope.mp ha

lemma sourceConditional_field_continuous (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (b : SourceBaseData n k) :
    Continuous (fun h => ∫ g, sourceKernelPressure n k f p d u h (b,g) ∂countableGaussianLaw) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun h' => sourceFieldDistance p d u h' h) ?_ ?_
  · intro h'
    simpa only [Real.norm_eq_abs] using sourceConditional_field_comparison n k f p d u h' h b
  · have hc : Tendsto (fun h' => sourceFieldDistance p d u h' h) (𝓝 h)
        (𝓝 (sourceFieldDistance p d u h h)) := (sourceFieldDistance_continuous p d u h).continuousAt
    rwa [sourceFieldDistance_self] at hc

lemma sourceConditional_field_slope (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      (-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) ∂countableGaussianLaw))
      (Ici 0) 0 := by
  have H := sourceConditional_field_right_derivative n k f p d u hh0 hh ha0 ha b
  dsimp only at H
  rw [sourceConditional_response_eq n k f p d u h ha0 ha b] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

lemma sourceConditional_field_slope_at (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      (-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d (fun l => h l+s*a l) u (b,g)) 2
        (sourceFieldObservable a) ∂countableGaussianLaw)) (Ici s) s := by
  apply rightDerivative_translate
  have hd := sourceConditional_field_slope n k f p d u
    (fun l => add_nonneg (hh0 l) (mul_nonneg hs (ha0 l))) (hh.add (ha.const_mul hs)) ha0 ha b
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  have he : (fun l => h l+(s+t)*a l) = (fun l => h l+s*a l+t*a l) := by
    funext l; ring
  rw [he]

lemma sourceConditional_field_direction_bound (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) {s : ℝ} (hs : 0 ≤ s) :
    |(∫ g, sourceKernelPressure n k f p d u (fun l => h l+s*a l) (b,g) ∂countableGaussianLaw)-
      ∫ g, sourceKernelPressure n k f p d u h (b,g) ∂countableGaussianLaw| ≤ a (Fin.last k)*s := by
  have hc : Continuous (fun t : ℝ => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
      ∂countableGaussianLaw) := (sourceConditional_field_continuous n k f p d u b).comp (by fun_prop)
  have hbound (t : ℝ) : ‖-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d (fun l => h l+t*a l) u (b,g)) 2
      (sourceFieldObservable a) ∂countableGaussianLaw)‖ ≤ a (Fin.last k) := by
    rw [norm_neg]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := countableGaussianLaw)
      (ae_of_all _ fun g => show ‖gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d (fun l => h l+t*a l) u (b,g)) 2
        (sourceFieldObservable a)‖ ≤ a (Fin.last k) by
          simpa only [Real.norm_eq_abs] using sourceConditional_field_observable_bound n k f p d u _ ha0 ha b g)
  have he := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
    (fun t ht => sourceConditional_field_slope_at n k f p d u hh0 hh ha0 ha b ht.1)
    (fun t _ => hbound t) s (show s ∈ Icc 0 s from ⟨hs,le_rfl⟩)
  simpa only [zero_mul,add_zero,sub_zero,Real.norm_eq_abs] using he

theorem sourceExpectedPressure_field_right_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    HasDerivWithinAt (fun s => sourceExpectedPressure n k f p d (fun l => h l+s*a l) z t u)
      (-(∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))) (Ici 0) 0 := by
  have hi (s : ℝ) := ((sourceKernelPressure_memLp n k f p d u (fun l => h l+s*a l)
    z hz hz0 hz1 t).integrable (by norm_num))
  have hd := integral_hasDerivWithinAt_right (sourceBaseDataLaw n k z t)
    (fun s => (hi s).integral_prod_left)
    (ae_of_all _ fun b => sourceConditional_field_slope n k f p d u hh0 hh ha0 ha b)
    (C := a (Fin.last k)) (fun s hs => ae_of_all _ fun b => by
      simpa only [zero_mul,add_zero] using
        sourceConditional_field_direction_bound n k f p d u hh0 hh ha0 ha b hs)
  have hI : Integrable (fun b => gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
      (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a))
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) :=
    kernel_replicaMean_bounded_integrable (sourceFullSpinLeafKernel n k) _
      (H := sourceCouplingHamiltonian n k f p d h u) (G := fun _ => sourceFieldObservable a)
      (sourceCouplingHamiltonian_measurable n k f p d h u)
      ((sourceFieldObservable_measurable a).comp measurable_snd)
      (ha0 _) (fun _ => sourceFieldObservable_bound ha0 ha)
  simpa only [sourceExpectedPressure,integral_prod _ (hi _),integral_neg,integral_prod _ hI] using hd

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma source_global_contact_field (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {c : SourceContactParameter n k} (hc : c∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
      (sourceContactCompactDomain n k α H) c) (hcap : c.2.1 (Fin.last k)<H)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤
      ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d c.2.1 c.2.2 b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k (stepCumulative w) c.1).prod countableGaussianLaw) := by
  let L := ∑ i, w i*(q i:ℝ)*a i
  let F : ℝ→ℝ := fun s => -sourceExpectedPressure n k f p d (fun l => c.2.1 l+s*a l)
    (stepCumulative w) c.1 c.2.2-s*L
  let ε := (H-c.2.1 (Fin.last k))/(a (Fin.last k)+1)
  have hε : 0<ε := div_pos (sub_pos.mpr hcap) (by linarith [ha0 (Fin.last k)])
  have hεa : ε*a (Fin.last k) ≤ H-c.2.1 (Fin.last k) := by
    have he : ε*(a (Fin.last k)+1)=H-c.2.1 (Fin.last k) := by
      dsimp [ε]; field_simp [ne_of_gt (show 0<a (Fin.last k)+1 by linarith [ha0 (Fin.last k)])]
    nlinarith
  have hm : IsMinOn F (Icc 0 ε) 0 := by
    intro s hs
    have hc' : (c.1,(fun l => c.2.1 l+s*a l),c.2.2)∈sourceContactCompactDomain n k α H := by
      refine ⟨hc.1,⟨⟨?_,?_⟩,hc.2.1.2.add (ha.const_mul hs.1)⟩,hc.2.2⟩
      · intro i
        exact add_nonneg (hc.2.1.1.1 i) (mul_nonneg hs.1 (ha0 i))
      · intro i
        have hi := hc.2.1.2 (Fin.le_last i)
        have hai : s*a i ≤ ε*a (Fin.last k) :=
          mul_le_mul hs.2 (ha (Fin.le_last i)) (ha0 i) hε.le
        linarith
    have he := hmin hc'
    have hsum : (∑ i, w i*(q i:ℝ)*(c.2.1 i+s*a i))=
        (∑ i, w i*(q i:ℝ)*c.2.1 i)+s*L := by
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros; ring
    change sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ c ≤
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ
        (c.1,(fun l => c.2.1 l+s*a l),c.2.2) at he
    dsimp only [sourceStepContactObjective,sourceJointPressure] at he
    rw [hsum] at he
    change F 0 ≤ F s
    dsimp only [F]
    simp only [zero_mul,add_zero,sub_zero]
    linarith
  let D := ∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
    (sourceCouplingHamiltonian n k f p d c.2.1 c.2.2 b) 2 (sourceFieldObservable a)
    ∂((sourceBaseDataLaw n k (stepCumulative w) c.1).prod countableGaussianLaw)
  have hd : HasDerivWithinAt F (D-L) (Ici 0) 0 := by
    have hp := sourceExpectedPressure_field_right_derivative n k f p d c.2.2 hc.2.1.1.1
      hc.2.1.2 ha0 ha (stepCumulative w) (stepCumulative_strictMono w hw)
      (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) c.1
    convert hp.neg.sub
      (((hasDerivAt_id (0:ℝ)).mul_const L).hasDerivWithinAt (s := Ici 0)) using 1 <;>
      first | rfl | simp [D]
  have hseg : segment ℝ (0:ℝ) ε ⊆ Icc 0 ε := by rw [segment_eq_Icc hε.le]
  have hn := hm.localize.hasFDerivWithinAt_nonneg
    (hd.mono (fun _ hx => hx.1)).hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hseg)
  change 0≤(ε-0)*(D-L) at hn
  change L ≤ D
  nlinarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ContactControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

section Contact
variable (k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))

include hc hmin in

theorem source_global_contact_limit_field_along_oai
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun i => p i.val) (fun i => d i.val)
      (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))
    (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ i, 0≤a i) (ha : Monotone a) :
    (∑ i, w i*(q i:ℝ)*a i) ≤ ∫ Q, sourceFieldArrayTest a Q ∂ν := by
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (sourceFieldArrayTest a)).continuousAt.tendsto.comp hlim
  apply ge_of_tendsto ht
  filter_upwards [hcap] with n hn
  dsimp only [Function.comp_apply]
  rw [sourceGibbsArray_field_integral _ _ _ _ _ _ (hc (s n)).2.1.1.1 (hc (s n)).2.1.2]
  exact source_global_contact_field _ _ _ _ _ _ _ _ hw hw1 _ _ _ (hc (s n)) (hmin (s n))
    hn ha0 ha

end Contact

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.source_global_contact_limit_field_along_oai := @OAI.SphericalPerceptronFreeEnergy.source_global_contact_limit_field_along_oai
