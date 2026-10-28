-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:51.522711+00:00
-- url     : https://prove2.me/submissions/0690042d-6f14-4be8-8ac8-c73bb9a7effb

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

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

lemma tilt_mean_twice {v w F : S → ℝ} (hw : Measurable w)
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ x, |w x| ≤ D) (s t : ℝ) :
    tiltMean (tiltLaw μ w s) v F t = tiltMean μ (fun x => s*w x+t*v x) F 1 := by
  have := tilt_law_probability μ hw hD hwD s
  have hp := (tilt_partition_pos μ hw hD hwD s).ne'
  unfold tiltMean tiltIntegral tiltPartition
  rw [tilt_law_integral μ hw hD hwD s,tilt_law_integral μ hw hD hwD s]
  simp only [tiltMean,tiltIntegral,one_mul,Real.exp_add]
  have he (x : S) : Real.exp (s*w x) * (Real.exp (t*v x)*F x) =
      Real.exp (s*w x) * Real.exp (t*v x) * F x := by ring
  simp_rw [he]
  change ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) * F x ∂μ) / tiltPartition μ w s) /
    ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) ∂μ) / tiltPartition μ w s) = _
  rw [div_div_div_cancel_right₀ hp]

end GibbsProducts

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

section GibbsConvex
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_variance_eq {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    tiltMean μ v (fun x => v x * v x) t - tiltMean μ v v t * tiltMean μ v v t =
      variance v (tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  have hLp : MemLp v 2 (tiltLaw μ v t) := memLp_of_bounded
    (ae_of_all _ fun x => abs_le.mp (hvC x)) hv.aestronglyMeasurable 2
  rw [variance_eq_sub hLp]
  simp_rw [tilt_law_integral μ hv hC hvC t]
  simp only [pow_two]
  rfl

end GibbsConvex

lemma convex_contact_derivative_bound {f A : ℝ → ℝ} {u s d dA C : ℝ}
    (hs : 0 < s) (hf : ConvexOn ℝ Set.univ f) (hd : HasDerivAt f d u)
    (hp : A (u+s)-A u-s*dA ≤ C*s^2)
    (hm : A (u-s)-A u+s*dA ≤ C*s^2) :
    |d-dA| ≤ C*s + (|f (u+s)-A (u+s)| + 2*|f u-A u| + |f (u-s)-A (u-s)|)/s := by
  have hu := hf.le_slope_of_hasDerivAt (Set.mem_univ u) (Set.mem_univ (u+s))
    (by linarith : u < u+s) hd
  have hl := hf.slope_le_of_hasDerivAt (Set.mem_univ (u-s)) (Set.mem_univ u)
    (by linarith : u-s < u) hd
  simp only [slope_def_field] at hu hl
  have he1 : u+s-u = s := by ring
  have he2 : u-(u-s) = s := by ring
  rw [he1,le_div_iff₀ hs] at hu
  rw [he2,div_le_iff₀ hs] at hl
  apply (abs_le).mpr
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [neg_mul,add_mul,div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (u-s)-A (u-s)),neg_abs_le (f u-A u),
      abs_nonneg (f (u+s)-A (u+s)),abs_nonneg (f u-A u)]
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [add_mul,div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (u+s)-A (u+s)),neg_abs_le (f u-A u),
      abs_nonneg (f (u-s)-A (u-s)),abs_nonneg (f u-A u)]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuadraticContactRemainders
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

lemma integral_convex_contact_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ → ℝ} {A : ℝ → ℝ}
    {d : Ω → ℝ} {u s dA C δ : ℝ} (hs : 0 < s)
    (hdm : AEStronglyMeasurable d P)
    (hf : ∀ᵐ ω ∂P, ConvexOn ℝ univ (f ω) ∧ HasDerivAt (f ω) (d ω) u)
    (hp : A (u+s)-A u-s*dA ≤ C*s^2) (hm : A (u-s)-A u+s*dA ≤ C*s^2)
    (hip : Integrable (fun ω => f ω (u+s)) P)
    (hi0 : Integrable (fun ω => f ω u) P)
    (him : Integrable (fun ω => f ω (u-s)) P)
    (hbp : (∫ ω, |f ω (u+s)-A (u+s)| ∂P) ≤ δ)
    (hb0 : (∫ ω, |f ω u-A u| ∂P) ≤ δ)
    (hbm : (∫ ω, |f ω (u-s)-A (u-s)| ∂P) ≤ δ) :
    (∫ ω, |d ω-dA| ∂P) ≤ C*s+4*δ/s := by
  have ip := (hip.sub (integrable_const (A (u+s)))).abs
  have i0 := (hi0.sub (integrable_const (A u))).abs
  have im := (him.sub (integrable_const (A (u-s)))).abs
  let B := fun ω => C*s+(|f ω (u+s)-A (u+s)|+2*|f ω u-A u|+|f ω (u-s)-A (u-s)|)/s
  have hB : Integrable B P := (integrable_const (C*s)).add ((ip.add (i0.const_mul 2) |>.add im).div_const s)
  have hbound : ∀ᵐ ω ∂P, |d ω-dA| ≤ B ω := hf.mono fun ω hω =>
    convex_contact_derivative_bound hs hω.1 hω.2 hp hm
  have hi : Integrable (fun ω => |d ω-dA|) P := hB.mono'
    (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hdm.sub aestronglyMeasurable_const).norm) (hbound.mono fun ω hω => by simpa using hω)
  calc
    _ ≤ ∫ ω, B ω ∂P := integral_mono_ae hi hB hbound
    _ = C*s+((∫ ω, |f ω (u+s)-A (u+s)| ∂P)+
        2*(∫ ω, |f ω u-A u| ∂P)+(∫ ω, |f ω (u-s)-A (u-s)| ∂P))/s := by
      have he := integral_add (integrable_const (C*s)) ((ip.add (i0.const_mul 2) |>.add im).div_const s)
      have he' := integral_add (ip.add (i0.const_mul 2)) im
      have he'' := integral_add ip (i0.const_mul 2)
      simp only [Pi.add_apply,Pi.sub_apply] at he he' he''
      dsimp only [B]
      rw [he,integral_div,he',he'']
      simp [integral_const_mul]
    _ ≤ _ := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hs.le
      linarith

lemma integral_centered_abs_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω-∫ η, X η ∂P| ∂P) ≤ Real.sqrt (variance X P) := by
  have hC : MemLp (fun ω => X ω-∫ η, X η ∂P) 2 P := hX.sub (memLp_const _)
  have hA := hC.norm
  have hv := variance_nonneg (fun ω => |X ω-∫ η, X η ∂P|) P
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs] using hA)] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  rw [← variance_eq_integral hX.aestronglyMeasurable.aemeasurable] at hv
  apply (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) (variance_nonneg X P)).mpr
  linarith

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianRotation
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

lemma integral_sq_ge_sq_integral_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (hμ : 0 < μ.real univ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, (f x)^2 ∂μ := by
  let i := ∫ x, f x ∂μ
  let a := μ.real univ
  have hi := hf.integrable (by norm_num)
  have hi2 := hf.integrable_sq
  have he : (∫ x, (f x-i/a)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ)-2*(i/a)*i+a*(i/a)^2 := by
    calc
      _ = ∫ x, (f x)^2-(2*(i/a))*f x+(i/a)^2 ∂μ := integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
        have ha := integral_add (hi2.sub (hi.const_mul (2*(i/a)))) (integrable_const ((i/a)^2))
        have hb := integral_sub hi2 (hi.const_mul (2*(i/a)))
        simp only [Pi.sub_apply] at ha
        rw [ha,hb,integral_const_mul,integral_const]
        rfl
  have hn : (0 : ℝ) ≤ ∫ x, (f x-i/a)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [he] at hn
  have ha : a ≠ 0 := hμ.ne'
  have hae : a*(i/a)^2 = i^2/a := by field_simp
  have hie : 2*(i/a)*i = 2*(i^2/a) := by ring
  rw [hae,hie] at hn
  have : i^2/a ≤ ∫ x, (f x)^2 ∂μ := by linarith
  exact (div_le_iff₀ hμ).mp this |>.trans_eq (mul_comm ..)

lemma integral_independent_difference_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (∫ p : Ω×Ω, (F p.1-F p.2)^2 ∂μ.prod μ) = 2*variance F μ := by
  have hi := hF.integrable (by norm_num)
  have hi2 := hF.integrable_sq
  have hprod := hi.mul_prod hi
  calc
    _ = ∫ p : Ω×Ω, (F p.1)^2-2*(F p.1*F p.2)+(F p.2)^2 ∂μ.prod μ :=
      integral_congr_ae (ae_of_all _ fun p => by ring)
    _ = _ := by
      have ha := integral_add ((hi2.comp_fst μ).sub (hprod.const_mul 2)) (hi2.comp_snd μ)
      have hb := integral_sub (hi2.comp_fst μ) (hprod.const_mul 2)
      simp only [Pi.sub_apply] at ha
      rw [ha,hb,integral_const_mul,integral_fun_fst (fun x : Ω => (F x)^2),
        integral_fun_snd (fun x : Ω => (F x)^2),
        integral_prod_mul F F,variance_eq_sub hF]
      simp only [probReal_univ,one_smul,Pi.pow_apply]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma dual_rotation_norm (A B : StrongDual ℝ E) (t : ℝ) :
    ‖Real.cos t • A - Real.sin t • B‖^2 + ‖Real.sin t • A + Real.cos t • B‖^2 =
      ‖A‖^2+‖B‖^2 := by
  let e := (InnerProductSpace.toDual ℝ E).symm
  rw [← e.norm_map (Real.cos t • A - Real.sin t • B),
    ← e.norm_map (Real.sin t • A + Real.cos t • B),← e.norm_map A,← e.norm_map B]
  simp only [map_sub,map_add,map_smul,norm_sub_sq_real,norm_add_sq_real,
    real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have h := Real.sin_sq_add_cos_sq t
  nlinarith [sq_nonneg ‖e A‖,sq_nonneg ‖e B‖]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianVectorRotation_apply (t : ℝ) (p : E×E) :
    gaussianVectorRotation t p = (Real.cos t • p.1+Real.sin t • p.2,
      -Real.sin t • p.1+Real.cos t • p.2) := rfl

lemma gaussianVectorRotation_preserving (t : ℝ) :
    MeasurePreserving (gaussianVectorRotation (E := E) t) ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E)) := by
  refine ⟨by fun_prop, Measure.ext_of_charFunDual ?_⟩
  ext L
  rw [charFunDual_map]
  simp only [charFunDual_prod,charFunDual_stdGaussian]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  let A := L.comp (ContinuousLinearMap.inl ℝ E E)
  let B := L.comp (ContinuousLinearMap.inr ℝ E E)
  have hsplit (x y : E) : L (x,y) = L (x,0)+L (0,y) := by
    simpa using L.map_add (x,0) (0,y)
  have ha : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inl ℝ E E) =
      Real.cos t • A - Real.sin t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      smul_apply,sub_apply,gaussianVectorRotation_apply,smul_zero,add_zero]
    rw [hsplit]
    change A (Real.cos t • x) + B (-Real.sin t • x) = _
    simp [sub_eq_add_neg]
  have hb : (L.comp (gaussianVectorRotation t)).comp (ContinuousLinearMap.inr ℝ E E) =
      Real.sin t • A + Real.cos t • B := by
    ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      smul_apply,add_apply,gaussianVectorRotation_apply,smul_zero,zero_add]
    rw [hsplit]
    change A (Real.sin t • x) + B (Real.cos t • x) = _
    simp
  rw [ha,hb]
  have h := dual_rotation_norm A B t
  have hc : (‖Real.cos t • A - Real.sin t • B‖ : ℂ)^2 +
    (‖Real.sin t • A + Real.cos t • B‖ : ℂ)^2 = (‖A‖ : ℂ)^2+(‖B‖ : ℂ)^2 := by
    exact_mod_cast h
  change _ = -(‖A‖ : ℂ)^2/2 + -(‖B‖ : ℂ)^2/2
  linear_combination -hc/2

lemma stdGaussian_dual_secondMoment (L : StrongDual ℝ E) :
    (∫ x, (L x)^2 ∂stdGaussian E) = ‖L‖^2 := by
  have hm : MemLp L 2 (stdGaussian E) := IsGaussian.memLp_dual _ _ 2 (by simp)
  have h := variance_eq_sub hm
  rw [integral_strongDual_stdGaussian,zero_pow (by omega),sub_zero,
    variance_dual_stdGaussian] at h
  exact h.symm

lemma hasFDerivAt_bounded_gaussian_memLp {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) {C : ℝ} (hC : 0 ≤ C)
    (hDC : ∀ x, ‖D x‖ ≤ C) : MemLp F 2 (stdGaussian E) := by
  have hL : LipschitzWith ⟨C,hC⟩ F := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hF x).differentiableAt) (fun x => by
      rw [(hF x).fderiv]
      exact_mod_cast hDC x)
  have hgc : LipschitzWith ⟨C,hC⟩ (fun x => F x-F 0) := by
    intro x y
    simpa only [edist_sub_right] using hL x y
  have hg := hgc.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) 2 (by simp))
  have hh := hg.add (memLp_const (F 0))
  have he : ((fun x => F x-F 0) ∘ id + fun _ => F 0) = F := by
    funext x
    simp
  rw [he] at hh
  convert! hh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_vector_rotation_path_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D) (x y : E) :
    (F y-F x)^2 ≤ (Real.pi/2) * ∫ t in Ioc 0 (Real.pi/2),
      (D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y))^2 := by
  let d := fun t => D (Real.cos t • x+Real.sin t • y) (-Real.sin t • x+Real.cos t • y)
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hdF (t : ℝ) : HasDerivAt (fun t => F (Real.cos t • x+Real.sin t • y)) (d t) t := by
    exact (hF _).comp_hasDerivAt t (((Real.hasDerivAt_cos t).smul_const x).add
      ((Real.hasDerivAt_sin t).smul_const y))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hdF t) (hd.intervalIntegrable 0 (Real.pi/2))
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Real.cos_zero,Real.sin_zero,
    zero_smul,one_smul,zero_add,add_zero] at hi
  rw [intervalIntegral.integral_of_le (by positivity)] at hi
  have hm : MemLp d 2 (volume.restrict (Ioc 0 (Real.pi/2))) :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
      ((hd.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hmass : (volume.restrict (Ioc 0 (Real.pi/2))).real univ = Real.pi/2 := by
    simp [Measure.real,Real.volume_Ioc]; positivity
  have hh := integral_sq_ge_sq_integral_div (volume.restrict (Ioc 0 (Real.pi/2)))
    hm (by rw [hmass]; positivity)
  rw [hmass,hi] at hh
  exact hh

lemma gaussian_vector_rotation_derivative_square_mean {D : E → StrongDual ℝ E}
    (hD : Continuous D) {C : ℝ} (hDC : ∀ x, ‖D x‖ ≤ C) (t : ℝ) :
    (∫ p : E × E,
      (D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2))^2
      ∂(stdGaussian E).prod (stdGaussian E)) =
      ∫ x, ‖D x‖^2 ∂stdGaussian E := by
  have he := integral_map (μ := (stdGaussian E).prod (stdGaussian E))
    (gaussianVectorRotation t).continuous.measurable.aemeasurable
    (f := fun p : E×E => (D p.1 p.2)^2) (by fun_prop)
  rw [(gaussianVectorRotation_preserving t).map_eq] at he
  dsimp only [gaussianVectorRotation_apply] at he
  rw [← he]
  have hi : Integrable (fun p : E×E => (D p.1 p.2)^2) ((stdGaussian E).prod (stdGaussian E)) := by
    have hh := ((IsGaussian.memLp_id (stdGaussian E) 2 (by simp)).norm.integrable_sq.const_mul (C^2)).comp_snd (stdGaussian E)
    apply hh.mono' (by fun_prop)
    refine ae_of_all _ fun p => ?_
    have hC : 0 ≤ C := (norm_nonneg (D p.1)).trans (hDC _)
    have hh : |D p.1 p.2| ≤ C*‖p.2‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDC _) (norm_nonneg _))
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (norm_nonneg p.2))).mpr hh
    simpa only [Real.norm_eq_abs,abs_sq,sq_abs,mul_pow,id_eq] using hh2
  rw [integral_prod _ hi]
  congr 1
  funext x
  exact stdGaussian_dual_secondMoment (D x)

lemma stdGaussian_poincare {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*(∫ x, ‖D x‖^2 ∂stdGaussian E) := by
  let γ := stdGaussian E
  let μ := γ.prod γ
  let T := Real.pi/2
  let ν := volume.restrict (Ioc 0 T)
  let d := fun (t : ℝ) (p : E×E) =>
    D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)
  have hT : 0 < T := by dsimp [T]; positivity
  have hν : ν.real univ = T := by simp [ν,Measure.real,Real.volume_Ioc,hT.le]
  have hdom (t : ℝ) (p : E×E) : (d t p)^2 ≤ 2*C^2*(‖p.1‖^2+‖p.2‖^2) := by
    have hb : ‖-Real.sin t • p.1+Real.cos t • p.2‖ ≤ ‖p.1‖+‖p.2‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t,norm_nonneg p.1])
        (by nlinarith [Real.abs_cos_le_one t,norm_nonneg p.2])
    have hh : |d t p| ≤ C*(‖p.1‖+‖p.2‖) := by
      change ‖D (Real.cos t • p.1+Real.sin t • p.2) (-Real.sin t • p.1+Real.cos t • p.2)‖ ≤ _
      apply (ContinuousLinearMap.le_opNorm _ _).trans
      exact mul_le_mul (hDC _) hb (norm_nonneg _) hC
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ C*(‖p.1‖+‖p.2‖))).mpr hh
    simp only [sq_abs,mul_pow] at hh2
    have hh3 := mul_nonneg (sq_nonneg C) (sq_nonneg (‖p.1‖-‖p.2‖))
    nlinarith
  have hs : Integrable (fun x : E => ‖x‖^2) γ :=
    (IsGaussian.memLp_id γ 2 (by simp)).norm.integrable_sq
  have hdI : Integrable (fun p : (E×E)×ℝ => (d p.2 p.1)^2) (μ.prod ν) := by
    have hh : Integrable (fun p : (E×E)×ℝ => 2*C^2*(‖p.1.1‖^2+‖p.1.2‖^2)) (μ.prod ν) :=
      (((hs.comp_fst γ).add (hs.comp_snd γ)).const_mul (2*C^2)).comp_fst ν
    apply hh.mono' (by dsimp [d]; fun_prop)
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,abs_sq] using hdom p.2 p.1
  have hmF : MemLp F 2 γ := hasFDerivAt_bounded_gaussian_memLp hF hC hDC
  have hdiff : Integrable (fun p : E×E => (F p.2-F p.1)^2) μ := by
    simpa only [Pi.sub_apply] using ((hmF.comp_snd γ).sub (hmF.comp_fst γ)).integrable_sq
  have he : (∫ p : E×E, (F p.2-F p.1)^2 ∂μ) = 2*variance F γ := by
    rw [show (fun p : E×E => (F p.2-F p.1)^2) = fun p => (F p.1-F p.2)^2 by
      funext p; ring]
    exact integral_independent_difference_square γ hmF
  have hn := integral_mono_ae hdiff (hdI.integral_prod_left.const_mul T)
    (ae_of_all _ fun p => gaussian_vector_rotation_path_bound hF hD p.1 p.2)
  rw [he,integral_const_mul,← integral_prod _ hdI,integral_prod_symm _ hdI] at hn
  have hmeans : (∫ t, ∫ p : E×E, (d t p)^2 ∂μ ∂ν) =
      T*(∫ x, ‖D x‖^2 ∂γ) := by
    simp_rw [show ∀ t, (∫ p : E×E, (d t p)^2 ∂μ) = ∫ x, ‖D x‖^2 ∂γ
      from fun t => gaussian_vector_rotation_derivative_square_mean hD hDC t]
    rw [integral_const,hν,smul_eq_mul]
  rw [hmeans] at hn
  dsimp only [T] at hn
  nlinarith

lemma stdGaussian_variance_le_of_fderiv_bound {F : E → ℝ} {D : E → StrongDual ℝ E}
    (hF : ∀ x, HasFDerivAt F (D x) x) (hD : Continuous D)
    {C : ℝ} (hC : 0 ≤ C) (hDC : ∀ x, ‖D x‖ ≤ C) :
    variance F (stdGaussian E) ≤ (Real.pi^2/8)*C^2 := by
  apply (stdGaussian_poincare hF hD hC hDC).trans
  gcongr
  calc
    _ ≤ ∫ _ : E, C^2 ∂stdGaussian E :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
        (ae_of_all _ fun x => (sq_le_sq₀ (norm_nonneg _) hC).mpr (hDC x))
    _ = C^2 := by simp

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorPartition ρ W V) (∫ s, Real.exp (W s+V s x) • V s ∂ρ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
    (F' := fun y s => Real.exp (W s+V s y) • V s) (Metric.ball_mem_nhds x zero_lt_one)
    (Filter.Eventually.of_forall fun y => by fun_prop)
    (vectorPartition_integrable ρ hWm hVm hW hV x) (by fun_prop)
    (ae_of_all _ fun s y hy => ?_) (integrable_const _) (ae_of_all _ fun s y _ => ?_)
  · have hy' : ‖y‖ ≤ ‖x‖+1 := by
      have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hn := norm_add_le (y-x) x
      rw [sub_add_cancel] at hn
      linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact (((V s).hasFDerivAt).const_add (W s)).exp

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_hasFDerivAt (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    HasFDerivAt (vectorLogPartition ρ W V) (vectorLogDerivative ρ W V x) x :=
  (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).log
    (vectorPartition_pos ρ hWm hVm hW hV x).ne'

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogDerivative_bound (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    ‖vectorLogDerivative ρ W V x‖ ≤ C := by
  have hp := vectorPartition_pos ρ hWm hVm hW hV x
  have hn : ‖∫ s, Real.exp (W s+V s x) • V s ∂ρ‖ ≤ C*vectorPartition ρ W V x := by
    have hh := norm_integral_le_of_norm_le (f := fun s => Real.exp (W s+V s x) • V s)
      ((vectorPartition_integrable ρ hWm hVm hW hV x).const_mul C)
      (ae_of_all _ fun s => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_left (hV s) (Real.exp_pos _).le).trans_eq (mul_comm ..))
    simpa only [integral_const_mul,vectorPartition] using hh
  rw [vectorLogDerivative,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (vectorPartition ρ W V x)⁻¹*(C*vectorPartition ρ W V x) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    _ = C := by field_simp

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogDerivative_continuous (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    Continuous (vectorLogDerivative ρ W V) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp := (vectorPartition_hasFDerivAt ρ hWm hVm hC hW hV x).continuousAt
  apply (hp.inv₀ (vectorPartition_pos ρ hWm hVm hW hV x).ne').smul
  apply continuousAt_of_dominated (bound := fun _ => Real.exp (K+C*(‖x‖+1))*C)
  · exact Filter.Eventually.of_forall fun y => by fun_prop
  · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact ae_of_all _ fun s => by
      have hy' : ‖y‖ ≤ ‖x‖+1 := by
        have hh : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
        have hn := norm_add_le (y-x) x
        rw [sub_add_cancel] at hn
        linarith
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul _ (hV _) (norm_nonneg _) (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      exact ((le_abs_self _).trans (vectorEnergy_bound hW hV y s)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hC))
  · exact integrable_const _
  · exact ae_of_all _ fun s => by fun_prop

lemma vectorLogPartition_gaussian_variance (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hC : 0 ≤ C) (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    variance (vectorLogPartition ρ W V) (stdGaussian E) ≤ (Real.pi^2/8)*C^2 :=
  stdGaussian_variance_le_of_fderiv_bound
    (vectorLogPartition_hasFDerivAt ρ hWm hVm hC hW hV)
    (vectorLogDerivative_continuous ρ hWm hVm hC hW hV) hC
    (vectorLogDerivative_bound ρ hWm hVm hW hV)

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

section ProductVariance
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y] in
lemma continuous_integral_of_bounded {F : X × Y → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : ∀ p, |F p| ≤ K) :
    Continuous (fun x => ∫ y, F (x, y) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => K)
  · intro x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => hK (x, y))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun y =>
      hF.comp (continuous_id.prodMk continuous_const)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] in
lemma abs_integral_of_bounded {F : X × Y → ℝ} {K : ℝ} (hK : ∀ p, |F p| ≤ K)
    (x : X) : |∫ y, F (x, y) ∂ν| ≤ K := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (f := fun y => F (x, y))
    (Filter.Eventually.of_forall fun y => hK (x, y))

lemma variance_prod_le {F : X × Y → ℝ} (hF : Continuous F)
    {K A B : ℝ} (hK : ∀ p, |F p| ≤ K)
    (hA : ∀ x, variance (fun y => F (x, y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x, y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A + B := by
  have hp : MemLp F 2 (μ.prod ν) :=
    MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
  have hs (x : X) : MemLp (fun y => F (x, y)) 2 ν :=
    MemLp.of_bound (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      K (Filter.Eventually.of_forall fun y => hK (x, y))
  have hh : MemLp (fun x => ∫ y, F (x, y) ∂ν) 2 μ :=
    MemLp.of_bound (continuous_integral_of_bounded ν hF hK).aestronglyMeasurable K
      (Filter.Eventually.of_forall (abs_integral_of_bounded ν hK))
  have hi : (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + ∫ x, (∫ y, F (x, y) ∂ν) ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x, (A + (∫ y, F (x, y) ∂ν) ^ 2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using (sub_le_iff_le_add.mp hv)
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  simpa only [Pi.pow_apply] using sub_le_iff_le_add.mpr (by linarith :
    (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + B + (∫ x, ∫ y, F (x, y) ∂ν ∂μ) ^ 2)

end ProductVariance

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [SecondCountableTopology X] in
lemma variance_le_of_oscillation {F : X → ℝ} (hF : Continuous F) {c : ℝ}
    (hosc : ∀ x y, |F x - F y| ≤ c) : variance F μ ≤ c ^ 2 := by
  let x₀ : X := Classical.choice ‹Nonempty X›
  have hbound : ∀ᵐ x ∂μ, F x ∈ Icc (F x₀ - c) (F x₀ + c) := by
    apply Filter.Eventually.of_forall
    intro x
    have hh := abs_le.mp (hosc x x₀)
    constructor <;> linarith
  have hv := variance_le_sq_of_bounded hbound hF.measurable.aemeasurable
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma continuous_fin_cons {n : ℕ} :
    Continuous (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous (fun p : X × (Fin n → X) => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp
      (continuous_snd : Continuous (fun p : X × (Fin n → X) => p.2))

omit [BorelSpace X] [Nonempty X] in
lemma measurePreserving_fin_cons (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma measurableEmbedding_fin_cons (n : ℕ) :
    MeasurableEmbedding (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurableEmbedding
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

theorem variance_pi_le_of_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
    (hF : Continuous F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
    (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
    variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2 := by
  classical
  induction n with
  | zero =>
      rw [Measure.pi_of_empty]
      simp
  | succ n ih =>
      let ν := Measure.pi fun _ : Fin n => μ
      let G : X × (Fin n → X) → ℝ := fun p => F (Fin.cons (α := fun _ => X) p.1 p.2)
      have hG : Continuous G := hF.comp continuous_fin_cons
      have hGK (p) : |G p| ≤ K := hK _
      have hA (x : X) : variance (fun y => G (x, y)) ν ≤ (n : ℝ) * c ^ 2 := by
        apply ih (hG.comp (continuous_const.prodMk continuous_id)) (fun y => hGK (x,y))
        intro y i z
        simpa only [G, Function.comp_apply, id_eq, Fin.cons_update] using hdiff (Fin.cons x y) i.succ z
      have hHc : Continuous (fun x => ∫ y, G (x, y) ∂ν) :=
        continuous_integral_of_bounded ν hG hGK
      have hHosc (x x' : X) :
          |(∫ y, G (x, y) ∂ν) - ∫ y, G (x', y) ∂ν| ≤ c := by
        have hi (x : X) : Integrable (fun y => G (x, y)) ν :=
          (integrable_const K).mono'
            (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => hGK (x, y))
        rw [← integral_sub (hi x) (hi x')]
        have hh : ∀ y, |G (x, y) - G (x', y)| ≤ c := by
          intro y
          have hu : Function.update (Fin.cons x' y) 0 x = Fin.cons (α := fun _ => X) x y := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [G, hu] using hdiff (Fin.cons x' y) 0 x
        simpa using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun y => G (x,y) - G (x',y))
          (Filter.Eventually.of_forall hh)
      have hv := variance_prod_le μ ν hG hGK hA
        (variance_le_of_oscillation μ hHc hHosc)
      have hpF : MemLp F 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
        MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
      have hpG : MemLp G 2 (μ.prod ν) :=
        MemLp.of_bound hG.aestronglyMeasurable K (Filter.Eventually.of_forall hGK)
      rw [variance_eq_sub hpG] at hv
      rw [variance_eq_sub hpF]
      have hmean := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) F
      have hsquare := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) (fun x => F x ^ 2)
      change (∫ x, G x ∂μ.prod ν) = _ at hmean
      change (∫ x, G x ^ 2 ∂μ.prod ν) = _ at hsquare
      simp only [Pi.pow_apply] at hv ⊢
      rw [hsquare, hmean] at hv
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hv

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
section GeneralProductVariance
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma variance_prod_le_memLp {F : X × Y → ℝ}
    (hp : MemLp F 2 (μ.prod ν)) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A B : ℝ}
    (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ A+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  linarith

end GeneralProductVariance

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_data_bound {W W' : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hWm' : Measurable W') (hVm : Measurable V) {K K' C c : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hW' : ∀ s, |W' s| ≤ K') (hV : ∀ s, ‖V s‖ ≤ C)
    (hWc : ∀ s, |W s-W' s| ≤ c) (x : E) :
    |vectorLogPartition ρ W V x-vectorLogPartition ρ W' V x| ≤ c := by
  exact abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm' hVm hW' hV x)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm' hVm hW' hV x)
    (fun s => by simpa only [add_sub_add_right_eq_sub] using hWc s)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma vectorLogPartition_mixed_variance (n : ℕ)
    {W : (Fin n → X) → S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable (Function.uncurry W)) (hWc : ∀ s, Continuous (fun p => W p s))
    (hVm : Measurable V) {K C c : ℝ} (hC : 0 ≤ C)
    (hW : ∀ p s, |W p s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (hosc : ∀ p i z s, |W (Function.update p i z) s-W p s| ≤ c) :
    variance (fun p => vectorLogPartition ρ (W p.1) V p.2)
      ((Measure.pi fun _ : Fin n => μ).prod (stdGaussian E)) ≤
      Real.pi^2/8*C^2+(n:ℝ)*c^2 := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let γ := stdGaussian E
  let F := fun (p : Fin n → X) (g : E) => vectorLogPartition ρ (W p) V g
  have hWm' (p) : Measurable (W p) := hWm.comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable (Function.uncurry F) := by
    have hm : Measurable (fun p : ((Fin n → X)×E)×S =>
        Real.exp (W p.1.1 p.2+V p.2 p.1.2)) := by
      apply Measurable.exp
      exact (hWm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).add
        (((continuous_fst.clm_apply continuous_snd : Continuous
          (fun p : StrongDual ℝ E × E => p.1 p.2)).measurable).comp
          ((hVm.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable.log
  have hFB (p) (g) : |F p g| ≤ K+C*‖g‖ :=
    vectorLogPartition_bound ρ (hWm' p) hVm (hW p) hV g
  have hGB : MemLp (fun g : E => K+C*‖g‖) 2 γ := by
    exact (memLp_const K).add ((IsGaussian.memLp_id γ 2 (by simp)).norm.const_mul C)
  have hFL (p) : MemLp (F p) 2 γ := hGB.mono'
    ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g)
  have hFp (g : E) : Continuous (fun p => F p g) := by
    have hp : Continuous (fun p => vectorPartition ρ (W p) V g) := by
      apply continuous_of_dominated (bound := fun _ => Real.exp (K+C*‖g‖))
      · intro p; exact (vectorPartition_integrable ρ (hWm' p) hVm (hW p) hV g).aestronglyMeasurable
      · intro p; apply ae_of_all; intro s
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound (hW p) hV g s))
      · exact integrable_const _
      · exact ae_of_all _ fun s => ((hWc s).add continuous_const).rexp
    exact hp.log (fun p => (vectorPartition_pos ρ (hWm' p) hVm (hW p) hV g).ne')
  have hAc : Continuous (fun p => ∫ g, F p g ∂γ) := by
    apply continuous_of_dominated (bound := fun g => K+C*‖g‖)
    · intro p; exact (hFL p).aestronglyMeasurable
    · intro p; exact ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hFB p g
    · exact hGB.integrable (by norm_num)
    · exact ae_of_all _ hFp
  have hAB (p) : |∫ g, F p g ∂γ| ≤ ∫ g, (K+C*‖g‖) ∂γ := by
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono (hFL p |>.integrable (by norm_num) |>.norm)
        (hGB.integrable (by norm_num)) (fun g => by simpa only [Real.norm_eq_abs] using hFB p g))
  have hAL : MemLp (fun p => ∫ g, F p g ∂γ) 2 ν :=
    MemLp.of_bound hAc.aestronglyMeasurable _ (ae_of_all _ hAB)
  apply variance_prod_le_memLp ν γ
    ((hGB.comp_snd ν).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs,Function.uncurry] using hFB p.1 p.2)) hFL hAL
  · intro p
    exact vectorLogPartition_gaussian_variance ρ (hWm' p) hVm hC (hW p) hV
  · apply variance_pi_le_of_bounded_differences μ n hAc hAB
    intro p i z
    rw [← integral_sub ((hFL _).integrable (by norm_num)) ((hFL _).integrable (by norm_num))]
    have hh := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun g => F (Function.update p i z) g-F p g) (C := c)
      (ae_of_all _ fun g => by
        simpa only [Real.norm_eq_abs] using vectorLogPartition_data_bound ρ
          (hWm' _) (hWm' _) hVm (hW _) (hW _) hV (hosc p i z) g)
    simpa using hh

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

lemma affineMean_deriv {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    HasDerivAt (fun u => tiltMean μ (fun x => H x+u*Y x) Y 1)
      (tiltMean μ (fun x => H x+t*Y x) (fun x => Y x*Y x) 1 -
        (tiltMean μ (fun x => H x+t*Y x) Y 1)^2) t := by
  have := tilt_law_probability μ hH hA hHA 1
  have hh := tilt_mean_deriv (tiltLaw μ H 1) hY hY hB hB hYB hYB t
  have he : tiltMean (tiltLaw μ H 1) Y Y = (fun u => tiltMean μ (fun x => H x+u*Y x) Y 1) := by
    funext u
    simpa only [one_mul] using tilt_mean_twice μ (v := Y) (F := Y) hH hA hHA 1 u
  rw [he] at hh
  simpa only [tilt_mean_twice μ hH hA hHA,one_mul,pow_two] using hh

omit [MeasurableSpace S] in
lemma affinePotential_bound {H Y : S → ℝ} {A B : ℝ}
    (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) (x : S) :
    |H x+t*Y x| ≤ A+|t| * B := by
  exact (abs_add_le _ _).trans (add_le_add (hHA x) (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYB x) (abs_nonneg t)))

end

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]

lemma thermalVar_nonneg {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) : 0 ≤ thermalVar μ H Y t := by
  have := tilt_law_probability μ hH hA hHA 1
  have he := tilt_variance_eq (tiltLaw μ H 1) hY hB hYB t
  have he' : thermalVar μ H Y t = variance Y (tiltLaw (tiltLaw μ H 1) Y t) := by
    simpa only [thermalVar,tilt_mean_twice μ hH hA hHA,one_mul,pow_two] using he
  rw [he']
  exact variance_nonneg Y _

lemma thermalVar_bound {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) : |thermalVar μ H Y t| ≤ 2*B^2 := by
  have h0 := tilt_mean_bound μ (hH.add (hY.const_mul t)) hY
    (add_nonneg hA (mul_nonneg (abs_nonneg _) hB)) hB (affinePotential_bound hHA hYB t) hYB 1
  have h2 := tilt_mean_bound μ (hH.add (hY.const_mul t)) (hY.mul hY)
    (add_nonneg hA (mul_nonneg (abs_nonneg _) hB)) (sq_nonneg B)
    (affinePotential_bound hHA hYB t) (fun x => by
      simp only [Pi.mul_apply]
      rw [abs_mul,pow_two]; exact mul_le_mul (hYB x) (hYB x) (abs_nonneg _) hB) 1
  simp only [Pi.add_def,Pi.mul_def] at h0 h2
  have hs : |(tiltMean μ (fun x => H x+t*Y x) Y 1)^2| ≤ B^2 := by
    rw [abs_sq]
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hB] using h0)
  unfold thermalVar
  exact (abs_sub _ _).trans (by linarith)

lemma measurable_affineMean {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (t : ℝ) :
    Measurable (fun ω => tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1) :=
  measurable_tiltMean_param μ (hH.add (hY.const_mul t)) hY

lemma measurable_thermalVar {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (t : ℝ) :
    Measurable (fun ω => thermalVar μ (H ω) (Y ω) t) := by
  exact (measurable_tiltMean_param μ (hH.add (hY.const_mul t)) (hY.mul hY)).sub
    ((measurable_affineMean μ hH hY t).pow_const 2)

omit [IsProbabilityMeasure P] in
lemma annealedAffineMean_deriv {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hBI : Integrable B P) (hB2 : Integrable (fun ω => (B ω)^2) P) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, tiltMean μ (fun x => H ω x+u*Y ω x) (Y ω) 1 ∂P)
      (∫ ω, thermalVar μ (H ω) (Y ω) t ∂P) t := by
  have hHm (ω) : Measurable (H ω) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun ω => tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1) P := by
    apply hBI.mono' (measurable_affineMean μ hH hY t).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs,Pi.add_def] using tilt_mean_bound μ
        ((hHm ω).add ((hYm ω).const_mul t)) (hYm ω)
        (add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))) (hB ω)
        (affinePotential_bound (hHA ω) (hYB ω) t) (hYB ω) 1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (s := Set.univ) (bound := fun ω => 2*(B ω)^2) (F' := fun u ω => thermalVar μ (H ω) (Y ω) u)
    (by simp) (Eventually.of_forall fun u => (measurable_affineMean μ hH hY u).aestronglyMeasurable)
    hi (measurable_thermalVar μ hH hY t).aestronglyMeasurable
    (ae_of_all _ fun ω u _ => by
      simpa only [Real.norm_eq_abs] using thermalVar_bound μ (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u)
    (hB2.const_mul 2) (ae_of_all _ fun ω u _ => affineMean_deriv μ
      (hHm ω) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) u)).2

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

lemma tilt_mean_centered_abs_sq_le {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B) :
    (tiltMean μ H (fun x => |Y x-tiltMean μ H Y 1|) 1)^2 ≤
      tiltMean μ H (fun x => Y x*Y x) 1-(tiltMean μ H Y 1)^2 := by
  have := tilt_law_probability μ hH hA hHA 1
  let ν := tiltLaw μ H 1
  have hLp : MemLp Y 2 ν := MemLp.of_bound hY.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hYB x)
  have hh := integral_centered_abs_le_sqrt_variance ν hLp
  have hnon : 0 ≤ ∫ x, |Y x-∫ y, Y y ∂ν| ∂ν := integral_nonneg fun _ => abs_nonneg _
  have hsq := pow_le_pow_left₀ hnon hh 2
  rw [Real.sq_sqrt (variance_nonneg Y ν),variance_eq_sub hLp] at hsq
  simp only [Pi.pow_apply] at hsq
  change (∫ x, |Y x-∫ y, Y y ∂tiltLaw μ H 1| ∂tiltLaw μ H 1)^2 ≤
    (∫ x, (Y x)^2 ∂tiltLaw μ H 1) - (∫ x, Y x ∂tiltLaw μ H 1)^2 at hsq
  simp_rw [tilt_law_integral μ hH hA hHA 1] at hsq
  simpa only [pow_two] using hsq

omit [IsProbabilityMeasure μ] in
lemma tiltMean_nonneg {H F : S → ℝ} (hF : ∀ x, 0 ≤ F x) (t : ℝ) : 0 ≤ tiltMean μ H F t := by
  exact div_nonneg (integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (hF x))
    (integral_nonneg fun _ => (Real.exp_pos _).le)

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma annealed_thermal_abs_sq_le {H Y : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω → ℝ} (hA : ∀ ω, 0 ≤ A ω) (hB : ∀ ω, 0 ≤ B ω)
    (hHA : ∀ ω x, |H ω x| ≤ A ω) (hYB : ∀ ω x, |Y ω x| ≤ B ω)
    (hB2 : MemLp B 2 P) (t : ℝ) :
    (∫ ω, tiltMean μ (fun x => H ω x+t*Y ω x)
      (fun x => |Y ω x-tiltMean μ (fun x => H ω x+t*Y ω x) (Y ω) 1|) 1 ∂P)^2 ≤
        ∫ ω, thermalVar μ (H ω) (Y ω) t ∂P := by
  let T := fun ω x => H ω x+t*Y ω x
  let M := fun ω => tiltMean μ (T ω) (Y ω) 1
  let U := fun ω => tiltMean μ (T ω) (fun x => |Y ω x-M ω|) 1
  have hT : Measurable (Function.uncurry T) := hH.add (hY.const_mul t)
  have hM : Measurable M := measurable_tiltMean_param μ hT hY
  have hU : Measurable U := measurable_tiltMean_param μ hT ((hY.sub (hM.comp measurable_fst)).abs)
  have hTm (ω) : Measurable (T ω) := hT.comp (measurable_const.prodMk measurable_id)
  have hYm (ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hTB (ω x) : |T ω x| ≤ A ω+|t| * B ω := affinePotential_bound (hHA ω) (hYB ω) t x
  have hTp (ω) : 0 ≤ A ω+|t| * B ω := add_nonneg (hA ω) (mul_nonneg (abs_nonneg _) (hB ω))
  have hMB (ω) : |M ω| ≤ B ω := tilt_mean_bound μ (hTm ω) (hYm ω) (hTp ω) (hB ω) (hTB ω) (hYB ω) 1
  have hUB (ω) : |U ω| ≤ 2*B ω := by
    apply tilt_mean_bound μ (hTm ω) ((hYm ω).sub_const (M ω) |>.abs) (hTp ω) (mul_nonneg (by norm_num) (hB ω)) (hTB ω) _ 1
    intro x
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith [hYB ω x,hMB ω])
  have hULp : MemLp U 2 P := (hB2.const_mul 2).mono' hU.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hUB ω)
  have hv := variance_nonneg U P
  rw [variance_eq_sub hULp] at hv
  have hIvar : Integrable (fun ω => thermalVar μ (H ω) (Y ω) t) P :=
    ((memLp_two_iff_integrable_sq hB2.aestronglyMeasurable).mp hB2 |>.const_mul 2).mono'
      (measurable_thermalVar μ hH hY t).aestronglyMeasurable (ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using thermalVar_bound μ
          (show Measurable (H ω) from hH.comp (measurable_const.prodMk measurable_id)) (hYm ω) (hA ω) (hB ω) (hHA ω) (hYB ω) t)
  have hsq : (∫ ω, U ω^2 ∂P) ≤ ∫ ω, thermalVar μ (H ω) (Y ω) t ∂P := by
    apply integral_mono ((memLp_two_iff_integrable_sq hULp.aestronglyMeasurable).mp hULp) hIvar
    intro ω
    exact tilt_mean_centered_abs_sq_le μ (hTm ω) (hYm ω) (hTp ω) (hTB ω) (hYB ω)
  simp only [Pi.pow_apply] at hv
  change (∫ ω, U ω ∂P)^2 ≤ _
  linarith

end

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]

lemma tilt_mean_center_triangle {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) (hYB : ∀ x, |Y x| ≤ B)
    (a b : ℝ) :
    tiltMean μ H (fun x => |Y x-a|) 1 ≤ tiltMean μ H (fun x => |Y x-b|) 1+|b-a| := by
  have := tilt_law_probability μ hH hA hHA 1
  have hi (c : ℝ) : Integrable (fun x => |Y x-c|) (tiltLaw μ H 1) :=
    Integrable.of_bound (hY.sub_const c).abs.aestronglyMeasurable (B+|c|)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_abs] using (abs_sub (Y x) c).trans (add_le_add (hYB x) le_rfl))
  simp_rw [← tilt_law_integral μ hH hA hHA 1]
  have hc : (∫ _ : S, |b-a| ∂tiltLaw μ H 1) = |b-a| := by simp
  rw [← hc, ← integral_add (hi b) (integrable_const _)]
  apply integral_mono (hi a) ((hi b).add (integrable_const _))
  intro x
  change |Y x-a| ≤ |Y x-b|+|b-a|
  calc
    _ = |(Y x-b)+(b-a)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

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
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_EnrichedPatternMean
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedPatternEnergy_update (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (a : Fin M) (v : Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N M f (Function.update g a v) x-normalizedPatternEnergy N M f g x| ≤ 2*‖f‖ := by
  classical
  unfold normalizedPatternEnergy
  rw [← Finset.sum_sub_distrib]
  have he : (∑ b : Fin M, (f (∑ i, (Function.update g a v) b i*x.val i)-f (∑ i, g b i*x.val i)))=
      f (∑ i, v i*x.val i)-f (∑ i, g a i*x.val i) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [he]
  exact (abs_sub _ _).trans (by
    have hb := f.norm_coe_le_norm (∑ i, v i*x.val i)
    have ha := f.norm_coe_le_norm (∑ i, g a i*x.val i)
    simp only [Real.norm_eq_abs] at hb ha
    linarith)

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

lemma bulkFeature_norm_sq (N : ℕ) (v : ℕ → ℝ) (x : NormalizedSpin N) :
    ‖bulkFeature N v x‖^2 = ∑ p, bulkAmplitude N v p^2 := by
  rw [bulkFeature, enrichedFeature_norm_sq]
  simp

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

lemma bulkLogPartition_variance (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    variance (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2)
      (bulkDisorderLaw (n+1) M) ≤ Real.pi^2/8*bulkFeatureBound (n+1) v^2+M*(2*‖f‖)^2 := by
  apply vectorLogPartition_mixed_variance (unitSphereLaw (n+1))
    (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) M
    (W := normalizedPatternEnergy (n+1) M f)
    (V := fun x => innerSL ℝ (bulkFeature (n+1) v x))
    (normalizedPatternEnergy_continuous (n+1) M f).measurable
    (fun x => (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_id.prodMk continuous_const))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (Real.sqrt_nonneg _) (normalizedPatternEnergy_bound (n+1) M f)
    (fun x => by simp only [innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl])
    (normalizedPatternEnergy_update (n+1) M f)


lemma enrichedFeature_cross_inner (N J : ℕ) (p : Fin J→ℕ) (c d : Fin J→ℝ)
    (x y : NormalizedSpin N) :
    inner ℝ (enrichedFeature N J p 0 c x) (enrichedFeature N J p 0 d y)=
      ∑ j, c j*d j*spinOverlap x y^(p j) := by
  change (∑ i : EnrichedIndex N J p,
    enrichedFeature N J p 0 d y i * enrichedFeature N J p 0 c x i)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedFeature,zero_mul,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [← spinTensorFeature_inner N (p j) x y]
  change (∑ i, d j*spinTensorFeature N (p j) y i*(c j*spinTensorFeature N (p j) x i))=
    c j*d j*(∑ i, spinTensorFeature N (p j) y i*spinTensorFeature N (p j) x i)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma bulkDirection_continuous (N : ℕ) (p : Fin N) : Continuous (bulkDirection N p) :=
  enrichedFeature_continuous _ _ _ _ _

lemma bulkDirection_norm (N : ℕ) (p : Fin N) (x : NormalizedSpin N) : ‖bulkDirection N p x‖=1 := by
  rw [bulkDirection,enrichedFeature_norm]
  have he : (∑ j : Fin N, (Pi.single (M := fun _ : Fin N => ℝ) p (1:ℝ) j)^2)=1 := by
    classical
    simp [Pi.single_apply]
  rw [he]
  norm_num

lemma bulkFeature_direction_inner (N : ℕ) (v : ℕ→ℝ) (p : Fin N) (x y : NormalizedSpin N) :
    inner ℝ (bulkDirection N p x) (bulkFeature N v y)=
      bulkAmplitude N v p*spinOverlap x y^(p.val+1) := by
  rw [bulkDirection,bulkFeature,enrichedFeature_cross_inner]
  classical
  simp [Pi.single_apply,bulkDegree]

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

lemma bulkExpectedLog_convex (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    ConvexOn ℝ univ (fun t => bulkExpectedLog n M f (Function.update v (p.val+1) t)) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  let F := fun t (d : BulkDisorder (n+1) M) => bulkLogPartition n M f (Function.update v (p.val+1) t) d.1 d.2
  have hi (t : ℝ) : Integrable (F t) (bulkDisorderLaw (n+1) M) :=
    (bulkLogPartition_memLp n M f _).integrable (by norm_num)
  have hi1 : Integrable (fun d => a*F x d) (bulkDisorderLaw (n+1) M) := (hi x).const_mul a
  have hi2 : Integrable (fun d => b*F y d) (bulkDisorderLaw (n+1) M) := (hi y).const_mul b
  change (∫ d, F (a*x+b*y) d ∂bulkDisorderLaw (n+1) M) ≤
    a*(∫ d, F x d ∂bulkDisorderLaw (n+1) M)+b*(∫ d, F y d ∂bulkDisorderLaw (n+1) M)
  calc
    _ ≤ ∫ d, a*F x d+b*F y d ∂bulkDisorderLaw (n+1) M := by
      apply integral_mono (hi _) (hi1.add hi2)
      intro d
      exact (bulkCoupling_regular n M f v p d).2.1.2 (mem_univ x) (mem_univ y) ha hb hab
    _ = _ := by rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul]

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

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FieldDerivative
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma tiltMean_const_of_pos {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H : S→ℝ) (t c : ℝ) (hpos : 0 < tiltPartition μ H t) :
    tiltMean μ H (fun _ => c) t=c := by
  unfold tiltMean tiltIntegral
  rw [integral_mul_const]
  change tiltPartition μ H t*c/tiltPartition μ H t=c
  field_simp

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

lemma convex_derivative_monotone {A a : ℝ→ℝ} (hc : ConvexOn ℝ univ A)
    (hd : ∀ u, HasDerivAt A (a u) u) : Monotone a := by
  intro x y hxy
  simpa only [(hd x).deriv,(hd y).deriv] using
    hc.monotoneOn_deriv (fun x _ => (hd x).differentiableAt) (mem_univ x) (mem_univ y) hxy

lemma integral_convex_derivative_fluctuation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω→ℝ→ℝ} {A a : ℝ→ℝ}
    {D : Ω→ℝ} {u s δ : ℝ} (hs : 0 < s)
    (hD : AEStronglyMeasurable D P)
    (hF : ∀ᵐ ω ∂P, ConvexOn ℝ univ (F ω) ∧ HasDerivAt (F ω) (D ω) u)
    (hA : ConvexOn ℝ univ A) (ha : ∀ x, HasDerivAt A (a x) x)
    (hi : ∀ x ∈ Icc (u-s) (u+s), Integrable (fun ω => F ω x) P)
    (hb : ∀ x ∈ Icc (u-s) (u+s), (∫ ω, |F ω x-A x| ∂P)≤ δ) :
    (∫ ω, |D ω-a u| ∂P) ≤ a (u+s)-a (u-s)+4*δ/s := by
  have hm := convex_derivative_monotone hA ha
  have hp := hA.slope_le_of_hasDerivAt (mem_univ u) (mem_univ (u+s))
    (by linarith : u<u+s) (ha (u+s))
  have hn := hA.le_slope_of_hasDerivAt (mem_univ (u-s)) (mem_univ u)
    (by linarith : u-s<u) (ha (u-s))
  have he1 : u+s-u=s := by ring
  have he2 : u-(u-s)=s := by ring
  simp only [slope,he1,he2,smul_eq_mul,vsub_eq_sub] at hp hn
  have hp' : A (u+s)-A u≤ s*a (u+s) := by
    have := (div_le_iff₀ hs).mp (show (A (u+s)-A u)/s≤ a (u+s) by simpa [div_eq_mul_inv,mul_comm] using hp)
    linarith
  have hn' : s*a (u-s)≤A u-A (u-s) := by
    have := (le_div_iff₀ hs).mp (show a (u-s)≤(A u-A (u-s))/s by simpa [div_eq_mul_inv,mul_comm] using hn)
    linarith
  have he : ((a (u+s)-a (u-s))/s)*s^2=(a (u+s)-a (u-s))*s := by field_simp [ne_of_gt hs]
  have hp'' : A (u+s)-A u-s*a u≤((a (u+s)-a (u-s))/s)*s^2 := by
    rw [he]; nlinarith [hm (show u-s≤u by linarith)]
  have hn'' : A (u-s)-A u+s*a u≤((a (u+s)-a (u-s))/s)*s^2 := by
    rw [he]; nlinarith [hm (show u≤u+s by linarith)]
  have hh := integral_convex_contact_bound P hs hD hF hp'' hn''
    (hi (u+s) (by constructor <;> linarith)) (hi u (by constructor <;> linarith))
    (hi (u-s) (by constructor <;> linarith))
    (hb (u+s) (by constructor <;> linarith)) (hb u (by constructor <;> linarith))
    (hb (u-s) (by constructor <;> linarith))
  simpa only [div_mul_cancel₀ _ (ne_of_gt hs)] using hh

lemma convex_integrated_derivative_shift {A a : ℝ→ℝ}
    (hc : ConvexOn ℝ univ A) (hd : ∀ u, HasDerivAt A (a u) u)
    {s K : ℝ} (hs : 0≤ s) (hK : ∀ u ∈ Icc (1-s) (2+s), |a u|≤ K) :
    (∫ u in (1:ℝ)..2, a (u+s)-a (u-s)) ≤ 4*K*s := by
  have hm := convex_derivative_monotone hc hd
  have hp : Monotone (fun u => a (u+s)) := hm.comp (fun _ _ h => by linarith)
  have hn : Monotone (fun u => a (u-s)) := hm.comp (fun _ _ h => sub_le_sub_right h s)
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hn.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => (hd (u+s)).comp_add_const u s) hp.intervalIntegrable,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => (hd (u-s)).comp_sub_const u s) hn.intervalIntegrable]
  have ht (t : ℝ) (ht : t∈Icc (1:ℝ) 2) : |A (t+s)-A (t-s)|≤ 2*K*s := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hm.intervalIntegrable]
    have hh : ‖∫ u in (t-s)..(t+s), a u‖≤ K*|(t+s)-(t-s)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
        rw [uIoc_of_le (by linarith : t-s≤t+s)] at hu
        exact hK u ⟨by linarith [ht.1,hu.1],by linarith [ht.2,hu.2]⟩)
    have he : (t+s)-(t-s)=2*s := by ring
    rw [he,abs_of_nonneg (by positivity)] at hh
    simpa only [Real.norm_eq_abs] using hh.trans_eq (by ring)
  have h1 := ht 1 (by norm_num)
  have h2 := ht 2 (by norm_num)
  linarith [le_abs_self (A (2+s)-A (2-s)),neg_abs_le (A (1+s)-A (1-s))]

lemma integrated_convex_fluctuation_bound {H A a : ℝ→ℝ}
    (hc : ConvexOn ℝ univ A) (hd : ∀ u, HasDerivAt A (a u) u)
    {s K δ : ℝ} (hs : 0 < s)
    (hK : ∀ u ∈ Icc (1-s) (2+s), |a u|≤ K)
    (hH : IntervalIntegrable H volume 1 2)
    (hb : ∀ u ∈ Icc (1:ℝ) 2, H u≤ a (u+s)-a (u-s)+4*δ/s) :
    (∫ u in (1:ℝ)..2, H u) ≤ 4*K*s+4*δ/s := by
  have hm := convex_derivative_monotone hc hd
  have hp : Monotone (fun u => a (u+s)) := hm.comp (fun _ _ h => by linarith)
  have hn : Monotone (fun u => a (u-s)) := hm.comp (fun _ _ h => sub_le_sub_right h s)
  calc
    _ ≤ ∫ u in (1:ℝ)..2, a (u+s)-a (u-s)+4*δ/s :=
      intervalIntegral.integral_mono_on (by norm_num) hH
        ((hp.intervalIntegrable.sub hn.intervalIntegrable).add intervalIntegrable_const) hb
    _ = (∫ u in (1:ℝ)..2, a (u+s)-a (u-s))+4*δ/s := by
      rw [intervalIntegral.integral_add (hp.intervalIntegrable.sub hn.intervalIntegrable) intervalIntegrable_const]
      norm_num
    _ ≤ _ := by linarith [convex_integrated_derivative_shift hc hd hs.le hK]

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkStein
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

lemma bulkOverlapPower_measurable (N r : ℕ) :
    Measurable (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 1) (x 0)^r) := by
  exact (((measurable_pi_apply 1).subtype_val).inner ((measurable_pi_apply 0).subtype_val)).pow_const r

lemma bulkOverlapPower_bound (N r : ℕ) (x : Fin 2→NormalizedSpin N) :
    |spinOverlap (x 1) (x 0)^r|≤1 := by
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) (spinOverlap_abs_le _ _) r).trans_eq (one_pow r)

lemma bulk_fixed_patterns_ibp_raw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) :
    (∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (bulkY (n+1) p g) 1 ∂stdGaussian (BulkMark (n+1))) =
    ∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (fun x => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x)) 1 -
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
        (fun x => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0)))
    ∂stdGaussian (BulkMark (n+1)) := by
  have hW : Measurable (normalizedPatternEnergy (n+1) M f a) :=
    ((normalizedPatternEnergy_continuous (n+1) M f).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact euclideanGaussian_tiltMean_ibp (unitSphereLaw (n+1)) hW
    (bulkFeature_continuous (n+1) v).measurable (bulkDirection_continuous (n+1) p).measurable
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => le_of_eq (bulkFeature_norm_sq (n+1) v x))
    (fun x => by rw [bulkDirection_norm]; norm_num : ∀ x, ‖bulkDirection (n+1) p x‖^2≤(1:ℝ))

lemma bulk_fixed_integrand_eq (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) (g : BulkMark (n+1)) :
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (fun x => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x)) 1 -
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
        (fun x => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0))) =
    bulkAmplitude (n+1) v p*(1-gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2 (fun x => spinOverlap (x 1) (x 0)^(p.val+1))) := by
  have h1 : (fun x : NormalizedSpin (n+1) => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x))=
      (fun _ => bulkAmplitude (n+1) v p) := by
    funext x
    rw [bulkFeature_direction_inner,spinOverlap_self,one_pow,mul_one]
  have h2 : (fun x : Fin 2→NormalizedSpin (n+1) => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0)))=
      (fun x => bulkAmplitude (n+1) v p*spinOverlap (x 1) (x 0)^(p.val+1)) := by
    funext x
    exact bulkFeature_direction_inner _ _ _ _ _
  have hp : 0<tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1 :=
    tilt_partition_pos_of_integrable _ (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v (a,g))
  rw [h1,h2,tiltMean_const_of_pos _ _ _ _ hp,gibbsReplicaMean,tiltMean_const_mul_general]
  change bulkAmplitude (n+1) v p - bulkAmplitude (n+1) v p * _ = bulkAmplitude (n+1) v p * (1-_)
  unfold gibbsReplicaMean
  ring

lemma bulk_replicaPower_integrable_fixed (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (a : Fin M→Fin (n+1)→ℝ) :
    Integrable (fun g => gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => spinOverlap (x 1) (x 0)^r)) (stdGaussian (BulkMark (n+1))) := by
  exact kernel_replicaMean_bounded_integrable (Kernel.const (BulkMark (n+1)) (unitSphereLaw (n+1)))
    (stdGaussian (BulkMark (n+1)))
    (H := fun g x => bulkHamiltonian (n+1) M f v a g x)
    (G := fun _ x => spinOverlap (x 1) (x 0)^r)
    (((bulkHamiltonian_continuous (n+1) M f v).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).measurable)
    ((bulkOverlapPower_measurable (n+1) r).comp measurable_snd)
    zero_le_one (fun _ x => bulkOverlapPower_bound _ _ x)

lemma bulk_fixed_patterns_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) :
    (∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (bulkY (n+1) p g) 1 ∂stdGaussian (BulkMark (n+1))) =
    bulkAmplitude (n+1) v p*(1-∫ g, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂stdGaussian (BulkMark (n+1))) := by
  rw [bulk_fixed_patterns_ibp_raw]
  simp_rw [bulk_fixed_integrand_eq]
  rw [integral_const_mul,integral_sub (integrable_const _) (bulk_replicaPower_integrable_fixed n M f v (p.val+1) a)]
  simp

lemma bulk_meanY_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun a : BulkDisorder (n+1) M => tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) (bulkY (n+1) p a.2) 1) :=
  kernel_tiltMean_measurable (bulkSpinKernel n M)
    (H := fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (Y := fun a x => bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable (bulkY_joint_measurable _ _ _)

lemma bulk_meanY_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : BulkDisorder (n+1) M) :
    |tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (bulkY (n+1) p a.2) 1|≤‖a.2‖ := by
  exact tiltMean_bound_of_integrable _ (bulkHamiltonian_section_measurable _ _ _ _ a)
    (bulkY_measurable _ _).of_uncurry_left
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v a)
    (bulkY_bound _ _ _)

lemma bulk_meanY_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Integrable (fun a : BulkDisorder (n+1) M => tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) (bulkY (n+1) p a.2) 1) (bulkDisorderLaw (n+1) M) := by
  have hi : Integrable (fun g : BulkMark (n+1) => ‖g‖) (stdGaussian (BulkMark (n+1))) :=
    ((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).integrable (by norm_num)
  apply (hi.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulk_meanY_measurable n M f v p).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulk_meanY_bound n M f v p a

lemma bulk_replicaPower_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2 (fun x => spinOverlap (x 1) (x 0)^r))
      (bulkDisorderLaw (n+1) M) :=
  kernel_replicaMean_bounded_integrable (bulkSpinKernel n M) _
    (H := fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (G := fun _ x => spinOverlap (x 1) (x 0)^r)
    (bulkHamiltonian_continuous _ _ _ _).measurable
    ((bulkOverlapPower_measurable _ _).comp measurable_snd) zero_le_one
    (fun _ x => bulkOverlapPower_bound _ _ x)

lemma bulk_annealed_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ a, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (bulkY (n+1) p a.2) 1 ∂bulkDisorderLaw (n+1) M) =
    bulkAmplitude (n+1) v p*(1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M) := by
  rw [bulkDisorderLaw,integral_prod _ (bulk_meanY_integrable n M f v p)]
  simp_rw [bulk_fixed_patterns_ibp]
  rw [integral_const_mul,integral_sub (integrable_const _)
    (bulk_replicaPower_integrable n M f v (p.val+1)).integral_prod_left]
  rw [integral_const]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [← integral_prod _ (bulk_replicaPower_integrable n M f v (p.val+1))]

lemma bulk_expected_slope_eq (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    (∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) =
    bulkCoefficient (n+1) p^2*u*(1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M) := by
  unfold bulkCouplingSlope
  rw [integral_const_mul,bulk_annealed_ibp]
  simp only [bulkAmplitude,Function.update_self,bulkCoefficient]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkThermal
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

lemma bulkMarkNorm_memLp (n M : ℕ) :
    MemLp (fun a : BulkDisorder (n+1) M => ‖a.2‖) 2 (bulkDisorderLaw (n+1) M) := by
  exact ((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).comp_snd
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))

lemma bulkThermalVar_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Measurable (bulkThermalVar n M f v p u) :=
  measurable_thermalVar (unitSphereLaw (n+1))
    (bulkHamiltonian_continuous _ _ _ _).measurable
    ((bulkY_joint_measurable _ _ _).const_mul _) u

lemma bulkThermalVar_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) : 0≤bulkThermalVar n M f v p u a := by
  apply thermalVar_nonneg (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a)
    ((bulkY_measurable _ _).of_uncurry_left.const_mul _)
    (by unfold bulkFeatureBound; positivity : 0≤(M:ℝ)*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg a.2))
    (bulkHamiltonian_bound _ _ _ _ a)
  intro x
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le

lemma bulkThermalVar_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (u : ℝ) (a : BulkDisorder (n+1) M) :
    |bulkThermalVar n M f v p u a|≤2*(bulkCoefficient (n+1) p*‖a.2‖)^2 := by
  apply thermalVar_bound (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable _ _ _ _ a)
    ((bulkY_measurable _ _).of_uncurry_left.const_mul _)
    (by unfold bulkFeatureBound; positivity : 0≤(M:ℝ)*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg a.2))
    (bulkHamiltonian_bound _ _ _ _ a)
  intro x
  rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
  exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le

lemma bulkThermalVar_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    Integrable (bulkThermalVar n M f v p u) (bulkDisorderLaw (n+1) M) := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  apply (((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 2).mono'
    (bulkThermalVar_measurable n M f v p u).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkThermalVar_bound n M f v p u a

lemma bulkExpectedSlope_hasDerivAt (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    HasDerivAt (fun t => ∫ a, bulkCouplingSlope n M f v p t a ∂bulkDisorderLaw (n+1) M)
      (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) u := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  have hd := annealedAffineMean_deriv (unitSphereLaw (n+1)) (bulkDisorderLaw (n+1) M)
    (H := fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2 x)
    (Y := fun a x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)
    (A := fun a => M*‖f‖+bulkFeatureBound (n+1) (Function.update v (p.val+1) 0)*‖a.2‖)
    (B := fun a => bulkCoefficient (n+1) p*‖a.2‖)
    (bulkHamiltonian_continuous _ _ _ _).measurable ((bulkY_joint_measurable _ _ _).const_mul _)
    (fun _ => by unfold bulkFeatureBound; positivity) (fun _ => mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg _))
    (bulkHamiltonian_bound _ _ _ _) (fun a x => by
      rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]
      exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le)
    (hb.integrable (by norm_num)) ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb) u
  convert hd using 1
  · funext t
    apply integral_congr_ae
    exact ae_of_all _ fun a => by
      unfold bulkCouplingSlope
      rw [← tiltMean_const_mul_general]
      congr 2
      funext x
      exact bulkHamiltonian_update _ _ _ _ _ _ _ _
  · rfl

lemma bulk_expected_slope_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    |∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M|≤
      2*bulkCoefficient (n+1) p^2*|u| := by
  rw [bulk_expected_slope_eq,abs_mul,abs_mul,abs_sq]
  have hh : |∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M|≤1 := by
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ _ : BulkDisorder (n+1) M, (1:ℝ) ∂bulkDisorderLaw (n+1) M := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
        exact ae_of_all _ fun a => gibbsReplicaMean_bound_of_integrable (unitSphereLaw (n+1))
          (bulkHamiltonian_section_measurable _ _ _ _ a) (bulkOverlapPower_measurable _ _)
          (bulkHamiltonian_exp_integrable n M f _ a) (bulkOverlapPower_bound _ _)
      _ = 1 := by simp
  have he : |1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M|≤2 := by
    simpa only [abs_one,one_add_one_eq_two] using (abs_sub _ _).trans (add_le_add (le_refl |(1:ℝ)|) hh)
  nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg (bulkCoefficient (n+1) p)) (abs_nonneg u))]

lemma bulkExpectedThermalVar_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) := by
  have he : (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)=
      deriv (fun u => ∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) := by
    funext u
    exact (bulkExpectedSlope_hasDerivAt n M f v p u).deriv.symm
  rw [he]
  exact measurable_deriv _

lemma bulkExpectedThermalVar_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (fun u => ∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M) volume a b := by
  have hb := (bulkMarkNorm_memLp n M).const_mul (bulkCoefficient (n+1) p)
  have hi := ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 2
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top)
    (bulkExpectedThermalVar_measurable n M f v p).aestronglyMeasurable.restrict
    (∫ x : BulkDisorder (n+1) M, 2*(bulkCoefficient (n+1) p*‖x.2‖)^2 ∂bulkDisorderLaw (n+1) M)
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs]
  exact abs_integral_le_integral_abs.trans (integral_mono (bulkThermalVar_integrable n M f v p u).abs hi
    (bulkThermalVar_bound n M f v p u))

lemma bulkThermalVar_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ u in (1:ℝ)..2, ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) ≤
      6*bulkCoefficient (n+1) p^2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => bulkExpectedSlope_hasDerivAt n M f v p u)
    (bulkExpectedThermalVar_intervalIntegrable n M f v p 1 2)]
  have h1 := bulk_expected_slope_bound n M f v p 1
  have h2 := bulk_expected_slope_bound n M f v p 2
  norm_num only [abs_one,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h1 h2
  linarith [le_abs_self (∫ a, bulkCouplingSlope n M f v p 2 a ∂bulkDisorderLaw (n+1) M),
    neg_abs_le (∫ a, bulkCouplingSlope n M f v p 1 a ∂bulkDisorderLaw (n+1) M)]

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

lemma bulkCouplingSlope_joint_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (Function.uncurry (bulkCouplingSlope n M f v p)) := by
  let H := fun a : ℝ × BulkDisorder (n+1) M => fun x : NormalizedSpin (n+1) =>
    bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.2.1 a.2.2 x+
      a.1*(bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x)
  let Y := fun a : ℝ × BulkDisorder (n+1) M => bulkY (n+1) p a.2.2
  have hYc : Continuous (Function.uncurry Y) :=
    ((bulkDirection_continuous (n+1) p).comp continuous_snd).inner continuous_fst.snd.snd
  have hY : Measurable (Function.uncurry Y) := hYc.measurable
  have hH : Measurable (Function.uncurry H) := by
    have hb : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
        bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1.2.1 a.1.2.2 a.2) :=
      (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) 0)).comp
        (continuous_fst.snd.prodMk continuous_snd)
    exact (hb.add (continuous_fst.fst.mul (hYc.const_mul _))).measurable
  have hm := (kernel_tiltMean_measurable (Kernel.const (ℝ × BulkDisorder (n+1) M) (unitSphereLaw (n+1))) hH hY).const_mul (bulkCoefficient (n+1) p)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  unfold Function.uncurry bulkCouplingSlope
  congr 2
  funext x
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

lemma bulkSlopeDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (bulkSlopeDeviation n M f v p) := by
  have hd := bulkCouplingSlope_joint_measurable n M f v p
  have hm := (hd.stronglyMeasurable.integral_prod_right' (ν:=bulkDisorderLaw (n+1) M)).measurable
  exact ((hd.sub (hm.comp measurable_fst)).abs).stronglyMeasurable.integral_prod_right'.measurable

lemma bulkSlopeDeviation_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkSlopeDeviation n M f v p u ≤
      2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
  have hi := (bulkExpectedLog_hasDerivAt n M f v p u).1
  have hn := (bulkMarkNorm_memLp n M).integrable (by norm_num)
  have hB : |∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M|≤
      bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M) := by
    calc
      _ ≤ ∫ a, |bulkCouplingSlope n M f v p u a| ∂bulkDisorderLaw (n+1) M := abs_integral_le_integral_abs
      _ ≤ ∫ a : BulkDisorder (n+1) M, bulkCoefficient (n+1) p*‖a.2‖ ∂bulkDisorderLaw (n+1) M :=
        integral_mono hi.abs (hn.const_mul _) (bulkCouplingSlope_bound n M f v p u)
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∫ a, bulkCoefficient (n+1) p*‖a.2‖+
        |∫ b, bulkCouplingSlope n M f v p u b ∂bulkDisorderLaw (n+1) M| ∂bulkDisorderLaw (n+1) M := by
      apply integral_mono (hi.sub (integrable_const _)).abs ((hn.const_mul _).add (integrable_const _))
      intro a
      exact (abs_sub _ _).trans (add_le_add (bulkCouplingSlope_bound n M f v p u a) (le_refl _))
    _ ≤ _ := by
      rw [integral_add (hn.const_mul _) (integrable_const _),integral_const_mul]
      simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
      linarith

lemma bulkSlopeDeviation_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (bulkSlopeDeviation n M f v p) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    (bulkSlopeDeviation_measurable n M f v p).aestronglyMeasurable.restrict
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤bulkSlopeDeviation n M f v p u from integral_nonneg fun _ => abs_nonneg _)]
    exact bulkSlopeDeviation_bound n M f v p u

lemma bulkLogPartition_fluctuation (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) {C : ℝ}
    (hC : 0≤C) (hv : ∀ p, |v p|≤C) :
    (∫ a : BulkDisorder (n+1) M, |bulkLogPartition n M f v a.1 a.2-bulkExpectedLog n M f v| ∂bulkDisorderLaw (n+1) M) ≤
      Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2) := by
  apply (integral_centered_abs_le_sqrt_variance _ (bulkLogPartition_memLp n M f v)).trans
  apply Real.sqrt_le_sqrt
  apply (bulkLogPartition_variance n M f v).trans
  have hh := mul_le_mul_of_nonneg_left (bulkFeatureBound_sq_le (n+1) v hC (fun j => hv (j+1))) (by positivity : 0≤Real.pi^2/8)
  nlinarith

lemma bulkSlopeDeviation_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    {s C : ℝ} (hs : 0 < s) (hs1 : s≤1) (hC : 3≤C) (hv : ∀ p, |v p|≤C) :
    (∫ u in (1:ℝ)..2, bulkSlopeDeviation n M f v p u) ≤
      4*(6*bulkCoefficient (n+1) p^2)*s+
      4*Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  apply integrated_convex_fluctuation_bound (bulkExpectedLog_convex n M f v p)
    (fun u => (bulkExpectedLog_hasDerivAt n M f v p u).2) hs
    (K:=6*bulkCoefficient (n+1) p^2)
  · intro u hu
    calc
      _ ≤ 2*bulkCoefficient (n+1) p^2*|u| := bulk_expected_slope_bound n M f v p u
      _ ≤ _ := by
        have hh : |u|≤3 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
        nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*bulkCoefficient (n+1) p^2)]
  · exact bulkSlopeDeviation_intervalIntegrable n M f v p 1 2
  · intro u hu
    apply integral_convex_derivative_fluctuation (bulkDisorderLaw (n+1) M) hs
      (bulkCouplingSlope_measurable n M f v p u).aestronglyMeasurable
      (ae_of_all _ fun a => ⟨(bulkCoupling_regular n M f v p a).2.1,(bulkCoupling_regular n M f v p a).2.2 u⟩)
      (bulkExpectedLog_convex n M f v p) (fun t => (bulkExpectedLog_hasDerivAt n M f v p t).2)
      (fun t _ => (bulkLogPartition_memLp n M f _).integrable (by norm_num))
    intro t ht
    apply bulkLogPartition_fluctuation n M f _ (by linarith : 0≤C)
    intro j
    by_cases hj : j=p.val+1
    · subst j
      simp only [Function.update_self]
      exact abs_le.mpr ⟨by linarith [ht.1,hu.1],by linarith [ht.2,hu.2]⟩
    · rw [Function.update_of_ne hj]
      exact hv j

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegratedThermal
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

lemma integral_sqrt_le_sqrt_integral_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω→ℝ}
    (hF : Measurable F) (hI : Integrable F P) (h0 : ∀ x, 0≤F x) :
    (∫ x, Real.sqrt (F x) ∂P)≤Real.sqrt (∫ x, F x ∂P) := by
  have hs : (fun x => (Real.sqrt (F x))^2)=F := funext fun x => Real.sq_sqrt (h0 x)
  have hLp : MemLp (fun x => Real.sqrt (F x)) 2 P :=
    (memLp_two_iff_integrable_sq hF.sqrt.aestronglyMeasurable).mpr (by simpa only [hs] using hI)
  have hv := variance_nonneg (fun x => Real.sqrt (F x)) P
  rw [variance_eq_sub hLp] at hv
  simp only [Pi.pow_apply] at hv
  change 0≤(∫ x, (Real.sqrt (F x))^2 ∂P)-(∫ x, Real.sqrt (F x) ∂P)^2 at hv
  rw [hs] at hv
  exact (Real.le_sqrt (integral_nonneg fun x => Real.sqrt_nonneg _) (integral_nonneg h0)).mpr (by linarith)

lemma annealed_centered_energy_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    {H Y : Ω→S→ℝ} (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω→ℝ} (hA : ∀ a, 0≤A a) (hB : ∀ a, 0≤B a)
    (hHA : ∀ a x, |H a x|≤A a) (hYB : ∀ a x, |Y a x|≤B a)
    (hB2 : MemLp B 2 P) :
    (∫ a, tiltMean μ (H a) (fun x => |Y a x-∫ b, tiltMean μ (H b) (Y b) 1 ∂P|) 1 ∂P) ≤
      Real.sqrt (∫ a, thermalVar μ (H a) (Y a) 0 ∂P)+
      ∫ a, |tiltMean μ (H a) (Y a) 1-∫ b, tiltMean μ (H b) (Y b) 1 ∂P| ∂P := by
  let M := fun a => tiltMean μ (H a) (Y a) 1
  let E := ∫ a, M a ∂P
  let U := fun a => tiltMean μ (H a) (fun x => |Y a x-M a|) 1
  have hM : Measurable M := measurable_tiltMean_param μ hH hY
  have hU : Measurable U := measurable_tiltMean_param μ hH (hY.sub (hM.comp measurable_fst)).abs
  have hHm (a) : Measurable (H a) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (a) : Measurable (Y a) := hY.comp (measurable_const.prodMk measurable_id)
  have hMB (a) : |M a|≤B a := tilt_mean_bound μ (hHm a) (hYm a) (hA a) (hB a) (hHA a) (hYB a) 1
  have hBI := hB2.integrable (by norm_num)
  have hUI : Integrable U P := by
    apply (hBI.const_mul 2).mono' hU.aestronglyMeasurable
    exact ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using tilt_mean_bound μ (hHm a)
        ((hYm a).sub_const (M a) |>.abs) (hA a) (mul_nonneg (by norm_num) (hB a)) (hHA a)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (by linarith [hYB a x,hMB a])) 1
  have hMI : Integrable (fun a => |M a-E|) P :=
    ((hBI.mono' hM.aestronglyMeasurable (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hMB a)).sub (integrable_const E)).abs
  have hQI : Integrable (fun a => tiltMean μ (H a) (fun x => |Y a x-E|) 1) P := by
    apply (hBI.add (integrable_const |E|)).mono'
      (measurable_tiltMean_param μ hH
        (show Measurable (Function.uncurry (fun a x => |Y a x-E|)) from (hY.sub_const E).abs)).aestronglyMeasurable
    exact ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using tilt_mean_bound μ (hHm a)
        ((hYm a).sub_const E |>.abs) (hA a) (add_nonneg (hB a) (abs_nonneg E)) (hHA a)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hYB a x) le_rfl)) 1
  have hs : (∫ a, U a ∂P)^2≤∫ a, thermalVar μ (H a) (Y a) 0 ∂P := by
    simpa only [zero_mul,add_zero] using annealed_thermal_abs_sq_le μ P hH hY hA hB hHA hYB hB2 0
  have hu : (∫ a, U a ∂P)≤Real.sqrt (∫ a, thermalVar μ (H a) (Y a) 0 ∂P) :=
    (Real.le_sqrt (integral_nonneg fun a => tiltMean_nonneg μ (fun _ => abs_nonneg _) 1)
      ((sq_nonneg _).trans hs)).mpr hs
  have ht : (∫ a, tiltMean μ (H a) (fun x => |Y a x-E|) 1 ∂P)≤
      (∫ a, U a ∂P)+(∫ a, |M a-E| ∂P) := by
    rw [← integral_add hUI hMI]
    exact integral_mono hQI (hUI.add hMI) fun a =>
      tilt_mean_center_triangle μ (hHm a) (hYm a) (hA a) (hHA a) (hYB a) E (M a)
  exact ht.trans (add_le_add hu le_rfl)

lemma bulkThermalSqrt_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.sqrt (∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M)) volume a b := by
  have hm := (bulkExpectedThermalVar_measurable n M f v p).sqrt
  have hs (u : ℝ) : (Real.sqrt (∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M))^2=
      ∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M :=
    Real.sq_sqrt (integral_nonneg (bulkThermalVar_nonneg n M f v p u))
  have hi := bulkExpectedThermalVar_intervalIntegrable n M f v p a b
  constructor
  · exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (by simpa only [IntegrableOn,hs] using hi.1)).integrable (by norm_num)
  · exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (by simpa only [IntegrableOn,hs] using hi.2)).integrable (by norm_num)

lemma bulkThermalSqrt_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M))≤
      Real.sqrt 6*bulkCoefficient (n+1) p := by
  let P := volume.restrict (Ioc (1:ℝ) 2)
  have : IsProbabilityMeasure P := ⟨by norm_num [P]⟩
  have hi : Integrable (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) P :=
    (bulkExpectedThermalVar_intervalIntegrable n M f v p 1 2).1
  have he := integral_sqrt_le_sqrt_integral_probability P
    (bulkExpectedThermalVar_measurable n M f v p) hi
    (fun u => integral_nonneg (bulkThermalVar_nonneg n M f v p u))
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  apply he.trans
  have hb := bulkThermalVar_integrated_bound n M f v p
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)] at hb
  calc
    _ ≤ Real.sqrt (6*bulkCoefficient (n+1) p^2) := Real.sqrt_le_sqrt hb
    _ = _ := by rw [Real.sqrt_mul (by norm_num),Real.sqrt_sq (bulkCoefficient_pos n p).le]

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

lemma bulkCoupledHamiltonian_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f (Function.update v (p.val+1) a.1.1) a.1.2.1 a.1.2.2 a.2) := by
  have hb : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1.2.1 a.1.2.2 a.2) :=
    (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) 0)).comp
      (continuous_fst.snd.prodMk continuous_snd)
  have hy : Continuous (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkY (n+1) p a.1.2.2 a.2) :=
    ((bulkDirection_continuous (n+1) p).comp continuous_snd).inner continuous_fst.snd.snd
  convert (hb.add (continuous_fst.fst.mul (hy.const_mul (bulkCoefficient (n+1) p)))).measurable using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  exact bulkHamiltonian_update _ _ _ _ _ _ _ _

lemma bulkEnergyDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    0≤bulkEnergyDeviation n M f v p u :=
  integral_nonneg fun _ => tiltMean_nonneg _ (fun _ => abs_nonneg _) _

lemma bulkEnergyDeviation_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (bulkEnergyDeviation n M f v p) := by
  have hE := (bulkCouplingSlope_joint_measurable n M f v p).stronglyMeasurable.integral_prod_right'
    (ν:=bulkDisorderLaw (n+1) M)
  have hY : Measurable (fun a : (ℝ × BulkDisorder (n+1) M) × NormalizedSpin (n+1) =>
      bulkCoefficient (n+1) p*bulkY (n+1) p a.1.2.2 a.2) :=
    ((bulkY_measurable (n+1) p).comp (measurable_fst.snd.snd.prodMk measurable_snd)).const_mul _
  have hm := kernel_tiltMean_measurable (Kernel.const (ℝ × BulkDisorder (n+1) M) (unitSphereLaw (n+1)))
    (H:=fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) a.1) a.2.1 a.2.2 x)
    (Y:=fun a x => |bulkCoefficient (n+1) p*bulkY (n+1) p a.2.2 x-
      ∫ b, bulkCouplingSlope n M f v p a.1 b ∂bulkDisorderLaw (n+1) M|)
    (bulkCoupledHamiltonian_measurable n M f v p) (hY.sub (hE.measurable.comp measurable_fst.fst)).abs
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

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

lemma bulkEnergyDeviation_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (bulkEnergyDeviation n M f v p) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    (bulkEnergyDeviation_measurable n M f v p).aestronglyMeasurable.restrict
    (2*bulkCoefficient (n+1) p*(∫ a : BulkDisorder (n+1) M, ‖a.2‖ ∂bulkDisorderLaw (n+1) M))
  exact ae_of_all _ fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (bulkEnergyDeviation_nonneg n M f v p u)]
    exact bulkEnergyDeviation_bound n M f v p u

lemma bulkEnergyDeviation_thermal_disorder (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    bulkEnergyDeviation n M f v p u ≤
      Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)+
        bulkSlopeDeviation n M f v p u := by
  have he := annealed_centered_energy_bound (unitSphereLaw (n+1)) (bulkDisorderLaw (n+1) M)
    (H:=fun a x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)
    (Y:=fun a x => bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous (n+1) M f (Function.update v (p.val+1) u)).measurable
    ((bulkY_joint_measurable (n+1) M p).const_mul (bulkCoefficient (n+1) p))
    (B:=fun a => bulkCoefficient (n+1) p*‖a.2‖)
    (fun a => by unfold bulkFeatureBound; positivity)
    (fun a => mul_nonneg (bulkCoefficient_pos n p).le (norm_nonneg _))
    (bulkHamiltonian_bound (n+1) M f (Function.update v (p.val+1) u))
    (fun a x => by rw [abs_mul,abs_of_pos (bulkCoefficient_pos n p)]; exact mul_le_mul_of_nonneg_left (bulkY_bound _ _ _ _) (bulkCoefficient_pos n p).le)
    ((bulkMarkNorm_memLp n M).const_mul _)
  simp_rw [← bulkCouplingSlope_eq_mean] at he
  change bulkEnergyDeviation n M f v p u ≤ _ at he
  apply he.trans_eq
  unfold bulkSlopeDeviation
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    have hh : (fun x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2 x)=
        (fun x => bulkHamiltonian (n+1) M f (Function.update v (p.val+1) 0) a.1 a.2 x+
          u*(bulkCoefficient (n+1) p*bulkY (n+1) p a.2 x)) :=
      funext fun x => bulkHamiltonian_update _ _ _ _ _ _ _ _
    unfold bulkThermalVar thermalVar
    simp only [zero_mul,add_zero,hh]

lemma bulkEnergyDeviation_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    {s C : ℝ} (hs : 0 < s) (hs1 : s≤1) (hC : 3≤C) (hv : ∀ j, |v j|≤C) :
    (∫ u in (1:ℝ)..2, bulkEnergyDeviation n M f v p u)≤
      Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*C^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  have hsq : IntervalIntegrable (fun u => Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)) volume 1 2 :=
    bulkThermalSqrt_intervalIntegrable n M f v p 1 2
  calc
    _ ≤ ∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M)+bulkSlopeDeviation n M f v p u :=
      intervalIntegral.integral_mono (by norm_num) (bulkEnergyDeviation_intervalIntegrable n M f v p 1 2)
        (hsq.add (bulkSlopeDeviation_intervalIntegrable n M f v p 1 2))
        (fun u => bulkEnergyDeviation_thermal_disorder n M f v p u)
    _ = (∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M))+
        ∫ u in (1:ℝ)..2, bulkSlopeDeviation n M f v p u := intervalIntegral.integral_add hsq (bulkSlopeDeviation_intervalIntegrable n M f v p 1 2)
    _ ≤ _ := by have h1 := bulkThermalSqrt_integrated_bound n M f v p; have h2 := bulkSlopeDeviation_integrated_bound n M f v p hs hs1 hC hv; linarith

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

lemma infinitePi_update_measurePreserving {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ℕ) :
    MeasurePreserving (fun a : (ℕ→X) × X => Function.update a.1 p a.2)
      ((Measure.infinitePi fun _ : ℕ => μ).prod μ) (Measure.infinitePi fun _ : ℕ => μ) := by
  classical
  refine ⟨by fun_prop,?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  by_cases hp : p∈s
  · have he : (fun a : (ℕ→X) × X => Function.update a.1 p a.2) ⁻¹' Set.pi s t =
        (Set.pi (s.erase p) t) ×ˢ t p := by
      ext a
      simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi => ?_,?_⟩
        · simpa only [Function.update_of_ne hi.1] using h i hi.2
        · simpa only [Function.update_self] using h p hp
      · rintro ⟨ha,hb⟩ i hi
        by_cases hip : i=p
        · subst i; simpa only [Function.update_self] using hb
        · simpa only [Function.update_of_ne hip] using ha i ⟨hip,hi⟩
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.prod_erase_mul _ _ hp
  · have he : (fun a : (ℕ→X) × X => Function.update a.1 p a.2) ⁻¹' Set.pi s t =
        (Set.pi s t) ×ˢ (univ : Set X) := by
      ext a
      simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Set.mem_univ,and_true,Finset.mem_coe]
      exact forall_congr' fun i => by
        by_cases hi : i∈s
        · have hip : i≠p := fun h => hp (h ▸ hi)
          simp only [hi,true_implies,Function.update_of_ne hip]
        · simp only [hi,false_implies]
    rw [he,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi _ (fun i _ => ht i)]

lemma bulkParameterLaw_ae : ∀ᵐ v ∂bulkParameterLaw, ∀ j, v j∈Icc (1:ℝ) 2 := by
  rw [ae_all_iff]
  intro j
  have he : ∀ᵐ x ∂bulkParameterUniform, x∈Icc (1:ℝ) 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => ⟨hx.1.le,hx.2⟩
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => bulkParameterUniform) j).quasiMeasurePreserving.ae he

lemma bulkParameterLaw_integral_resample (p : ℕ) {F : (ℕ→ℝ)→ℝ}
    (hF : Integrable F bulkParameterLaw) :
    (∫ v, F v ∂bulkParameterLaw) = ∫ v, (∫ u in (1:ℝ)..2,
      F (Function.update v p u)) ∂bulkParameterLaw := by
  have hm := infinitePi_update_measurePreserving bulkParameterUniform p
  change MeasurePreserving (fun a : (ℕ→ℝ) × ℝ => Function.update a.1 p a.2)
    (bulkParameterLaw.prod bulkParameterUniform) bulkParameterLaw at hm
  have hi : Integrable (fun a : (ℕ→ℝ) × ℝ => F (Function.update a.1 p a.2))
      (bulkParameterLaw.prod bulkParameterUniform) := hm.integrable_comp hF.aestronglyMeasurable |>.mpr hF
  calc
    _ = ∫ a : (ℕ→ℝ) × ℝ, F (Function.update a.1 p a.2) ∂(bulkParameterLaw.prod bulkParameterUniform) :=
      by
        have hh : AEStronglyMeasurable F (Measure.map (fun a : (ℕ→ℝ) × ℝ => Function.update a.1 p a.2)
            (bulkParameterLaw.prod bulkParameterUniform)) := by rw [hm.map_eq]; exact hF.aestronglyMeasurable
        simpa only [hm.map_eq] using integral_map hm.measurable.aemeasurable hh
    _ = ∫ v, ∫ u, F (Function.update v p u) ∂bulkParameterUniform ∂bulkParameterLaw := integral_prod _ hi
    _ = _ := by simp only [bulkParameterUniform,intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]

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

lemma bulkDegreeDeviation_update (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) (u : ℝ) :
    bulkDegreeDeviation n M f p (Function.update v (p.val+1) u)=bulkEnergyDeviation n M f v p u := by
  simp only [bulkDegreeDeviation,Function.update_self,bulkEnergyDeviation,bulkCouplingSlope,Function.update_idem]

lemma bulkDegreeDeviation_integral_bound (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1))
    {s : ℝ} (hs : 0 < s) (hs1 : s≤1) :
    (∫ v, bulkDegreeDeviation n M f p v ∂bulkParameterLaw)≤
      Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s := by
  rw [bulkParameterLaw_integral_resample (p.val+1) (bulkDegreeDeviation_integrable n M f p)]
  simp only [bulkDegreeDeviation_update]
  calc
    _ ≤ ∫ _ : ℕ→ℝ, Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s ∂bulkParameterLaw := by
      apply integral_mono_of_nonneg (ae_of_all _ fun v => intervalIntegral.integral_nonneg (by norm_num)
        (fun u _ => bulkEnergyDeviation_nonneg n M f v p u)) (integrable_const _)
      filter_upwards [bulkParameterLaw_ae] with v hv
      exact bulkEnergyDeviation_integrated_bound n M f v p hs hs1 (by norm_num) (fun j =>
        abs_le.mpr ⟨by linarith [(hv j).1],by linarith [(hv j).2]⟩)
    _ = _ := by simp

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


lemma bulk_rate_identity {x θ C : ℝ} (hx : 0<x) (hθ : θ≠0) (hC : 0≤C) :
    (Real.sqrt 6*(x^((3:ℝ)/8)*θ)+24*(x^((3:ℝ)/8)*θ)^2*x^(-(1:ℝ)/8)+
      4*Real.sqrt (C*x)/x^(-(1:ℝ)/8))/(x^((3:ℝ)/8)*θ*x^((3:ℝ)/8)) =
      Real.sqrt 6*x^(-(3:ℝ)/8)+(24*θ+4*Real.sqrt C/θ)*x^(-(1:ℝ)/8) := by
  have hp1 : x^(-(3:ℝ)/8)*x^((3:ℝ)/8)=1 := by rw [←Real.rpow_add hx]; norm_num
  have hp2 : x^((1:ℝ)/2) = x^(-(1:ℝ)/8)*x^(-(1:ℝ)/8)*(x^((3:ℝ)/8))^2 := by
    rw [← Real.rpow_mul_natCast hx.le,←Real.rpow_add hx,←Real.rpow_add hx]
    congr 1
    norm_num
  rw [Real.sqrt_mul hC,Real.sqrt_eq_rpow x, hp2]
  have h1 : x^((3:ℝ)/8)≠0 := (Real.rpow_pos_of_pos hx _).ne'
  have h2 : x^(-(1:ℝ)/8)≠0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp
  simp only [neg_div] at hp1
  linear_combination -(Real.sqrt 6*θ)*hp1

lemma bulkScale_sq_le (n : ℕ) : bulkScale (n+1)^2≤(n+1:ℕ) := by
  have hx : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  unfold bulkScale
  rw [←Real.rpow_mul_natCast (by positivity : (0:ℝ)≤(n+1:ℕ))]
  calc
    _ ≤ ((n+1:ℕ):ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = _ := Real.rpow_one _

lemma bulkNormalizedDeviation_nonneg (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1)) (v : ℕ→ℝ) :
    0≤bulkNormalizedDeviation n M f p v := by
  unfold bulkNormalizedDeviation
  exact div_nonneg (bulkDegreeDeviation_nonneg n M f p v)
    (mul_nonneg (bulkCoefficient_pos n p).le (by unfold bulkScale; positivity))

lemma bulkNormalizedDeviation_integral_bound (n M : ℕ) (f : ℝ→ᵇℝ) (p : Fin (n+1))
    {A : ℝ} (hA : 0≤A) (hM : (M:ℝ)≤A*(n+1:ℕ)) :
    (∫ v, bulkNormalizedDeviation n M f p v ∂bulkParameterLaw)≤bulkDeviationRate A f p.val (n+1:ℕ) := by
  let x : ℝ := (n+1:ℕ)
  let s : ℝ := x^(-(1:ℝ)/8)
  let C := Real.pi^2/8*3^2+A*(2*‖f‖)^2
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : 1≤x := by dsimp [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hs : 0 < s := Real.rpow_pos_of_pos hx _
  have hs1 : s≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hC : 0≤C := by dsimp [C]; positivity
  have hV : Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2≤C*x := by
    calc
      _ ≤ Real.pi^2/8*3^2*x+(A*x)*(2*‖f‖)^2 :=
        add_le_add (mul_le_mul_of_nonneg_left (bulkScale_sq_le n) (by positivity))
          (mul_le_mul_of_nonneg_right hM (sq_nonneg _))
      _ = _ := by dsimp [C]; ring
  have hden : 0<bulkCoefficient (n+1) p*bulkScale (n+1) := mul_pos (bulkCoefficient_pos n p) (Real.rpow_pos_of_pos hx _)
  unfold bulkNormalizedDeviation
  rw [integral_div]
  calc
    _ ≤ (Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (Real.pi^2/8*3^2*bulkScale (n+1)^2+M*(2*‖f‖)^2)/s)/
          (bulkCoefficient (n+1) p*bulkScale (n+1)) :=
      div_le_div_of_nonneg_right (bulkDegreeDeviation_integral_bound n M f p hs hs1) hden.le
    _ ≤ (Real.sqrt 6*bulkCoefficient (n+1) p+24*bulkCoefficient (n+1) p^2*s+
        4*Real.sqrt (C*x)/s)/(bulkCoefficient (n+1) p*bulkScale (n+1)) := by gcongr
    _ = _ := bulk_rate_identity hx (by positivity) hC

lemma bulkDeviationRate_tendsto (A : ℝ) (f : ℝ→ᵇℝ) (p : ℕ) :
    Tendsto (fun n : ℕ => bulkDeviationRate A f p (n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n+1:ℕ) : ℕ→ℝ) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/8)).comp hN
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)).comp hN
  unfold bulkDeviationRate
  convert (h3.const_mul (Real.sqrt 6)).add (h1.const_mul (24*(2:ℝ)^(-((p+1:ℕ):ℤ))+
    4*Real.sqrt (Real.pi^2/8*3^2+A*(2*‖f‖)^2)/(2:ℝ)^(-((p+1:ℕ):ℤ)))) using 1 <;> norm_num

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

lemma bulkDeviationAt_integral_tendsto_oai (M : ℕ→ℕ) (f : ℝ→ᵇℝ) {A : ℝ}
    (hA : 0≤A) (hM : ∀ n, (M n:ℝ)≤A*(n+1:ℕ)) (p : ℕ) :
    Tendsto (fun n => ∫ v, bulkDeviationAt n (M n) f p v ∂bulkParameterLaw) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (bulkDeviationAt_nonneg n (M n) f p)) _
    (bulkDeviationRate_tendsto A f p)
  filter_upwards [eventually_ge_atTop p] with n hn
  have hp : p<n+1 := Nat.lt_succ_of_le hn
  simp only [bulkDeviationAt,dite_eq_left hp]
  exact bulkNormalizedDeviation_integral_bound n (M n) f ⟨p,hp⟩ hA (hM n)

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto_oai := @OAI.SphericalPerceptronFreeEnergy.bulkDeviationAt_integral_tendsto_oai
