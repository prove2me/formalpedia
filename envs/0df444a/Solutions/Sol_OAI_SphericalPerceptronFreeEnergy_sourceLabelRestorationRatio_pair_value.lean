-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:50:56.884999+00:00
-- url     : https://prove2.me/submissions/44a0e46f-435e-425e-9672-d7d38e6515c2

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedTerminalPairMean_integral

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

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

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

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_DecoratedWeightedTotal
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

lemma fractionalLogMoment_centered {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b : ℝ} (hb : b ≠ 0) {f : X×S → ℝ} (x : X)
    (hI : Integrable (fun s => Real.exp (b*f (x,s))) ν) :
    Integrable (fun s => Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x))) ν ∧
    (∫ s, Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) ∂ν) = 1 := by
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hfac (s : S) : Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) =
      Real.exp (-(Real.log (∫ t, Real.exp (b*f (x,t)) ∂ν)))*Real.exp (b*f (x,s)) := by
    rw [← Real.exp_add]
    congr 1
    unfold fractionalLogMoment
    field_simp
    ring
  constructor
  · simp_rw [hfac]
    exact hI.const_mul _
  · simp_rw [hfac]
    rw [integral_const_mul,Real.exp_neg,Real.exp_log hp,inv_mul_cancel₀ hp.ne']

lemma finiteCascadeShifts_normalized_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0) (H : X → ℝ)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    rcases hI with ⟨hroot,htail⟩
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) htail j) i
    intro x
    exact fractionalLogMoment_centered ν (hz 0)
      (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x (hroot x)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ProductMarkLaw
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

lemma fractional_log_moment_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ}
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν)
    (hIg : Integrable (fun t => Real.exp (b*g t)) ρ) :
    Real.log (∫ p, Real.exp (b*(f p.1+g p.2)) ∂ν.prod ρ)/b =
      Real.log (∫ s, Real.exp (b*f s) ∂ν)/b + Real.log (∫ t, Real.exp (b*g t) ∂ρ)/b := by
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun s => Real.exp (b*f s)) (fun t => Real.exp (b*g t)),Real.log_mul (integral_exp_pos hIf).ne' (integral_exp_pos hIg).ne',add_div]

theorem finiteCascadeLogRecursion_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    finiteCascadeLogRecursion (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
        (fun q => H q.1+G q.2) (x,y) =
      finiteCascadeLogRecursion ν step₁ n z H x + finiteCascadeLogRecursion ρ step₂ n z G y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    conv_lhs => rw [finiteCascadeLogRecursion]
    change Real.log (∫ p : S×T, Real.exp (z 0 *
      finiteCascadeLogRecursion (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n (fun i => z i.succ)
          (fun q => H q.1+G q.2) (step₁ (x,p.1),step₂ (y,p.2))) ∂(ν : Measure S).prod (ρ : Measure T))/(z 0) = _
    simp_rw [ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail]
    exact fractional_log_moment_prod_add (ν : Measure S) (ρ : Measure T) (z 0) (hHroot x) (hGroot y)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_CascadeIndependentTilt
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma finiteCascadeFractionalIntegrable_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i) {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) :
    finiteCascadeFractionalIntegrable (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2)))
      (fun q => H q.1+G q.2) n z := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    constructor
    · intro x
      simp_rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n
        (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail,mul_add,Real.exp_add]
      exact (hHroot x.1).mul_prod (hGroot x.2)
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_InfinitePiSplit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma infinitePi_sumPiEquivProdPi_symm {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.infinitePi fun i => μ (.inl i)).prod
      (Measure.infinitePi fun i => μ (.inr i))).map
        (MeasurableEquiv.sumPiEquivProdPi X).symm = Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have he : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' ((s : Set (ι ⊕ κ)).pi t) =
      (s.toLeft : Set ι).pi (fun i => t (.inl i)) ×ˢ
      (s.toRight : Set κ).pi (fun i => t (.inr i)) := by
    ext p
    simp only [mem_preimage,mem_pi,mem_prod,Finset.mem_coe,Finset.mem_toLeft,Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi,fun i hi => h (.inr i) hi⟩
    · rintro ⟨h₁,h₂⟩ (i|i) hi
      · exact h₁ i hi
      · exact h₂ i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun _ _ => ht _),
    Measure.infinitePi_pi _ (fun _ _ => ht _),Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

lemma infinitePi_zip {ι A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure A) (ν : ι → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B s
  have hm : Measurable (Prod.map (Finset.restrict s : (ι → A) → (s → A))
      (Finset.restrict s : (ι → B) → (s → B))) := by fun_prop
  have hp : ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p (i : s) => (p.1 i,p.2 i)) = Measure.pi (fun i : s => (μ i).prod (ν i)) := by
    calc
      _ = (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
        (Prod.map (Finset.restrict s) (Finset.restrict s))).map e.symm := by
          rw [Measure.map_map e.symm.measurable hm]
          rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
          Measure.infinitePi_map_restrict,Measure.infinitePi_map_restrict]
        exact (measurePreserving_arrowProdEquivProdArrow A B s (fun i => μ i) (fun i => ν i)).symm.map_eq
  have he : (fun p : (ι → A) × (ι → B) => fun i => (p.1 i,p.2 i)) ⁻¹'
      (s : Set ι).pi t =
      (fun p : (ι → A) × (ι → B) => fun i : s => (p.1 i,p.2 i)) ⁻¹'
        (univ.pi (fun i : s => t i)) := by
    ext p
    simp [Set.mem_pi]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ => ht i),he,
    ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi fun i : s => ht i),hp,Measure.pi_pi]
  exact Finset.prod_attach s (fun i => (μ i).prod (ν i) (t i))

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

lemma indexedMarksFromVertices_measurable {S : Type} [MeasurableSpace S] (n : ℕ) :
    Measurable (indexedMarksFromVertices (S := S) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply (i,j,Sum.inl ())).prodMk
      (ih.comp (Measurable.of_eval fun vertex => measurable_pi_apply (i,j,Sum.inr vertex)))

lemma infinitePi_sumPiEquivProdPi {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map (MeasurableEquiv.sumPiEquivProdPi X) =
      (Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  exact (infinitePi_sumPiEquivProdPi_symm μ).symm

lemma indexedMarksFromVertices_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) :
    (Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))).map
      (indexedMarksFromVertices n) = indexedCascadeMarksLaw ν n := by
  induction n with
  | zero => simp [indexedMarksFromVertices,indexedCascadeMarksLaw,Measure.map_const]
  | succ n ih =>
    let Q := Measure.infinitePi (fun _ : Unit ⊕ IndexedVertex n => (ν : Measure S))
    let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
    let a : (Unit ⊕ IndexedVertex n → S) → S×IndexedCascadeMarks S n := fun f =>
      (f (.inl ()),indexedMarksFromVertices n (fun v => f (.inr v)))
    have ha : Measurable a := (measurable_pi_apply _).prodMk
      ((indexedMarksFromVertices_measurable n).comp (Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)))
    have haQ : Q.map a = (ν : Measure S).prod M := by
      let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ IndexedVertex n => S)
      have he : a = (Prod.map (fun f : Unit → S => f ()) (indexedMarksFromVertices n)) ∘ e := rfl
      rw [he,← Measure.map_map ((measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)) e.measurable,infinitePi_sumPiEquivProdPi]
      rw [← Measure.map_prod_map _ _ (by fun_prop) (indexedMarksFromVertices_measurable n),ih]
      rw [(measurePreserving_eval_infinitePi (fun _ : Unit => (ν : Measure S)) ()).map_eq]
    let e := MeasurableEquiv.curry ℕ (ℕ × (Unit ⊕ IndexedVertex n)) S
    let r := MeasurableEquiv.curry ℕ (Unit ⊕ IndexedVertex n) S
    let c : (IndexedVertex (n+1) → S) → ℕ → ℕ → Unit ⊕ IndexedVertex n → S :=
      fun f i j v => f (i,j,v)
    have hc : Measurable c := by fun_prop
    have hcQ : (Measure.infinitePi (fun _ : IndexedVertex (n+1) => (ν : Measure S))).map c =
        Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Q)) := by
      have he : c = (fun f i => r (f i)) ∘ e := rfl
      rw [he,← Measure.map_map (by fun_prop) e.measurable]
      dsimp only [e, IndexedVertex]
      rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S)),
        Measure.infinitePi_map_pi _ (fun _ => r.measurable)]
      dsimp only [r]
      simp_rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S))]
      rfl
    have he : indexedMarksFromVertices (S := S) (n+1) = (fun f i j => a (f i j)) ∘ c := rfl
    rw [he,← Measure.map_map (by fun_prop) hc,hcQ]
    rw [Measure.infinitePi_map_pi _ (f := fun _ (f : ℕ → Unit ⊕ IndexedVertex n → S) => fun j => a (f j))
      (fun _ => Measurable.of_eval fun column => ha.comp (measurable_pi_apply column))]
    simp_rw [Measure.infinitePi_map_pi _ (fun _ => ha),haQ]
    rfl

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

end

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma mem_interior_integrableExpSet_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ=univ := Set.eq_univ_of_forall hX
  simp [he]

omit [IsProbabilityMeasure μ] in
lemma cgf_analytic_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    AnalyticAt ℝ (cgf X μ) t :=
  analyticAt_cgf (mem_interior_integrableExpSet_of_all μ hX t)

lemma entropicMean_eq_div (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {p : ℝ} (hp : p ≠ 0) : entropicMean μ p X=cgf X μ p/p := by
  rw [entropicMean,intervalIntegral.integral_comp_mul_left _ hp]
  simp only [mul_zero,mul_one]
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (cgf_analytic_of_all μ hX t).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _),cgf_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma entropicMean_zero (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    entropicMean μ 0 X=∫ ω, X ω ∂μ := by
  simp [entropicMean,deriv_cgf_zero (mem_interior_integrableExpSet_of_all μ hX 0)]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

lemma gaussian_integrable_exp_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a σ : ℝ) (x : E) :
    Integrable (fun y : E => Real.exp (a*f (x+σ • y))) μ := by
  have hbound (y : E) : a*f (x+σ • y) ≤ |a| *|f x|+(|a| *L*|σ|)*‖y‖ := by
    have hl := hf.dist_le_mul (x+σ • y) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hl
    have hn := abs_add_le (f (x+σ • y)-f x) (f x)
    rw [sub_add_cancel] at hn
    have hmul := mul_le_mul_of_nonneg_left (le_trans hn (add_le_add hl le_rfl)) (abs_nonneg a)
    have hle := le_abs_self (a*f (x+σ • y))
    rw [abs_mul] at hle
    nlinarith
  have hfc := hf.continuous
  apply ((gaussian_integrable_exp_norm μ (|a| *L*|σ|)).const_mul
    (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (hbound y)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

lemma integrable_of_all_exp (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) :
    Integrable X μ :=
  (memLp_of_mem_interior_integrableExpSet (mem_interior_integrableExpSet_of_all μ hX 0) 1).integrable (by simp)

omit [IsProbabilityMeasure μ] in
lemma all_exp_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) (c : ℝ) :
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t*(X ω+c))) μ := by
  intro t
  simpa only [mul_add,Real.exp_add] using (hX t).mul_const (Real.exp (t*c))

lemma entropicMean_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (p c : ℝ) : entropicMean μ p (fun ω => X ω+c)=entropicMean μ p X+c := by
  by_cases hp : p=0
  · subst p
    rw [entropicMean_zero μ (all_exp_add_const μ hX c),entropicMean_zero μ hX,
      integral_add (integrable_of_all_exp μ hX) (integrable_const c),integral_const]
    simp
  · rw [entropicMean_eq_div μ (all_exp_add_const μ hX c) hp,entropicMean_eq_div μ hX hp]
    simp only [cgf,mgf_add_const]
    rw [Real.log_mul (ne_of_gt (mgf_pos (hX p))) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    field_simp

lemma entropicMean_mono_variable
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hXY : X ≤ᵐ[μ] Y) {p : ℝ} (hp : 0 ≤ p) :
    entropicMean μ p X ≤ entropicMean μ p Y := by
  rcases hp.eq_or_lt with hp|hp
  · subst p
    rw [entropicMean_zero μ hX,entropicMean_zero μ hY]
    exact integral_mono_ae (integrable_of_all_exp μ hX) (integrable_of_all_exp μ hY) hXY
  · rw [entropicMean_eq_div μ hX (ne_of_gt hp),entropicMean_eq_div μ hY (ne_of_gt hp)]
    apply div_le_div_of_nonneg_right _ hp.le
    exact Real.log_le_log (mgf_pos (hX p)) (mgf_mono_of_nonneg hXY hp.le (hY p))

lemma entropicMean_bounded_difference
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    {C p : ℝ} (hp : 0 ≤ p) (hXY : ∀ᵐ ω ∂μ, |X ω-Y ω| ≤ C) :
    |entropicMean μ p X-entropicMean μ p Y| ≤ C := by
  have h1 : X ≤ᵐ[μ] (fun ω => Y ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).2
    linarith
  have h2 : Y ≤ᵐ[μ] (fun ω => X ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).1
    linarith
  have H1 := entropicMean_mono_variable μ hX (all_exp_add_const μ hY C) h1 hp
  have H2 := entropicMean_mono_variable μ hY (all_exp_add_const μ hX C) h2 hp
  rw [entropicMean_add_const μ hY] at H1
  rw [entropicMean_add_const μ hX] at H2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_linear_shift {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : E →L[ℝ] E) (a : ℝ) (x : E) :
    Integrable (fun y => Real.exp (a*f (x+A y))) μ := by
  have hA : LipschitzWith ‖A‖₊ (fun y => x+A y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using A.lipschitz.dist_le_mul y z
  have hg := hf.comp hA
  simpa using gaussian_integrable_exp_lipschitz μ hg a 1 (0:E)

lemma gaussianLinearEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {b : ℝ} (hb : 0 ≤ b) (A : E →L[ℝ] E) :
    LipschitzWith L (gaussianLinearEntropic μ b A f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianLinearEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a x)
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a y) hb
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+A z) (y+A z)

lemma gaussianLinearBackward_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (ℝ×(E →L[ℝ] E)))
    (hl : ∀ c ∈ l, 0 ≤ c.1) : LipschitzWith L (gaussianLinearBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons c l ih =>
    exact gaussianLinearEntropic_lipschitz μ
      (ih (fun d hd => hl d (List.mem_cons_of_mem c hd))) (hl c List.mem_cons_self) c.2

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_nonneg (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ linearCascadeWord A k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearRecursion_realization (ν : ProbabilityMeasure E) [IsGaussian (ν:Measure E)]
    (A : ℕ → E →L[ℝ] E) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion ν (gaussianLinearMarkStep A) k z (fun x => f (x 0)) x=
        gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k z) f (x k)) ∧
    finiteCascadeFractionalIntegrable ν (gaussianLinearMarkStep A) (fun x => f (x 0)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    let g := gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := gaussianLinearBackward_lipschitz (ν:Measure E) hf _
      (linearCascadeWord_nonneg A k _ (fun i => (hz i.succ).le))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,gaussianLinearMarkStep,
        linearCascadeWord,gaussianLinearBackward,gaussianLinearEntropic]
      rw [entropicMean_eq_div (ν:Measure E)
        (fun a => gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) a (x (k+1)))
        (hz 0).ne']
      rfl
    · constructor
      · intro x
        simp only [H.1,gaussianLinearMarkStep]
        exact gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) (z 0) (x (k+1))
      · exact H.2

end

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

lemma indexedGaussianDisorder_measurable (n : ℕ) (I : Type) [Fintype I] :
    Measurable (indexedGaussianDisorder n I) := by
  exact ((measurable_pi_apply (Sum.inl ())).comp (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))).prodMk
    ((indexedMarksFromVertices_measurable n).comp
      ((Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)).comp
        (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))))

lemma indexedGaussianDisorder_law (n : ℕ) (I : Type) [Fintype I] :
    countableGaussianLaw.map (indexedGaussianDisorder n I) =
      (stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) n) := by
  let E := EuclideanSpace ℝ I
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : SharedVertex n => E)
  let a := Prod.map (fun f : Unit → E => f ()) (indexedMarksFromVertices (S := E) n)
  have ha : Measurable a := (measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)
  have he : indexedGaussianDisorder n I = (a ∘ e) ∘ countableGaussianVectors (V := SharedVertex n) (I := I) := rfl
  rw [he,← Measure.map_map (ha.comp e.measurable) countableGaussianVectors_measurable,
    countableGaussianVectors_law,← Measure.map_map ha e.measurable,infinitePi_sumPiEquivProdPi]
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply ()) (indexedMarksFromVertices_measurable n),
    Measure.infinitePi_map_eval]
  exact congrArg (Measure.prod (stdGaussian E)) (indexedMarksFromVertices_law (gaussianMarkLaw (E := E)) n)

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E] in
lemma indexedLeafState_gaussianLinear (A : ℕ → E →L[ℝ] E) (n : ℕ)
    (x : ℕ → E) (f : IndexedVertex n → E) (l : IndexedLeaf n) (j : ℕ) :
    indexedLeafState (gaussianLinearMarkStep A) n (x,indexedMarksFromVertices n f) l j =
      x (j+n) + ∑ i : Fin n, A (j+n-1-i.val) (f (indexedLeafVertex n l i)) := by
  induction n generalizing x j with
  | zero => simp [indexedLeafState]
  | succ n ih =>
    change indexedLeafState (gaussianLinearMarkStep A) n
      (gaussianLinearMarkStep A (x,f (l.1,l.2.1,Sum.inl ())),
        indexedMarksFromVertices n (fun v => f (l.1,l.2.1,Sum.inr v))) l.2.2 j = _
    rw [ih,Fin.sum_univ_succ]
    simp only [gaussianLinearMarkStep,indexedLeafVertex,Fin.cases_zero,Fin.cases_succ,
      Fin.val_zero,Fin.val_succ,Nat.sub_zero]
    rw [show j+(n+1)-1 = j+n by omega]
    have he : (∑ i : Fin n, A (j+n-1-i.val) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i)))) =
        ∑ i : Fin n, A (j+n-(i.val+1)) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      omega
    rw [he]
    simp only [add_assoc]

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_diagonal_identity (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (g : ℕ → ℝ) (x : S×IndexedLeaf n) :
    countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
      (indexedGaussianRowLength (I := I) n) g x =
    inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
      ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
        (indexedGaussianDisorder n I g).2) x.2 0) := by
  rw [indexedGaussianRow_field]
  change _ = inner ℝ (V x.1) (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
    ((fun _ => diagonalMark root (countableGaussianVectors g (Sum.inl ()))),
      indexedMarksFromVertices n (fun v => countableGaussianVectors g (Sum.inr v))) x.2 0)
  rw [indexedLeafState_gaussianLinear,inner_add_right,inner_sum,Fin.sum_univ_succ]
  simp only [Nat.zero_add,hierarchyRowCoefficients,Fin.cases_zero,Fin.cases_succ,
    indexedLeafSharedVertex]
  congr 1
  · simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (root i * g (countableCoordinate (Sum.inl (),i))) * V x.1 i
    ring
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [PiLp.inner_apply,diagonalMark_apply,countableGaussianVectors]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = (step (n-1-d.val) i * g (countableCoordinate (Sum.inr (indexedLeafVertex n x.2 d),i))) * V x.1 i
    ring

end

section Partition
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_lipschitz {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K : ℝ} {C : ℝ≥0}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) :
    LipschitzWith C (vectorLogPartition ρ W V) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,vectorLogPartition,vectorPartition]
  apply abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (vectorPartition_integrable ρ hWm hVm hW hV y)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (vectorPartition_pos ρ hWm hVm hW hV y)
  intro s
  simp only [add_sub_add_left_eq_sub,← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg _))
end Partition

lemma sourceEnrichedFeature_norm (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (x : NormalizedSpin N) : ‖sourceEnrichedFeature N p u x‖=enrichedFeatureBound N u := by
  rw [sourceEnrichedFeature,enrichedFeature_norm,Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

lemma enrichedTerminal_lipschitz (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (htop : ℝ) : LipschitzWith (enrichedFeatureBound (n+1) u)
      (enrichedTerminal n M f g p u htop) := by
  have hW : Continuous (normalizedPatternEnergy (n+1) M f g) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp
    (continuous_const.prodMk continuous_id)
  have hV : Continuous (fun x : NormalizedSpin (n+1) =>
      innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) :=
    (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hL := vectorLogPartition_lipschitz (unitSphereLaw (n+1)) hW.measurable hV.measurable
    (normalizedPatternEnergy_bound (n+1) M f g)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm])
  intro x y
  simpa only [enrichedTerminal,edist_sub_right] using hL x y

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedGibbsPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace SphericalPerceptronFreeEnergy

variable {S I : Type} [MeasurableSpace S] [Fintype I]
variable (ρ : Measure S) [IsProbabilityMeasure ρ]
variable {W : S → ℝ} {V : S → EuclideanSpace ℝ I}
variable (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
variable (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)

include hWm hVm hW hV

lemma vectorPartition_exp_terminal (c : ℝ) (a : EuclideanSpace ℝ I) :
    (∫ s, Real.exp (W s+inner ℝ (V s) a-c) ∂ρ) =
      Real.exp (vectorLogPartition ρ W (fun s => innerSL ℝ (V s)) a-c) := by
  have hm : Measurable (fun s => innerSL ℝ (V s)) := (innerSL ℝ).continuous.measurable.comp hVm
  have hb : ∀ s, ‖innerSL ℝ (V s)‖ ≤ C := by simpa only [innerSL_apply_norm] using hV
  simp only [Real.exp_sub,integral_div,vectorLogPartition]
  rw [Real.exp_log (vectorPartition_pos ρ hWm hm hW hb a)]
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

lemma enrichedIncrementMap_profile {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) :
    enrichedIncrementMap p d h j = diagonalMark (profileGaussianStep (enrichedCoordinateLevel p d h) j) := by
  by_cases hj : j<k
  · rw [enrichedIncrementMap,dite_eq_left hj]
    congr 1
    funext i
    simp only [profileGaussianStep,dite_eq_left hj]
  · apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [enrichedIncrementMap,profileGaussianStep,hj,diagonalMark_apply]

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

lemma gibbsProbabilityKernel_congr_apply {B : Type*} [MeasurableSpace B]
    (η : Kernel B S) [IsMarkovKernel η] (G : B→S→ℝ)
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    (a : A) (b : B) (he : κ a=η b) (hE : H a=G b) :
    gibbsProbabilityKernel κ H a=gibbsProbabilityKernel η G b := by
  by_cases hi : Integrable (fun x => Real.exp (H a x)) (κ a)
  · have hi' : Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_integrable η G hG b hi',he,hE]
  · have hi' : ¬Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_not_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_not_integrable η G hG b hi',he]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CountableFreshMoment
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

variable {S : Type} [MeasurableSpace S] {k : ℕ}

lemma labelProfileField_marked_state {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    labelProfileField q g x =
      inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))
        (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark
          (profileGaussianStep (fun l (_ : Fin 1) => q l) j))) k
          ((fun _ => diagonalMark (profileGaussianRoot (fun l (_ : Fin 1) => q l))
            (indexedGaussianDisorder k (Fin 1) g).1),
            (indexedGaussianDisorder k (Fin 1) g).2) x.2 0) :=
  indexedGaussianRow_diagonal_identity k _ _ _ g x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma sourceFresh_exp_ae (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceLabelLevel_val_injective (k : ℕ) :
    Function.Injective (fun l : Fin (k+1) => (sourceLabelLevel k l).val) := by
  intro i j hij
  apply Fin.ext
  have h : (i.val:ℝ)=(j.val:ℝ) := by
    apply (div_left_inj' (show (k+1:ℕ)≠(0:ℝ) by positivity)).mp
    exact hij
  exact_mod_cast h

lemma labelProfileInterpolant_node {k : ℕ} (q : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    labelProfileInterpolant q (sourceLabelLevel k l)=q l := by
  exact Lagrange.eval_interpolate_at_node q (sourceLabelLevel_val_injective k).injOn (Finset.mem_univ l)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedMarkProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

section
variable {S T : Type} [MeasurableSpace S] [MeasurableSpace T]

lemma indexedMarksZip_measurable (n : ℕ) : Measurable (indexedMarksZip (S:=S) (T:=T) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact ((by fun_prop : Measurable (fun p : IndexedCascadeMarks S (n+1) × IndexedCascadeMarks T (n+1) =>
      ((p.1 i j).1,(p.2 i j).1)))).prodMk (ih.comp (by fun_prop))

lemma indexedMarksZip_vertices (n : ℕ) (a : IndexedVertex n→S) (b : IndexedVertex n→T) :
    indexedMarksZip n (indexedMarksFromVertices n a,indexedMarksFromVertices n b)=
      indexedMarksFromVertices n (fun v => (a v,b v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i j
    exact congrArg (fun x => ((a (i,j,.inl ()),b (i,j,.inl ())),x))
      (ih (fun v => a (i,j,.inr v)) (fun v => b (i,j,.inr v)))

lemma indexedMarksZip_law (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (n : ℕ) :
    ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
      (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))).map (indexedMarksZip n)=
        (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)) := by
  let A := Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))
  let B := Measure.infinitePi (fun _ : IndexedVertex n => (ρ : Measure T))
  have he : (fun p : (IndexedVertex n→S)×(IndexedVertex n→T) =>
      indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=
        indexedMarksFromVertices n ∘ (fun p v => (p.1 v,p.2 v)) := by
    funext p
    exact indexedMarksZip_vertices n p.1 p.2
  rw [← indexedMarksFromVertices_law ν n,← indexedMarksFromVertices_law ρ n,
    Measure.map_prod_map _ _ (indexedMarksFromVertices_measurable n) (indexedMarksFromVertices_measurable n),
    Measure.map_map (indexedMarksZip_measurable n)
      ((indexedMarksFromVertices_measurable n).prodMap (indexedMarksFromVertices_measurable n))]
  change (A.prod B).map (fun p => indexedMarksZip n (indexedMarksFromVertices n p.1,indexedMarksFromVertices n p.2))=_
  rw [he,← Measure.map_map (indexedMarksFromVertices_measurable n) (by fun_prop)]
  dsimp [A,B]
  rw [infinitePi_zip]
  exact indexedMarksFromVertices_law (productMarkLaw ν ρ) n

lemma indexedLeafState_product {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (step₁ : X×S→X) (step₂ : Y×T→Y)
    (n : ℕ) (x : X) (y : Y) (a : IndexedCascadeMarks S n) (b : IndexedCascadeMarks T n)
    (l : IndexedLeaf n) :
    indexedLeafState (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n
      ((x,y),indexedMarksZip n (a,b)) l=
        (indexedLeafState step₁ n (x,a) l,indexedLeafState step₂ n (y,b) l) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _ _

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LeafFreshLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

lemma freshRoot_swap_nested {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun t : A×(B×C) => (t.2.1,(t.1,t.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν ρ)
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
    (MeasurePreserving.id ρ)
  exact (measurePreserving_prodAssoc ν μ ρ).comp (h₂.comp h₁)

lemma freshRoot_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving (fun t : (A×B)×(C×D) => ((t.1.1,t.2.1),(t.1.2,t.2.2)))
      ((μ.prod ν).prod (ρ.prod σ)) ((μ.prod ρ).prod (ν.prod σ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h₂ := (MeasurePreserving.id μ).prod (freshRoot_swap_nested ν ρ σ)
  have h₃ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ (ν.prod σ))
  exact h₃.comp (h₂.comp h₁)

lemma freshRoot_five_regroup {B X S Y T : Type*}
    [MeasurableSpace B] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y] [MeasurableSpace T]
    (β : Measure B) (μ : Measure X) (ν : Measure S) (ρ : Measure Y) (σ : Measure T)
    [SFinite β] [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite σ] :
    MeasurePreserving
      (fun t : B×((X×S)×(Y×T)) => ((t.2.1.1,t.2.2.1),(t.1,(t.2.1.2,t.2.2.2))))
      (β.prod ((μ.prod ν).prod (ρ.prod σ))) ((μ.prod ρ).prod (β.prod (ν.prod σ))) := by
  exact (freshRoot_swap_nested β (μ.prod ρ) (ν.prod σ)).comp
    ((MeasurePreserving.id β).prod (freshRoot_four_shuffle μ ν ρ σ))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma tiltedMarkKernel_markov (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedMarkKernel ν z F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [tiltedMarkKernel,Kernel.withDensity_apply _ ((hF.const_mul z).exp.ennreal_ofReal)]
  simp only [Kernel.const_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI x)
    (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),hM x]
  exact ENNReal.ofReal_one

lemma tiltedStateStep_markov (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedStateStep ν step z F) := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  exact Kernel.IsMarkovKernel.map _ hs

lemma tiltedStateStep_lintegral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1)
    (h : X → ℝ≥0∞) (hh : Measurable h) (x : X) :
    (∫⁻ y, h y ∂tiltedStateStep ν step z F x) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (z*F (x,s)))*h (step (x,s)) ∂ν := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  rw [tiltedStateStep,Kernel.lintegral_map _ hs _ hh,
    Kernel.lintegral_id_prod (show Measurable (fun p : X×S => h (step p)) from hh.comp hs)]
  exact Kernel.lintegral_withDensity _ ((hF.const_mul z).exp.ennreal_ofReal) x
    ((hh.comp hs).comp (measurable_const.prodMk measurable_id))

lemma pathOneKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) : IsMarkovKernel (pathOneKernel n κ) := by
  induction n with
  | zero => dsimp [pathOneKernel]; infer_instance
  | succ n ih =>
    have := hκ 0
    have := ih (fun i => κ i.succ) (fun i => hκ i.succ)
    dsimp [pathOneKernel]; infer_instance

lemma pathPairKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (d : Fin (n+1)) :
    IsMarkovKernel (pathPairKernel n κ d) := by
  induction n with
  | zero => dsimp [pathPairKernel]; infer_instance
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · have := pathOneKernel_markov (n+1) κ hκ
      simp only [pathPairKernel,Fin.cases_zero]; infer_instance
    · have := hκ 0
      have := ih (fun i => κ i.succ) (fun i => hκ i.succ) j
      simp only [pathPairKernel,Fin.cases_succ]; infer_instance

lemma path_bounded_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma pathMean_succ (n : ℕ) (κ : Fin (n+1) → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (x : X) :
    pathMean (n+1) κ f x = ∫ y, pathMean n (fun i => κ i.succ) f y ∂κ 0 x := by
  have := hκ 0
  have := pathOneKernel_markov n (fun i => κ i.succ) (fun i => hκ i.succ)
  exact Kernel.integral_comp (path_bounded_integrable _ f hf C hb)

lemma pathCorrelation_zero (n : ℕ) (κ : Fin n → Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (f : X → ℝ) (hf : Measurable f) (x : X) :
    pathCorrelation n κ f 0 x = (pathMean n κ f x)^2 := by
  cases n with
  | zero =>
    simp only [pathCorrelation,pathPairKernel,Kernel.deterministic_apply,pathMean,pathOneKernel,
      Kernel.id_apply]
    rw [integral_dirac' (fun y : X×X => f y.1*f y.2) (x,x)
      (show StronglyMeasurable (fun y : X×X => f y.1*f y.2) from
        ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).stronglyMeasurable),
      integral_dirac' _ _ hf.stronglyMeasurable,pow_two]
  | succ n =>
    have := pathOneKernel_markov (n+1) κ hκ
    simp only [pathCorrelation,pathPairKernel,Fin.cases_zero,Kernel.prod_apply]
    rw [integral_prod_mul]
    exact (pow_two _).symm

lemma pathCorrelation_succ (n : ℕ) (κ : Fin (n+1) → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) (d : Fin (n+1)) (x : X) :
    pathCorrelation (n+1) κ f d.succ x =
      ∫ y, pathCorrelation n (fun i => κ i.succ) f d y ∂κ 0 x := by
  have := hκ 0
  have := pathPairKernel_markov n (fun i => κ i.succ) (fun i => hκ i.succ) d
  simp only [pathCorrelation,pathPairKernel,Fin.cases_succ]
  apply Kernel.integral_comp
  apply path_bounded_integrable _ _ ((hf.comp measurable_fst).mul (hf.comp measurable_snd)) (C^2)
  intro y
  change |f y.1*f y.2| ≤ C^2
  rw [abs_mul,pow_two]
  exact mul_le_mul (hb y.1) (hb y.2) (abs_nonneg _) hC

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma pathMean_parallel (n : ℕ) (κ : Fin n → Kernel X X) (η : Fin n → Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ y, |g y| ≤ D) (x : X) (y : Y) :
    pathMean n (fun i => κ i ∥ₖ η i) (fun p => f p.1*g p.2) (x,y) =
      pathMean n κ f x * pathMean n η g y := by
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2| ≤ C*D := fun p => by
    simpa only [abs_mul, abs_of_nonneg hD] using
      mul_le_mul (hfB p.1) ((hgB p.2).trans (le_abs_self D)) (abs_nonneg _) hC
  induction n generalizing x y with
  | zero =>
    simp only [pathMean,pathOneKernel,Kernel.id_apply]
    rw [integral_dirac' _ _ hfg.stronglyMeasurable,
      integral_dirac' _ _ hf.stronglyMeasurable,integral_dirac' _ _ hg.stronglyMeasurable]
  | succ n ih =>
    have := hκ 0
    have := hη 0
    have hpar : ∀ i, IsMarkovKernel (κ i ∥ₖ η i) := by intro i; have := hκ i; have := hη i; infer_instance
    rw [pathMean_succ n _ hpar _ hfg (C*D) hB,
      pathMean_succ n κ hκ f hf C hfB,pathMean_succ n η hη g hg D hgB,
      Kernel.parallelComp_apply]
    simp_rw [ih _ _ (fun i => hκ i.succ) (fun i => hη i.succ)]
    exact integral_prod_mul _ _

lemma pathCorrelation_parallel (n : ℕ) (κ : Fin n → Kernel X X) (η : Fin n → Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfB : ∀ x, |f x| ≤ C) (hgB : ∀ y, |g y| ≤ D) (d : Fin (n+1)) (x : X) (y : Y) :
    pathCorrelation n (fun i => κ i ∥ₖ η i) (fun p => f p.1*g p.2) d (x,y) =
      pathCorrelation n κ f d x * pathCorrelation n η g d y := by
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hB : ∀ p : X×Y, |f p.1*g p.2| ≤ C*D := fun p => by
    rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC
  induction n generalizing x y with
  | zero =>
    have hd : d=0 := by apply Fin.ext; omega
    rw [hd,pathCorrelation_zero _ _ (fun i => Fin.elim0 i) _ hfg,
      pathCorrelation_zero _ κ hκ f hf,pathCorrelation_zero _ η hη g hg,
      pathMean_parallel 0 κ η hκ hη f g hf hg C D hC hD hfB hgB x y]
    ring
  | succ n ih =>
    have := hκ 0
    have := hη 0
    have hpar : ∀ i, IsMarkovKernel (κ i ∥ₖ η i) := by intro i; have := hκ i; have := hη i; infer_instance
    induction d using Fin.cases with
    | zero =>
      rw [pathCorrelation_zero _ _ hpar _ hfg,pathCorrelation_zero _ κ hκ f hf,
        pathCorrelation_zero _ η hη g hg,
        pathMean_parallel _ κ η hκ hη f g hf hg C D hC hD hfB hgB x y]
      ring
    | succ d =>
      rw [pathCorrelation_succ n _ hpar _ hfg (C*D) (mul_nonneg hC hD) hB,
        pathCorrelation_succ n κ hκ f hf C hC hfB,
        pathCorrelation_succ n η hη g hg D hD hgB,Kernel.parallelComp_apply]
      simp_rw [ih _ _ (fun i => hκ i.succ) (fun i => hη i.succ)]
      exact integral_prod_mul _ _

lemma finiteCascadeShifts_add_product (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    {H : X→ℝ} {G : Y→ℝ} (hH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) (p : (X×Y)×(S×T)) :
    finiteCascadeShifts (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
      (fun x => H x.1+G x.2) i p =
      finiteCascadeShifts ν step₁ n z H i (p.1.1,p.2.1)+
        finiteCascadeShifts ρ step₂ n z G i (p.1.2,p.2.2) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      simp only [finiteCascadeShifts,Fin.cases_zero]
      rw [finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ n _ (fun i => hz i.succ) hH.2 hG.2,
        finiteCascadeLogRecursion_add_product ν ρ step₁ step₂ (n+1) z hz hH hG]
      ring
    | succ i =>
      exact ih (fun i => z i.succ) (fun i => hz i.succ) hH.2 hG.2 i

lemma tiltedStateStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (z : ℝ) (F : X×S→ℝ) (G : Y×T→ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hGI : ∀ y, Integrable (fun t => Real.exp (z*G (y,t))) ρ)
    (hFM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν)=1)
    (hGM : ∀ y, (∫ t, Real.exp (z*G (y,t)) ∂ρ)=1) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) z
      (fun p => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) =
      tiltedStateStep ν step₁ z F ∥ₖ tiltedStateStep ρ step₂ z G := by
  have hs : Measurable (fun p : (X×Y)×(S×T) =>
      (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) := by fun_prop
  have hFG : Measurable (fun p : (X×Y)×(S×T) => F (p.1.1,p.2.1)+G (p.1.2,p.2.2)) := by fun_prop
  have hI (x : X×Y) : Integrable (fun s : S×T => Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))
      (productMarkLaw ν ρ) := by
    simp_rw [mul_add,Real.exp_add]
    exact (hFI x.1).mul_prod (hGI x.2)
  have hM (x : X×Y) : (∫ s : S×T, Real.exp (z*(F (x.1,s.1)+G (x.2,s.2)))
      ∂productMarkLaw ν ρ)=1 := by
    simp_rw [mul_add,Real.exp_add]
    change (∫ s : S×T, Real.exp (z*F (x.1,s.1))*Real.exp (z*G (x.2,s.2))
      ∂(ν : Measure S).prod (ρ : Measure T))=1
    exact (integral_prod_mul (fun s => Real.exp (z*F (x.1,s)))
      (fun t => Real.exp (z*G (x.2,t)))).trans (by rw [hFM,hGM,one_mul])
  have := tiltedStateStep_markov ν step₁ hs₁ z F hF hFI hFM
  have := tiltedStateStep_markov ρ step₂ hs₂ z G hG hGI hGM
  apply Kernel.ext
  intro x
  apply Measure.ext_of_lintegral
  intro f hf
  rw [tiltedStateStep_lintegral (productMarkLaw ν ρ) _ hs z _ hFG hI hM f hf,
    Kernel.parallelComp_apply,lintegral_prod _ hf.aemeasurable]
  have hi (a : X) := tiltedStateStep_lintegral ρ step₂ hs₂ z G hG hGI hGM
    (fun b => f (a,b)) (hf.comp (measurable_const.prodMk measurable_id)) x.2
  simp_rw [hi]
  have hm : Measurable (fun a : X => ∫⁻ t, ENNReal.ofReal (Real.exp (z*G (x.2,t)))*
      f (a,step₂ (x.2,t)) ∂ρ) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun p : X×T => ENNReal.ofReal (Real.exp (z*G (x.2,p.2)))*
      f (p.1,step₂ (x.2,p.2)))
    fun_prop
  rw [tiltedStateStep_lintegral ν step₁ hs₁ z F hF hFI hFM _ hm]
  change (∫⁻ s : S×T, ENNReal.ofReal (Real.exp (z*(F (x.1,s.1)+G (x.2,s.2))))*
    f (step₁ (x.1,s.1),step₂ (x.2,s.2)) ∂(ν : Measure S).prod (ρ : Measure T))=_
  rw [lintegral_prod]
  · apply lintegral_congr
    intro s
    rw [←lintegral_const_mul]
    · apply lintegral_congr
      intro t
      rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact mul_assoc _ _ _
    · fun_prop
  · fun_prop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma cascadeTiltedStep_parallel (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i) (H : X→ℝ) (G : Y→ℝ)
    (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (i : Fin n) :
    tiltedStateStep (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) (z i)
      (finiteCascadeShifts (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
          (fun x => H x.1+G x.2) i) =
      tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i) ∥ₖ
        tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i) := by
  have he := fun p => finiteCascadeShifts_add_product ν ρ step₁ step₂ n z hz hHI hGI i p
  rw [funext he]
  exact tiltedStateStep_parallel ν ρ step₁ step₂ hs₁ hs₂ (z i) _ _
    (finiteCascadeShifts_measurable ν step₁ hs₁ n z hH i)
    (finiteCascadeShifts_measurable ρ step₂ hs₂ n z hG i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step₁ n z (fun i => (hz i).ne') H hHI i x).2)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ρ step₂ n z (fun i => (hz i).ne') G hGI i x).2)

lemma cascadeTiltedStep_markov (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (i : Fin n) :
    IsMarkovKernel (tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) :=
  tiltedStateStep_markov ν step hs (z i) _ (finiteCascadeShifts_measurable ν step hs n z hH i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).2)

lemma pathCorrelation_one (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (d : Fin (n+1)) (x : X) : pathCorrelation n κ (fun _ => 1) d x=1 := by
  have := pathPairKernel_markov n κ hκ d
  simp [pathCorrelation]

lemma indexedTerminalEnergy_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) :
    Measurable (Function.uncurry (indexedTerminalEnergy step n H x)) :=
  hH.comp ((indexedLeafState_measurable hs n).comp
    ((measurable_const.prodMk measurable_fst.snd).prodMk measurable_snd))

lemma indexedTerminalPairMean_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) :
    Measurable (indexedTerminalPairMean step n H x d f) := by
  let κ := gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x)
  have hm (j : IndexedLeaf n×IndexedLeaf n→IndexedLeaf n) (hj : Measurable j) :
      Measurable (fun p : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n) =>
        f (indexedLeafState step n (x,p.1.2) (j p.2))) :=
    hf.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_const.prodMk measurable_fst.snd).prodMk (hj.comp measurable_snd)))
  have hcond : MeasurableSet {p : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n) |
      indexedCommonDepth n p.2.1 p.2.2=d} :=
    ((Set.to_countable {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).measurableSet).preimage measurable_snd
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov _ _
    (indexedTerminalEnergy_measurable step hs n H hH x)
  let F : (IndexedCascadeBase n×IndexedCascadeMarks S n)×(IndexedLeaf n×IndexedLeaf n)→ℝ :=
    fun p => if indexedCommonDepth n p.2.1 p.2.2=d then
      f (indexedLeafState step n (x,p.1.2) p.2.1)*f (indexedLeafState step n (x,p.1.2) p.2.2) else 0
  have hF : Measurable F :=
    Measurable.ite hcond ((hm Prod.fst measurable_fst).mul (hm Prod.snd measurable_snd)) measurable_const
  have hm' : Measurable (fun p => ∫ l, F (p,l) ∂(κ×ₖκ) p) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  unfold indexedTerminalPairMean
  simpa only [F,κ, Kernel.prod_apply] using hm'

lemma indexedTerminalPairMean_bound (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1)) (f : X→ℝ)
    (C : ℝ) (hC : 0≤C) (hB : ∀ x, |f x|≤C)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n) :
    |indexedTerminalPairMean step n H x d f p|≤C^2 := by
  have := gibbsProbabilityKernel_markov (indexedTerminalBaseKernel n)
    (indexedTerminalEnergy step n H x) (indexedTerminalEnergy_measurable step hs n H hH x)
  have hb : ∀ l : IndexedLeaf n×IndexedLeaf n,
      ‖(if indexedCommonDepth n l.1 l.2=d then
        f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)‖≤C^2 := by
    intro l
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,pow_two]
      exact mul_le_mul (hB _) (hB _) (abs_nonneg _) hC
    · simp only [norm_zero]
      positivity
  simpa [indexedTerminalPairMean] using norm_integral_le_of_norm_le_const
    (μ:=(gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p).prod
      (gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H x) p))
    (Filter.Eventually.of_forall hb)

variable [Nonempty S] [Nonempty T]

lemma indexedTerminalPairMean_independent_arrays
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x,y) d
      (fun p => f p.1*g p.2) (p.1,indexedMarksZip n p.2)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
          (indexedCascadeMarksLaw ρ n))) =
      (twoVisitMass n z d).toReal *
        (pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d x *
          pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i)) g d y) := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  let B := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n))
  let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
    (indexedCascadeMarksLaw ρ n : Measure (IndexedCascadeMarks T n))
  let M' := (indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n))
  let a : IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n) →
      IndexedCascadeBase n×IndexedCascadeMarks (S×T) n :=
    Prod.map id (indexedMarksZip (S:=S) (T:=T) n)
  have ha : Measurable a := measurable_id.prodMap (indexedMarksZip_measurable n)
  have hmap : (B.prod M).map a=B.prod M' := by
    rw [←Measure.map_prod_map _ _ measurable_id (indexedMarksZip_measurable n),Measure.map_id]
    exact congrArg (Measure.prod B) (indexedMarksZip_law ν ρ n)
  have hterm : Measurable (fun p : X×Y => H p.1+G p.2) :=
    (hH.comp measurable_fst).add (hG.comp measurable_snd)
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hval := indexedTerminalPairMean_integral (productMarkLaw ν ρ) st hs n z hz hz0 hz1
    (fun p : X×Y => H p.1+G p.2) hterm
    (finiteCascadeFractionalIntegrable_add_product ν ρ step₁ step₂ n z hz0 hHI hGI)
    (x,y) d (fun p : X×Y => f p.1*g p.2) hfg (C*D) (mul_nonneg hC hD)
    (fun p => by rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC)
  change (∫ p, indexedTerminalPairMean st n _ _ _ _ p ∂B.prod M')=_ at hval
  rw [←hmap,integral_map ha.aemeasurable
    (indexedTerminalPairMean_measurable st hs n _ hterm (x,y) d _ hfg).aestronglyMeasurable] at hval
  refine hval.trans ?_
  dsimp only [st]
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  rw [pathCorrelation_parallel n _ _
    (cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI)
    (cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI) f g hf hg C D hC hD hfB hgB]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalRoots
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
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
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTerminalPairMean_joint_measurable (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) :
    Measurable (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
      indexedTerminalPairMean step n H p.1 d f p.2) := by
  let β : Kernel (X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) (IndexedLeaf n) :=
    (indexedTerminalBaseKernel n).comap Prod.snd measurable_snd
  let E : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))→IndexedLeaf n→ℝ :=
    fun p l => H (indexedLeafState step n (p.1,p.2.2) l)
  have hE : Measurable (Function.uncurry E) :=
    hH.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd))
  let κ := gibbsProbabilityKernel β E
  have : IsMarkovKernel β := by dsimp [β]; infer_instance
  have : IsMarkovKernel κ := gibbsProbabilityKernel_markov β E hE
  have he (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) :
      κ p=gibbsProbabilityKernel (indexedTerminalBaseKernel n) (indexedTerminalEnergy step n H p.1) p.2 :=
    gibbsProbabilityKernel_congr_apply β E (indexedTerminalBaseKernel n)
      (indexedTerminalEnergy step n H p.1) hE
      (indexedTerminalEnergy_measurable step hs n H hH p.1) p p.2
      (by simp [β]) rfl
  let F : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n)→ℝ :=
    fun p => if indexedCommonDepth n p.2.1 p.2.2=d then
      f (indexedLeafState step n (p.1.1,p.1.2.2) p.2.1)*
      f (indexedLeafState step n (p.1.1,p.1.2.2) p.2.2) else 0
  have hm (j : IndexedLeaf n×IndexedLeaf n→IndexedLeaf n) (hj : Measurable j) :
      Measurable (fun p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n) =>
        f (indexedLeafState step n (p.1.1,p.1.2.2) (j p.2))) :=
    hf.comp ((indexedLeafState_measurable hs n).comp
      ((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk (hj.comp measurable_snd)))
  have hcond : MeasurableSet {p : (X×(IndexedCascadeBase n×IndexedCascadeMarks S n))×(IndexedLeaf n×IndexedLeaf n) |
      indexedCommonDepth n p.2.1 p.2.2=d} :=
    ((Set.to_countable {l : IndexedLeaf n×IndexedLeaf n | indexedCommonDepth n l.1 l.2=d}).measurableSet).preimage measurable_snd
  have hF : Measurable F :=
    Measurable.ite hcond ((hm Prod.fst measurable_fst).mul (hm Prod.snd measurable_snd)) measurable_const
  have hv : Measurable (fun p => ∫ l, F (p,l) ∂(κ×ₖκ) p) :=
    (hF.stronglyMeasurable.integral_kernel_prod_right').measurable
  simp_rw [Kernel.prod_apply,he] at hv
  unfold indexedTerminalPairMean
  simpa only [F] using hv

end
variable {X Y S T R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T] [Nonempty S] [Nonempty T]
  [MeasurableSpace R] [MeasurableSpace Q]

lemma indexedTerminalPairMean_independent_roots
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2) d
      (fun p => f p.1*g p.2) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      (twoVisitMass n z d).toReal *
        ((∫ r, pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d (x r) ∂μ) *
          (∫ q, pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i) (finiteCascadeShifts ρ step₂ n z G i)) g d (y q) ∂σ)) := by
  dsimp only
  let st : (X×Y)×(S×T)→X×Y := fun p => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
  let term : X×Y→ℝ := fun p => H p.1+G p.2
  let obs : X×Y→ℝ := fun p => f p.1*g p.2
  have hs : Measurable st := by fun_prop
  have hterm : Measurable term := by fun_prop
  have hfg : Measurable obs := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB p.1) (hgB p.2) (abs_nonneg _) hC
  let V : (R×Q)×(IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n))→ℝ :=
    fun p => indexedTerminalPairMean st n term (x p.1.1,y p.1.2) d obs (p.2.1,indexedMarksZip n p.2.2)
  let B := IndexedCascadeBase n×(IndexedCascadeMarks S n×IndexedCascadeMarks T n)
  let transport : (R×Q)×B→(X×Y)×(IndexedCascadeBase n×IndexedCascadeMarks (S×T) n) :=
    fun p => ((x p.1.1,y p.1.2),(p.2.1,indexedMarksZip n p.2.2))
  have hzip : Measurable (indexedMarksZip (S:=S) (T:=T) n) := indexedMarksZip_measurable n
  have htransport : Measurable transport :=
    (((hx.comp (measurable_fst.fst : Measurable (fun p : (R×Q)×B => p.1.1))).prodMk
      (hy.comp measurable_fst.snd)).prodMk
      (measurable_snd.fst.prodMk (hzip.comp measurable_snd.snd)))
  have hjoint := indexedTerminalPairMean_joint_measurable st hs n term hterm d obs hfg
  have hV' := hjoint.comp htransport
  have hV : Measurable V := hV'
  have hi : Integrable V (((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) :=
    Integrable.of_bound hV.aestronglyMeasurable ((C*D)^2) (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs] using indexedTerminalPairMean_bound st hs n term hterm
        (x p.1.1,y p.1.2) d obs (C*D) (mul_nonneg hC hD) hb _)
  change (∫ p, V p ∂_)=_
  rw [integral_prod _ hi]
  simp_rw [V,term,obs,st,indexedTerminalPairMean_independent_arrays ν ρ step₁ step₂ hs₁ hs₂ n z hz hz0 hz1
    H G hH hG hHI hGI _ _ d f g hf hg C D hC hD hfB hgB]
  rw [integral_const_mul]
  exact congrArg ((twoVisitMass n z d).toReal * ·)
    (integral_prod_mul
      (fun r => pathCorrelation n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f d (x r))
      (fun q => pathCorrelation n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g d (y q)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
variable {X Y R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q]

lemma rootPathCorrelation_parallel (μ : Measure R) (σ : Measure Q) [SFinite μ] [SFinite σ]
    (x : R→X) (y : Q→Y) (n : ℕ) (κ : Fin n→Kernel X X) (η : Fin n→Kernel Y Y)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (hη : ∀ i, IsMarkovKernel (η i))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D)
    (d : Fin (n+1)) :
    rootPathCorrelation (μ.prod σ) (fun p => (x p.1,y p.2)) n (fun i => κ i ∥ₖ η i)
      (fun p => f p.1*g p.2) d =
      rootPathCorrelation μ x n κ f d * rootPathCorrelation σ y n η g d := by
  unfold rootPathCorrelation
  simp_rw [pathCorrelation_parallel n κ η hκ hη f g hf hg C D hC hD hfB hgB]
  exact integral_prod_mul (fun r => pathCorrelation n κ f d (x r))
    (fun q => pathCorrelation n η g d (y q))

open scoped ENNReal NNReal BoundedContinuousFunction

lemma residualResponse_eq_tiltMean (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f v x =
      tiltMean (gaussianReal 0 s) (fun z => f (x+z)) (fun z => v (x+z)) 1 := by
  simp only [residualResponse,gaussianAverage,tiltMean,tiltIntegral,tiltPartition,
    Pi.mul_apply,expBCF_apply,one_mul]

lemma residualResponse_continuous (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) :
    Continuous (residualResponse s f v) :=
  (gaussianAverage_continuous s (expBCF 1 f*v)).div
    (gaussianAverage_continuous s (expBCF 1 f))
    (fun x => (gaussianAverage_exp_pos s 1 f x).ne')

lemma residualResponse_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    |residualResponse s f v x|≤‖v‖ := by
  rw [residualResponse_eq_tiltMean]
  exact tilt_mean_bound (gaussianReal 0 s) (f.measurable.comp (measurable_const.add measurable_id))
    (v.measurable.comp (measurable_const.add measurable_id)) (norm_nonneg _) (norm_nonneg _)
    (fun z => f.norm_coe_le_norm (x+z)) (fun z => v.norm_coe_le_norm (x+z)) 1

lemma residualResponse_weighted (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (expBCF 1 f) x * residualResponse s f v x =
      gaussianAverage s (expBCF 1 f*v) x := by
  unfold residualResponse
  exact mul_div_cancel₀ _ (gaussianAverage_exp_pos s 1 f x).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalRestorationCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

section
section
variable {X Y R Q S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace T]
  [Nonempty S] [Nonempty T]

lemma indexedTerminalPairMean_ignore_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (hx : Measurable x) (hy : Measurable y) (d : Fin (n+1))
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hfB : ∀ x, |f x|≤C) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => H p.1+G p.2) (x p.1.1,y p.1.2) d
      (fun p => f p.1) (p.2.1,indexedMarksZip n p.2.2)
      ∂((μ : Measure R).prod (σ : Measure Q)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)).prod
            (indexedCascadeMarksLaw ρ n)))) =
      (twoVisitMass n z d).toReal * rootPathCorrelation μ x n
        (fun i => tiltedStateStep ν step₁ (z i) (finiteCascadeShifts ν step₁ n z H i)) f d := by
  have h := indexedTerminalPairMean_independent_roots μ σ ν ρ step₁ step₂ hs₁ hs₂
    n z hz hz0 hz1 H G hH hG hHI hGI x y hx hy d f (fun _ => 1)
    hf measurable_const C 1 hC (by norm_num) hfB (fun _ => by norm_num)
  have hm i := cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i
  simpa only [mul_one,pathCorrelation_one n _ hm,integral_const,probReal_univ,
    one_smul,rootPathCorrelation] using h

omit [Nonempty S] [Nonempty T] in
lemma cascade_root_pair_coefficients_product
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S→X) (step₂ : Y×T→Y) (hs₁ : Measurable step₁) (hs₂ : Measurable step₂)
    (n : ℕ) (z : Fin n→ℝ) (hz0 : ∀ i, 0<z i)
    (H : X→ℝ) (G : Y→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hHI : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ step₂ G n z)
    (x : R→X) (y : Q→Y) (d : Fin (n+1))
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ x, |f x|≤C) (hgB : ∀ y, |g y|≤D) :
    let st := fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))
    rootPathCorrelation ((μ : Measure R).prod (σ : Measure Q)) (fun r => (x r.1,y r.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ) st (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ) st n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) d =
      rootPathCorrelation μ x n (fun i => tiltedStateStep ν step₁ (z i)
        (finiteCascadeShifts ν step₁ n z H i)) f d *
      rootPathCorrelation σ y n (fun i => tiltedStateStep ρ step₂ (z i)
        (finiteCascadeShifts ρ step₂ n z G i)) g d := by
  dsimp only
  simp_rw [cascadeTiltedStep_parallel ν ρ step₁ step₂ hs₁ hs₂ n z hz0 H G hH hG hHI hGI]
  exact rootPathCorrelation_parallel μ σ x y n _ _
    (fun i => cascadeTiltedStep_markov ν step₁ hs₁ n z hz0 H hH hHI i)
    (fun i => cascadeTiltedStep_markov ρ step₂ hs₂ n z hz0 G hG hGI i)
    f g hf hg C D hC hD hfB hgB d

end

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GibbsRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_restore {H W F : S→ℝ} (_hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) :
    tiltMean μ (fun x => H x+W x) F 1 =
      tiltMean μ H (fun x => Real.exp (W x)*F x) 1 /
        tiltMean μ H (fun x => Real.exp (W x)) 1 := by
  have hp : tiltPartition μ H 1≠0 :=
    (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using hi)).ne'
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul,Real.exp_add,mul_assoc]
  have hp' : (∫ x, Real.exp (H x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition,one_mul] using hp
  exact (div_div_div_cancel_right₀ hp' _ _).symm

lemma gibbsReplicaMean_fintype_prod {H F : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) :
    gibbsReplicaMean μ H r (fun x => ∏ i, F (x i))=(tiltMean μ H F 1)^r := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi,
    ← tilt_law_integral_of_integrable μ hH hi']
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow (ι:=Fin r) F (μ:=tiltLaw μ H 1)

lemma gibbsReplicaMean_restore {H W : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) (F : (Fin r→S)→ℝ) :
    gibbsReplicaMean μ (fun x => H x+W x) r F =
      gibbsReplicaMean μ H r (fun x => (∏ i, Real.exp (W (x i)))*F x) /
        (tiltMean μ H (fun x => Real.exp (W x)) 1)^r := by
  have hp : replicaPotential (fun x => H x+W x) r =
      fun x => replicaPotential H r x+replicaPotential W r x := by
    funext x; simp only [replicaPotential,Finset.sum_add_distrib]
  have hir : Integrable (fun x => Real.exp (replicaPotential H r x)) (Measure.pi fun _ : Fin r => μ) := by
    simpa only [one_mul] using (replica_exp_integrable μ
      (show Integrable (fun x => Real.exp (1*H x)) μ by simpa only [one_mul] using hi) r)
  unfold gibbsReplicaMean
  rw [hp,tiltMean_restore _ (replicaPotential_measurable hH r) hir]
  simp only [replicaPotential,Real.exp_sum]
  congr 1
  exact gibbsReplicaMean_fintype_prod μ (F:=fun x => Real.exp (W x)) hH hi r

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LeafGibbsMarginal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma tiltMean_prod_snd_of_partition {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [SFinite μ] [SFinite ν]
    (H : S×T→ℝ) (G F : T→ℝ) (hF : Measurable F) {B : ℝ} (hB : ∀ t, |F t|≤B)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) :
    tiltMean (μ.prod ν) H (fun x => F x.2) 1=tiltMean ν G F 1 := by
  have hi : Integrable (fun x : S×T => F x.2*Real.exp (H x)) (μ.prod ν) :=
    he.bdd_mul (hF.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x.2)
  have hi' : Integrable (fun x : S×T => Real.exp (H x)*F x.2) (μ.prod ν) := by
    simpa only [mul_comm] using hi
  unfold tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  rw [integral_prod_symm _ hi',integral_prod_symm _ he]
  simp_rw [integral_mul_const,hp]

lemma enrichedIndexedHamiltonian_leaf_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (g : ℕ→ℝ) (l : IndexedLeaf k) :
    (∫ x, Real.exp (enrichedIndexedHamiltonian n M k f a p d h u g (x,l)) ∂unitSphereLaw (n+1))=
      Real.exp (enrichedTerminal n M f a p u (h (Fin.last k))
        (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
          ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
            (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0)) := by
  let root := profileGaussianRoot (enrichedCoordinateLevel p d h)
  let step := profileGaussianStep (enrichedCoordinateLevel p d h)
  have hA : enrichedIncrementMap p d h = fun j => diagonalMark (step j) :=
    funext (enrichedIncrementMap_profile p d h)
  have hR : enrichedRootMap p d h = diagonalMark root := rfl
  rw [hA,hR]
  let v := indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) k
    ((fun _ => diagonalMark root (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
      (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0
  have he (x : NormalizedSpin (n+1)) :
      enrichedIndexedHamiltonian n M k f a p d h u g (x,l)=
        normalizedPatternEnergy (n+1) M f a x+inner ℝ (sourceEnrichedFeature (n+1) p u x) v-
          (n+1:ℕ)*h (Fin.last k) := by
    unfold enrichedIndexedHamiltonian countableGaussianHamiltonian enrichedIndexedBoundedEnergy sourceGaussianRow
    rw [indexedGaussianRow_diagonal_identity]
    dsimp only [v,root,step]
    ring
  simp_rw [he]
  exact vectorPartition_exp_terminal (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)).measurable
    (sourceEnrichedFeature_measurable (n+1) p u) (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => (sourceEnrichedFeature_norm (n+1) p u x).le) _ v

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LeafMarginalLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SphericalPerceptronFreeEnergy
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma tiltLaw_prod_snd_of_partition (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) :
    (tiltLaw (μ.prod ν) H 1).map Prod.snd=tiltLaw ν G 1 := by
  have heG : Integrable (fun t => Real.exp (G t)) ν := by
    have hi := he.integral_prod_right
    simpa only [hp] using hi
  have hhe : Integrable (fun x => Real.exp (1*H x)) (μ.prod ν) := by simpa using he
  have hhG : Integrable (fun t => Real.exp (1*G t)) ν := by simpa using heG
  let := tilt_law_probability_of_integrable (μ.prod ν) hhe
  let := tilt_law_probability_of_integrable ν hhG
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi : Measurable (s.indicator (fun _ : T => (1:ℝ))) := measurable_const.indicator hs
  have hb (t : T) : |s.indicator (fun _ : T => (1:ℝ)) t|≤1 := by
    by_cases ht : t∈s <;> simp [ht]
  have h := tiltMean_prod_snd_of_partition μ ν H G _ hi hb he hp
  rw [←tilt_law_integral_of_integrable (μ.prod ν) hH hhe,
    ←tilt_law_integral_of_integrable ν hG hhG] at h
  have hm := integral_map (μ:=tiltLaw (μ.prod ν) H 1) measurable_snd.aemeasurable hi.aestronglyMeasurable
  rw [←hm] at h
  simpa only [integral_indicator hs,integral_const,smul_eq_mul,mul_one,
    measureReal_def,Measure.restrict_apply_univ] using h

lemma tiltLaw_prod_snd_replica (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) (r : ℕ) :
    MeasurePreserving (fun x : Fin r→S×T => fun i => (x i).2)
      (Measure.pi fun _ : Fin r => tiltLaw (μ.prod ν) H 1)
      (Measure.pi fun _ : Fin r => tiltLaw ν G 1) := by
  have hhe : Integrable (fun x => Real.exp (1*H x)) (μ.prod ν) := by simpa using he
  let := tilt_law_probability_of_integrable (μ.prod ν) hhe
  have heG : Integrable (fun t => Real.exp (1*G t)) ν := by
    simpa only [one_mul,hp] using he.integral_prod_right
  let := tilt_law_probability_of_integrable ν heG
  exact measurePreserving_pi _ _ (fun _ : Fin r =>
    ⟨measurable_snd,tiltLaw_prod_snd_of_partition μ ν H G hH hG he hp⟩)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TerminalReplicaRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
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

lemma gibbsReplicaMean_product_leaf (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hi : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t))
    (r : ℕ) (F : (Fin r→T)→ℝ) (hF : Measurable F) :
    gibbsReplicaMean (μ.prod ν) H r (fun x => F (fun i => (x i).2)) =
      gibbsReplicaMean ν G r F := by
  have hiG : Integrable (fun t => Real.exp (G t)) ν := by simpa only [hp] using hi.integral_prod_right
  rw [gibbsReplicaMean_integral_of_integrable (μ.prod ν) hH hi,
    gibbsReplicaMean_integral_of_integrable ν hG hiG]
  have hmap := tiltLaw_prod_snd_replica μ ν H G hH hG hi hp r
  have he := integral_map (μ:=Measure.pi fun _ : Fin r => tiltLaw (μ.prod ν) H 1)
    hmap.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hmap.map_eq] at he
  exact he.symm

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTerminalPairMean_replica (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1)) (f : X→ℝ)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l))) (indexedLeafProbability n p.1)) :
    indexedTerminalPairMean step n H x d f p =
      gibbsReplicaMean (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 2
        (fun l => if indexedCommonDepth n (l 0) (l 1)=d then
          f (indexedLeafState step n (x,p.2) (l 0))*f (indexedLeafState step n (x,p.2) (l 1)) else 0) := by
  unfold indexedTerminalPairMean
  dsimp only
  rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _
    (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
  symm
  exact gibbsReplicaMean_pair_integral (indexedLeafProbability n p.1)
    (H:=indexedTerminalEnergy step n H x p) (measurable_of_countable _)
    (by simpa only [indexedTerminalEnergy] using hi)
    (fun l : IndexedLeaf n×IndexedLeaf n => if indexedCommonDepth n l.1 l.2=d then
      f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)
    (measurable_of_countable _)

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalRestorationLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y Z R Q U S T V : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace V]
  [Nonempty S] [Nonempty T] [Nonempty V]

lemma indexedTerminalPairMean_two_fresh_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (τ : ProbabilityMeasure U)
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (π : ProbabilityMeasure V)
    (st₁ : X×S→X) (st₂ : Y×T→Y) (st₀ : Z×V→Z)
    (hs₁ : Measurable st₁) (hs₂ : Measurable st₂) (hs₀ : Measurable st₀)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (J : Z→ℝ) (hH : Measurable H) (hG : Measurable G) (hJ : Measurable J)
    (hHI : finiteCascadeFractionalIntegrable ν st₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ st₂ G n z)
    (hJI : finiteCascadeFractionalIntegrable π st₀ J n z)
    (x : R→X) (y : Q→Y) (v : U→Z) (hx : Measurable x) (hy : Measurable y) (hv : Measurable v)
    (d : Fin (n+1)) (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
      ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
    (∫ p, indexedTerminalPairMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
      ((x p.1.1.1,y p.1.1.2),v p.1.2) d (fun p => f p.1.1*g p.1.2)
      (p.2.1,indexedMarksZip n p.2.2)
      ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
            (indexedCascadeMarksLaw π n)))) =
      (twoVisitMass n z d).toReal *
        (rootPathCorrelation μ x n (fun i => tiltedStateStep ν st₁ (z i)
          (finiteCascadeShifts ν st₁ n z H i)) f d *
        rootPathCorrelation σ y n (fun i => tiltedStateStep ρ st₂ (z i)
          (finiteCascadeShifts ρ st₂ n z G i)) g d) := by
  let st : (X×Y)×(S×T)→X×Y := fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))
  have hs : Measurable st := by fun_prop
  have hfg : Measurable (fun p : X×Y => f p.1*g p.2) := by fun_prop
  have hb (p : X×Y) : |f p.1*g p.2|≤C*D := by
    rw [abs_mul]; exact mul_le_mul (hfB _) (hgB _) (abs_nonneg _) hC
  have h := indexedTerminalPairMean_ignore_old (productMarkLaw μ σ) τ (productMarkLaw ν ρ) π
    st st₀ hs hs₀ n z hz hz0 hz1 (fun p => H p.1+G p.2) J (by fun_prop) hJ
    (finiteCascadeFractionalIntegrable_add_product ν ρ st₁ st₂ n z hz0 hHI hGI) hJI
    (fun p => (x p.1,y p.2)) v (by fun_prop) hv d (fun p => f p.1*g p.2) hfg
    (C*D) (mul_nonneg hC hD) hb
  dsimp only [st] at h ⊢
  change _ = (twoVisitMass n z d).toReal *
    rootPathCorrelation ((μ : Measure R).prod (σ : Measure Q)) (fun p => (x p.1,y p.2)) n
      (fun i => tiltedStateStep (productMarkLaw ν ρ)
        (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) (z i)
        (finiteCascadeShifts (productMarkLaw ν ρ)
          (fun p => (st₁ (p.1.1,p.2.1),st₂ (p.1.2,p.2.2))) n z (fun p => H p.1+G p.2) i))
      (fun p => f p.1*g p.2) d at h
  rw [cascade_root_pair_coefficients_product μ σ ν ρ st₁ st₂ hs₁ hs₂ n z hz0
    H G hH hG hHI hGI x y d f g hf hg C D hC hD hfB hgB] at h
  exact h

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleRootRegroup
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedGaussian_pair_zip_law (k : ℕ) (I J : Type) [Fintype I] [Fintype J] :
    MeasurePreserving (fun t : (ℕ→ℝ)×(ℕ→ℝ) =>
      (((indexedGaussianDisorder k I t.1).1,(indexedGaussianDisorder k J t.2).1),
        indexedMarksZip k ((indexedGaussianDisorder k I t.1).2,(indexedGaussianDisorder k J t.2).2)))
      (countableGaussianLaw.prod countableGaussianLaw)
      (((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))).prod
        (indexedCascadeMarksLaw
          (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
            (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k)) := by
  have hI : MeasurePreserving (indexedGaussianDisorder k I) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) k)) :=
    ⟨indexedGaussianDisorder_measurable k I,indexedGaussianDisorder_law k I⟩
  have hJ : MeasurePreserving (indexedGaussianDisorder k J) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ J)) k)) :=
    ⟨indexedGaussianDisorder_measurable k J,indexedGaussianDisorder_law k J⟩
  have hz : MeasurePreserving (indexedMarksZip (S:=EuclideanSpace ℝ I) (T:=EuclideanSpace ℝ J) k)
      ((indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) k : Measure _).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k))
      (indexedCascadeMarksLaw (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
        (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k) :=
    ⟨indexedMarksZip_measurable k,indexedMarksZip_law _ _ k⟩
  exact ((MeasurePreserving.id _).prod hz).comp
    ((freshRoot_four_shuffle _ _ _ _).comp (hI.prod hJ))

lemma indexedGaussian_three_regroup_law (k : ℕ) (z : Fin k→ℝ)
    (I J K : Type) [Fintype I] [Fintype J] [Fintype K] :
    MeasurePreserving
      (fun t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)) =>
        ((((indexedGaussianDisorder k I t.2.1.1).1,(indexedGaussianDisorder k J t.2.1.2).1),
          (indexedGaussianDisorder k K t.2.2).1),
         (t.1,(indexedMarksZip k ((indexedGaussianDisorder k I t.2.1.1).2,
           (indexedGaussianDisorder k J t.2.1.2).2),(indexedGaussianDisorder k K t.2.2).2))))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw))
      ((((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))).prod
        (stdGaussian (EuclideanSpace ℝ K))).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((indexedCascadeMarksLaw
              (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
                (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k :
              Measure (IndexedCascadeMarks (EuclideanSpace ℝ I×EuclideanSpace ℝ J) k)).prod
            (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ K)) k)))) := by
  have hK : MeasurePreserving (indexedGaussianDisorder k K) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ K)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ K)) k)) :=
    ⟨indexedGaussianDisorder_measurable k K,indexedGaussianDisorder_law k K⟩
  exact (freshRoot_five_regroup _ _ _ _ _).comp
    ((MeasurePreserving.id (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))).prod
      ((indexedGaussian_pair_zip_law k I J).prod hK))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_CountableTerminalRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable (I J K : Type) [Fintype I] [Fintype J] [Fintype K]

variable {I J K}

lemma tripleGaussianStep_measurable
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) : Measurable (tripleGaussianStep A B C) := by
  have ha := gaussianLinearMarkStep_measurable A
  have hb := gaussianLinearMarkStep_measurable B
  have hc := gaussianLinearMarkStep_measurable C
  unfold tripleGaussianStep
  fun_prop

lemma tripleGaussianPair_measurable (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (tripleGaussianPair k A B C R Q T H G F d f g) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  have ho : Measurable (tripleGaussianObservable (K:=K) f g) := by unfold tripleGaussianObservable; fun_prop
  have hr : Measurable (tripleGaussianRoot R Q T) := by unfold tripleGaussianRoot; fun_prop
  have hm := indexedTerminalPairMean_joint_measurable (tripleGaussianStep A B C)
    (tripleGaussianStep_measurable A B C) k (tripleGaussianTerminal H G F) ht d
    (tripleGaussianObservable f g) ho
  have hp : Measurable (fun p : TripleGaussianData I J K k =>
      (tripleGaussianRoot R Q T p.1,(p.2.1,indexedMarksZip k p.2.2))) :=
    (hr.comp measurable_fst).prodMk (measurable_snd.fst.prodMk
      ((indexedMarksZip_measurable k).comp measurable_snd.snd))
  have hc := hm.comp hp
  exact hc

theorem countable_three_terminal_pair_value (k : ℕ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    {L₁ L₂ L₀ : ℝ≥0} (hH : LipschitzWith L₁ H) (hG : LipschitzWith L₂ G) (hF : LipschitzWith L₀ F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hfB : ∀ x, |f x|≤D) (hgB : ∀ y, |g y|≤E) :
    (∫ t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)),
      tripleGaussianPair k A B C R Q T H G F d f g
        ((((indexedGaussianDisorder k I t.2.1.1).1,(indexedGaussianDisorder k J t.2.1.2).1),
          (indexedGaussianDisorder k K t.2.2).1),
         (t.1,(indexedMarksZip k ((indexedGaussianDisorder k I t.2.1.1).2,
           (indexedGaussianDisorder k J t.2.1.2).2),(indexedGaussianDisorder k K t.2.2).2)))
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal *
        (rootPathCorrelation (stdGaussian (EuclideanSpace ℝ I)) (fun r => fun _ => R r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) k z (fun x => H (x 0)) i))
          (fun x => f (x 0)) d *
        rootPathCorrelation (stdGaussian (EuclideanSpace ℝ J)) (fun r => fun _ => Q r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) k z (fun x => G (x 0)) i))
          (fun x => g (x 0)) d) := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ I) : Measure (EuclideanSpace ℝ I)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ I)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ J) : Measure (EuclideanSpace ℝ J)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ J)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ K) : Measure (EuclideanSpace ℝ K)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ K)))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) A hH k z hz0
  have hJ := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) B hG k z hz0
  have hK := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ K)) C hF k z hz0
  have hv := indexedTerminalPairMean_two_fresh_old
    (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianMarkLaw (E:=EuclideanSpace ℝ J))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ K))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianMarkLaw (E:=EuclideanSpace ℝ J))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ K))
    (gaussianLinearMarkStep A) (gaussianLinearMarkStep B) (gaussianLinearMarkStep C)
    (gaussianLinearMarkStep_measurable A) (gaussianLinearMarkStep_measurable B) (gaussianLinearMarkStep_measurable C)
    k z hz hz0 hz1 (fun x => H (x 0)) (fun x => G (x 0)) (fun x => F (x 0))
    (hH.continuous.measurable.comp (measurable_pi_apply 0))
    (hG.continuous.measurable.comp (measurable_pi_apply 0))
    (hF.continuous.measurable.comp (measurable_pi_apply 0)) hI.2 hJ.2 hK.2
    (fun r => fun _ => R r) (fun r => fun _ => Q r) (fun r => fun _ => T r)
    (by fun_prop) (by fun_prop) (by fun_prop) d (fun x => f (x 0)) (fun x => g (x 0))
    (hf.comp (measurable_pi_apply 0)) (hg.comp (measurable_pi_apply 0)) D E hD hE (fun x => hfB _) (fun x => hgB _)
  have hp := indexedGaussian_three_regroup_law k z I J K
  have hm := tripleGaussianPair_measurable k A B C R Q T H G F hH.continuous.measurable
    hG.continuous.measurable hF.continuous.measurable d f g hf hg
  have he := integral_map (μ:=(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans hv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TripleGaussianReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

lemma tripleGaussianLeafState (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (x : ℕ→EuclideanSpace ℝ I) (y : ℕ→EuclideanSpace ℝ J) (z : ℕ→EuclideanSpace ℝ K)
    (a : IndexedCascadeMarks (EuclideanSpace ℝ I) k) (b : IndexedCascadeMarks (EuclideanSpace ℝ J) k)
    (c : IndexedCascadeMarks (EuclideanSpace ℝ K) k) (l : IndexedLeaf k) :
    indexedLeafState (tripleGaussianStep A B C) k (((x,y),z),indexedMarksZip k (indexedMarksZip k (a,b),c)) l =
      ((indexedLeafState (gaussianLinearMarkStep A) k (x,a) l,
        indexedLeafState (gaussianLinearMarkStep B) k (y,b) l),
        indexedLeafState (gaussianLinearMarkStep C) k (z,c) l) := by
  have he := indexedLeafState_product
    (fun p : ((ℕ→EuclideanSpace ℝ I)×(ℕ→EuclideanSpace ℝ J))×
      (EuclideanSpace ℝ I×EuclideanSpace ℝ J) =>
      (gaussianLinearMarkStep A (p.1.1,p.2.1),gaussianLinearMarkStep B (p.1.2,p.2.2)))
    (gaussianLinearMarkStep C) k (x,y) z (indexedMarksZip k (a,b)) c l
  rw [indexedLeafState_product] at he
  exact he

lemma tripleGaussianPair_replica (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (b : IndexedCascadeBase k) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun l => Real.exp ((H (gaussianLeafValue k A R t.1.1 l)+
      G (gaussianLeafValue k B Q t.1.2 l))+F (gaussianLeafValue k C T t.2 l))) (indexedLeafProbability k b)) :
    tripleGaussianPair k A B C R Q T H G F d f g (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t) =
      gibbsReplicaMean (indexedLeafProbability k b)
        (fun l => (H (gaussianLeafValue k A R t.1.1 l)+G (gaussianLeafValue k B Q t.1.2 l))+
          F (gaussianLeafValue k C T t.2 l)) 2
        (fun l => if indexedCommonDepth k (l 0) (l 1)=d then
          (f (gaussianLeafValue k A R t.1.1 (l 0))*g (gaussianLeafValue k B Q t.1.2 (l 0)))*
          (f (gaussianLeafValue k A R t.1.1 (l 1))*g (gaussianLeafValue k B Q t.1.2 (l 1))) else 0) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  unfold tripleGaussianPair
  have he := indexedTerminalPairMean_replica (tripleGaussianStep A B C) (tripleGaussianStep_measurable A B C)
    k (tripleGaussianTerminal H G F) ht
    (tripleGaussianRoot R Q T (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).1) d (tripleGaussianObservable f g)
    ((tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).2.1,indexedMarksZip k (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).2.2)
  have hstate (l : IndexedLeaf k) := tripleGaussianLeafState k A B C
    (fun _ => R (indexedGaussianDisorder k I t.1.1).1)
    (fun _ => Q (indexedGaussianDisorder k J t.1.2).1)
    (fun _ => T (indexedGaussianDisorder k K t.2).1)
    (indexedGaussianDisorder k I t.1.1).2 (indexedGaussianDisorder k J t.1.2).2
    (indexedGaussianDisorder k K t.2).2 l
  simp only [tripleGaussianCountableData,tripleGaussianRoot] at he ⊢
  simp only [tripleGaussianTerminal,hstate] at he
  have hv := he hi
  simp only [tripleGaussianObservable] at hv
  rw [hv]
  congr 1
  funext l
  simp only [indexedTerminalEnergy,tripleGaussianTerminal,hstate,gaussianLeafValue]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundedLeafRestoration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma exp_add_integrable_of_bound (μ : Measure S) {H W : S→ℝ}
    (hi : Integrable (fun x => Real.exp (H x)) μ) (hW : Measurable W)
    {C : ℝ} (hb : ∀ x, W x≤C) : Integrable (fun x => Real.exp (H x+W x)) μ := by
  have h := hi.mul_bdd (hW.exp.aestronglyMeasurable) (ae_of_all μ fun x =>
    show ‖Real.exp (W x)‖≤Real.exp C by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (hb x))
  simpa only [Real.exp_add] using h

lemma product_leaf_restore (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G W : T→ℝ) (hH : Measurable H) (hG : Measurable G) (hW : Measurable W)
    (hi : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t))
    {C : ℝ} (hb : ∀ t, W t≤C) (r : ℕ) (F : (Fin r→T)→ℝ) (hF : Measurable F) :
    gibbsReplicaMean (μ.prod ν) (fun x => H x+W x.2) r (fun x => F (fun i => (x i).2))=
      gibbsReplicaMean ν (fun t => G t+W t) r F := by
  apply gibbsReplicaMean_product_leaf μ ν _ _ (hH.add (hW.comp measurable_snd)) (hG.add hW)
    (exp_add_integrable_of_bound _ hi (hW.comp measurable_snd) (fun x => hb x.2)) _ r F hF
  intro t
  change (∫ s, Real.exp (H (s,t)+W t) ∂μ)=Real.exp (G t+W t)
  simp only [Real.exp_add,integral_mul_const,hp]

lemma gibbsReplicaMean_congr (μ : Measure S) (H G : S→ℝ) (h : ∀ x,H x=G x)
    (r : ℕ) (F K : (Fin r→S)→ℝ) (hF : ∀ x,F x=K x) :
    gibbsReplicaMean μ H r F=gibbsReplicaMean μ G r K := by
  rw [show H=G from funext h,show F=K from funext hF]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableMarkedDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

variable {S : Type} [MeasurableSpace S] {k r : ℕ}

lemma labelProfileField_product_measurable (q : Fin (k+1)→ℝ) :
    Measurable (fun p : (ℕ→ℝ)×(S×IndexedLeaf k) => labelProfileField q p.1 p.2) :=
  countableGaussianField_measurable (v := labelProfileRow q)
    (indexedGaussianRow_measurable k _ measurable_const)
    (indexedGaussianRowLength_measurable (I := Fin 1) k)

lemma measurableReplicaProduct {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (V : A→B→ℝ) (hV : Measurable (Function.uncurry V)) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (fun p : A×(Fin r→B) => ∏ i, f i (V p.1 (p.2 i))) := by
  have h (i : Fin r) : Measurable (fun p : A×(Fin r→B) => f i (V p.1 (p.2 i))) :=
    (f i).measurable.comp (hV.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact Finset.measurable_prod Finset.univ (fun i _ => h i)

lemma labelMixedValue_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelMixedValue (S:=S) q s f)) :=
  measurableReplicaProduct (labelProfileField q) (labelProfileField_product_measurable q)
    (fun i => gaussianAverageBCF s (f i))

lemma labelMixedValue_bound {S : Type} [MeasurableSpace S] {k r : ℕ}
    (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ)
    (z : ℕ→ℝ) (xs : Fin r→S×IndexedLeaf k) :
    |labelMixedValue q s f z xs|≤∏ i, ‖gaussianAverageBCF s (f i)‖ := by
  simp only [labelMixedValue,Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ =>
    (gaussianAverageBCF s (f index)).norm_coe_le_norm _)

lemma labelTwoMixed_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f g : Fin r→ℝ →ᵇ ℝ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F) :
    Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) =>
      F p.2 * labelMixedValue q s f p.1.1 p.2 * labelMixedValue q s g p.1.2 p.2) := by
  have hf := (labelMixedValue_measurable (S:=S) q s f).comp
    (measurable_fst.fst.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.1,p.2)))
  have hg := (labelMixedValue_measurable (S:=S) q s g).comp
    (measurable_fst.snd.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.2,p.2)))
  exact ((hF.comp measurable_snd).mul hf).mul hg

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReferenceValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileTerminal_lipschitz (g : Jet3) (s : ℝ≥0) :
    LipschitzWith (‖(g.heatLog s 1).d1‖₊*
      ‖innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊)
      (labelProfileTerminal g s) := by
  have he : labelProfileTerminal g s =
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog s 1).f
        ((innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))) v) := by
    funext v
    rw [Jet3.heatLog_f]
    rfl
  rw [he]
  have heatLipschitz : LipschitzWith ‖(g.heatLog s 1).d1‖₊ (g.heatLog s 1).f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g.heatLog s 1).has1 point).differentiableAt)
    intro point
    rw [(g.heatLog s 1).deriv_eq]
    exact_mod_cast (g.heatLog s 1).d1.norm_coe_le_norm point
  exact heatLipschitz.comp
    (innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))).lipschitz

lemma labelProfileTerminal_bound (g : Jet3) (s : ℝ≥0) (v : EuclideanSpace ℝ (Fin 1)) :
    |labelProfileTerminal g s v|≤‖g.f‖ := heatLog_abs_le s 1 g.f _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedIndexedHamiltonian_exp_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (b : IndexedCascadeBase k) :
    ∀ᵐ g ∂countableGaussianLaw, Integrable
      (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p d h u g x))
      (enrichedIndexedBaseMeasure n k b) := by
  have he := countableGaussian_coupling_exp_ae (enrichedIndexedBaseMeasure n k b)
    (enrichedIndexedBoundedEnergy_measurable n M k f a h)
    (sourceGaussianRow_measurable p d h u) (sourceGaussianRow_measurable p d h u)
    (indexedGaussianRowLength_measurable k)
    (enrichedIndexedBoundedEnergy_bound n M k f a h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l))) 0
  simpa only [zero_mul,add_zero,enrichedIndexedHamiltonian] using he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileSpin_node {k : ℕ} (q : Fin (k+1)→Time) (l : Fin (k+1)) :
    labelProfileSpin q (sourceLabelLevel k l)=timeSpin (q l) := by
  apply Subtype.ext
  change min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) (sourceLabelLevel k l)))=(q l:ℝ)
  rw [labelProfileInterpolant_node,max_eq_right (q l).prop.1,min_eq_right (q l).prop.2]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S : Type} [MeasurableSpace S] {k : ℕ}

lemma labelRestorationTest_measurable {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} (hF : Measurable F)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) : Measurable (labelRestorationTest q s f v w F z) :=
  (labelTwoMixed_measurable q s (fun i => expBCF 1 f*v i) (fun i => expBCF 1 f*w i) F hF).comp
    (measurable_const.prodMk measurable_id)

lemma labelRestorationTest_bound {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ x, |F x|≤C) (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : Fin r→S×IndexedLeaf k) :
    |labelRestorationTest q s f v w F z x|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  simp only [labelRestorationTest,abs_mul]
  exact mul_le_mul (mul_le_mul (hF _) (labelMixedValue_bound q s _ _ _) (abs_nonneg _) hC)
    (labelMixedValue_bound q s _ _ _) (abs_nonneg _)
    (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))

omit [MeasurableSpace S] in
lemma residual_replica_weight_cancel (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (r : ℕ)
    (v w : Fin r→ℝ →ᵇ ℝ) (a b : S→ℝ) (F : (Fin r→S)→ℝ) (xs : Fin r→S) :
    (∏ i, Real.exp (heatLog s 1 f (a (xs i))+heatLog s 1 f (b (xs i)))) *
      (F xs*(∏ i, residualResponse s f (v i) (a (xs i)))*
        (∏ i, residualResponse s f (w i) (b (xs i)))) =
      F xs*(∏ i, gaussianAverageBCF s (expBCF 1 f*v i) (a (xs i)))*
        (∏ i, gaussianAverageBCF s (expBCF 1 f*w i) (b (xs i))) := by
  have hex (x : ℝ) : Real.exp (heatLog s 1 f x)=gaussianAverage s (expBCF 1 f) x := by
    simpa only [NNReal.coe_one,one_mul] using exp_heatLog s 1 (by norm_num) f x
  simp_rw [Real.exp_add,hex]
  calc
    _ = F xs * (∏ i, gaussianAverage s (expBCF 1 f) (a (xs i))*
          residualResponse s f (v i) (a (xs i))) *
        (∏ i, gaussianAverage s (expBCF 1 f) (b (xs i))*
          residualResponse s f (w i) (b (xs i))) := by
      simp only [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [residualResponse_weighted]; rfl

lemma residual_gibbs_restore (μ : Measure S) [IsProbabilityMeasure μ]
    (J : S→ℝ) (hJ : Measurable J) (hi : Integrable (fun x => Real.exp (J x)) μ)
    (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (r : ℕ) (v w : Fin r→ℝ →ᵇ ℝ)
    (a b : S→ℝ) (F : (Fin r→S)→ℝ) :
    gibbsReplicaMean μ (fun x => J x+(heatLog s 1 f (a x)+heatLog s 1 f (b x))) r
      (fun xs => F xs*(∏ i, residualResponse s f (v i) (a (xs i)))*
        (∏ i, residualResponse s f (w i) (b (xs i)))) =
      gibbsReplicaMean μ J r (fun xs =>
        F xs*(∏ i, gaussianAverageBCF s (expBCF 1 f*v i) (a (xs i)))*
          (∏ i, gaussianAverageBCF s (expBCF 1 f*w i) (b (xs i)))) /
      (tiltMean μ J (fun x => gaussianAverageBCF s (expBCF 1 f) (a x)*
        gaussianAverageBCF s (expBCF 1 f) (b x)) 1)^r := by
  rw [gibbsReplicaMean_restore μ hJ hi]
  have hex (x : S) : Real.exp (heatLog s 1 f (a x)+heatLog s 1 f (b x)) =
      gaussianAverageBCF s (expBCF 1 f) (a x)*gaussianAverageBCF s (expBCF 1 f) (b x) := by
    rw [Real.exp_add]
    have he (y : ℝ) : Real.exp (heatLog s 1 f y)=gaussianAverageBCF s (expBCF 1 f) y := by
      simpa only [NNReal.coe_one,one_mul,gaussianAverageBCF_coe] using exp_heatLog s 1 (by norm_num) f y
    rw [he,he]
  congr 1
  · apply congrArg (gibbsReplicaMean μ J r)
    funext xs
    exact residual_replica_weight_cancel s f r v w a b F xs
  · simp_rw [hex]

lemma labelRestoration_ratio {k r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ]
    (J : (S×IndexedLeaf k)→ℝ) (hJ : Measurable J)
    (hi : Integrable (fun x => Real.exp (J x)) μ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    gibbsReplicaMean μ (fun x => J x+(heatLog s 1 f (labelProfileField q z.1 x)+
        heatLog s 1 f (labelProfileField q z.2 x))) r
      (fun xs => F xs*(∏ i, residualResponse s f (v i) (labelProfileField q z.1 (xs i)))*
        (∏ i, residualResponse s f (w i) (labelProfileField q z.2 (xs i)))) =
      gibbsReplicaMean μ J r (labelRestorationTest q s f v w F z) /
        (tiltMean μ J (labelRestorationWeight q s f z) 1)^r :=
  residual_gibbs_restore μ J hJ hi s f r v w (labelProfileField q z.1) (labelProfileField q z.2) F

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A : Type*} {S : Type} [MeasurableSpace A] [MeasurableSpace S] {k r : ℕ}

lemma labelRestorationWeight_joint (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelRestorationWeight (S:=S) q s f)) := by
  have h₁ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.1,p.2)) from
      measurable_fst.fst.prodMk measurable_snd)
  have h₂ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.2,p.2)) from
      measurable_fst.snd.prodMk measurable_snd)
  exact ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₁).mul
    ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₂)

lemma labelRestorationWeight_exp {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) :
    labelRestorationWeight q s f z x =
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) := by
  have he (a : ℝ) : Real.exp (heatLog s 1 f a)=gaussianAverageBCF s (expBCF 1 f) a := by
    simpa only [NNReal.coe_one,one_mul,gaussianAverageBCF_coe] using exp_heatLog s 1 (by norm_num) f a
  simp only [Real.exp_add,he,labelRestorationWeight]

variable (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
variable (H : A → S×IndexedLeaf k → ℝ)
variable (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
variable (v w : Fin r → ℝ →ᵇ ℝ) (F : (Fin r → S×IndexedLeaf k) → ℝ)

lemma labelKernelDenominator_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (labelKernelDenominator κ H q s f) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hW := (labelRestorationWeight_joint (S:=S) q s f).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_tiltMean_measurable (κ.comap Prod.fst measurable_fst) hH' hW

lemma labelKernelNumerator_measurable (hH : Measurable (Function.uncurry H)) (hF : Measurable F) :
    Measurable (labelKernelNumerator κ H q s f v w F) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hG := (labelTwoMixed_measurable (S:=S) q s (fun i => expBCF 1 f*v i)
    (fun i => expBCF 1 f*w i) F hF).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(Fin r → S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_replicaMean_measurable (κ.comap Prod.fst measurable_fst) hH' hG

lemma labelKernelNumerator_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (a : A×((ℕ→ℝ)×(ℕ→ℝ))) :
    |labelKernelNumerator κ H q s f v w F a|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  apply tiltMean_bound_general (Measure.pi fun _ : Fin r => κ a.1)
    (replicaPotential_measurable hH.of_uncurry_left r)
    (labelRestorationTest_measurable q s f v w hF a.2)
    (mul_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  exact labelRestorationTest_bound q s f v w hC hb a.2

lemma labelKernelDenominator_bounds (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    labelKernelDenominator κ H q s f (a,z) ∈ Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) := by
  have hm (g : ℕ→ℝ) : Measurable (fun x : S×IndexedLeaf k => heatLog s 1 f (labelProfileField q g x)) := by
    have hp := (labelProfileField_product_measurable (S:=S) q).of_uncurry_left (x:=g)
    exact (heatLog_continuous s 1 f).measurable.comp hp
  have hb (x : S×IndexedLeaf k) :
      |heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)|≤2*‖f‖ :=
    (abs_add_le _ _).trans ((add_le_add (heatLog_abs_le s 1 f _) (heatLog_abs_le s 1 f _)).trans_eq
      (two_mul ‖f‖).symm)
  have he := tiltMean_exp_bounds (κ a) hH.of_uncurry_left ((hm z.1).add (hm z.2)) hi
    (mul_nonneg (by norm_num) (norm_nonneg f)) hb
  have hw : labelRestorationWeight (S:=S) q s f z = fun x =>
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) :=
    funext (labelRestorationWeight_exp q s f z)
  simpa only [labelKernelDenominator,hw,Set.mem_Icc,Pi.add_apply] using he

lemma labelKernelRestoredRatio_measurable (hH : Measurable (Function.uncurry H)) (hF : Measurable F) :
    Measurable (labelKernelRestoredRatio κ H q s f v w F) :=
  (labelKernelNumerator_measurable κ H q s f v w F hH hF).div
    ((labelKernelDenominator_measurable κ H q s f hH).pow_const r)

lemma labelKernelRestoredRatio_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) {a : A}
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    |labelKernelRestoredRatio κ H q s f v w F (a,z)|≤
      (C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (Real.exp (-(2*‖f‖)))^r := by
  have hd := (labelKernelDenominator_bounds κ H q s f hH hi z).1
  have hp : 0<labelKernelDenominator κ H q s f (a,z) := (Real.exp_pos _).trans_le hd
  rw [labelKernelRestoredRatio,abs_div,abs_of_pos (pow_pos hp r)]
  have hn := labelKernelNumerator_bound κ H q s f v w F hH hF hC hb (a,z)
  calc
    _ ≤ (C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (labelKernelDenominator κ H q s f (a,z))^r := div_le_div_of_nonneg_right hn (pow_nonneg hp.le _)
    _ ≤ _ := by gcongr

lemma labelKernelRestoredRatio_integrable (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C)
    (P : Measure A) [IsFiniteMeasure P]
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    Integrable (labelKernelRestoredRatio κ H q s f v w F)
      (P.prod (countableGaussianLaw.prod countableGaussianLaw)) := by
  apply Integrable.of_bound (labelKernelRestoredRatio_measurable κ H q s f v w F hH hF).aestronglyMeasurable
    ((C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (Real.exp (-(2*‖f‖)))^r)
  have ha := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hi
  filter_upwards [ha] with a ha
  simpa only [Real.norm_eq_abs] using labelKernelRestoredRatio_bound κ H q s f v w F hH hF hC hb ha a.2

lemma restorationClip_eq (f : ℝ →ᵇ ℝ) {x : ℝ} (hx : x∈RestorationRange f) :
    (restorationClip f x).val=x := by
  dsimp [restorationClip]
  rw [min_eq_right hx.2,max_eq_right hx.1]

lemma labelKernelCompactDenominator_eq (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    (labelKernelCompactDenominator κ H q s f (a,z)).val=labelKernelDenominator κ H q s f (a,z) :=
  restorationClip_eq f (labelKernelDenominator_bounds κ H q s f hH hi z)

lemma labelKernel_weighted_eq (hH : Measurable (Function.uncurry H))
    (P : Measure A) [IsFiniteMeasure P]
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) (J : ℝ→ℝ) :
    (∫ a, labelKernelNumerator κ H q s f v w F a * J (labelKernelCompactDenominator κ H q s f a).val
      ∂P.prod (countableGaussianLaw.prod countableGaussianLaw)) =
    ∫ a, labelKernelNumerator κ H q s f v w F a * J (labelKernelDenominator κ H q s f a)
      ∂P.prod (countableGaussianLaw.prod countableGaussianLaw) := by
  apply integral_congr_ae
  have ha := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hi
  filter_upwards [ha] with a ha
  rw [labelKernelCompactDenominator_eq κ H q s f hH ha a.2]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments2
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

variable (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
variable (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
variable (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ)
variable (z : Fin k → ℝ) (t : ℝ≥0)

lemma sourceLabelRestorationRatio_eq (hh0 : ∀ i,0≤h i) (hh : Monotone h) :
    sourceLabelRestorationRatio n k r q s f ψ v w F p d h u z t =
      ∫ a, labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
        (sourceCouplingHamiltonian n k f p d h u) q s ψ v w
        (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) a
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw) := by
  have he := labelKernel_weighted_eq (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian n k f p d h u) q s ψ v w
    (fun x => F (fun i l => sourceJointOverlap (x i) (x l)))
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceFresh_exp_ae n k f p d h hh0 hh u z t) (fun x => (x^r)⁻¹)
  simpa only [sourceLabelRestorationRatio,sourceLabelRestorationNumerator,sourceLabelRestorationDenominator,
    restorationReciprocal,ContinuousMap.coe_mk,labelKernelRestoredRatio,div_eq_mul_inv] using he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationPair
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileField_leaf {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf k) :
    labelProfileField q g x=labelEvaluation (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) g x.2) :=
  labelProfileField_marked_state q g x

lemma labelResidualObservable_measurable (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) :
    Measurable (labelResidualObservable s f v) :=
  (residualResponse_continuous s f v).measurable.comp (by unfold labelEvaluation; fun_prop)

lemma labelResidualObservable_bound (s : ℝ≥0) (f v : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    |labelResidualObservable s f v x|≤‖v‖ := residualResponse_bound s f v _

variable {S K : Type} [MeasurableSpace S] [Fintype K]

lemma labelRestorationPair_eq_terminal (μ : Measure S) [IsProbabilityMeasure μ]
    (k : ℕ) (b : IndexedCascadeBase k) (J : S×IndexedLeaf k→ℝ) (hJ : Measurable J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) (F : EuclideanSpace ℝ K→ℝ)
    (hF : Measurable F) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun x => Real.exp (J x)) (μ.prod (indexedLeafProbability k b)))
    (hp : ∀ l, (∫ x, Real.exp (J (x,l)) ∂μ)=Real.exp (F (gaussianLeafValue k C T t.2 l)))
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    gibbsReplicaMean (μ.prod (indexedLeafProbability k b)) J 2
      (labelRestorationTest q s g.f (fun _ => v) (fun _ => w)
        (fun xs => if indexedCommonDepth k (xs 0).2 (xs 1).2=d then 1 else 0) t.1) /
      (tiltMean (μ.prod (indexedLeafProbability k b)) J (labelRestorationWeight q s g.f t.1) 1)^2 =
    tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) C
      (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F d
      (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k b t) := by
  let G : IndexedLeaf k→ℝ := fun l => F (gaussianLeafValue k C T t.2 l)
  let W : IndexedLeaf k→ℝ := fun l =>
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)+
    labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l)
  let O : (Fin 2→IndexedLeaf k)→ℝ := fun l => if indexedCommonDepth k (l 0) (l 1)=d then
    (labelResidualObservable s g.f v (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 (l 0))*
      labelResidualObservable s g.f w (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 (l 0)))*
    (labelResidualObservable s g.f v (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 (l 1))*
      labelResidualObservable s g.f w (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 (l 1))) else 0
  have hW (l) : W l≤2*‖g.f‖ := by
    dsimp only [W]
    linarith [(le_abs_self _).trans (labelProfileTerminal_bound g s
      (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)),
      (le_abs_self _).trans (labelProfileTerminal_bound g s
      (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l))]
  have hiG : Integrable (fun l => Real.exp (G l)) (indexedLeafProbability k b) := by
    simpa only [hp,G] using hi.integral_prod_right
  have hiGW := exp_add_integrable_of_bound _ hiG (measurable_of_countable W) hW
  have hie : Integrable (fun l => Real.exp (
    (labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.1 l)+
      labelProfileTerminal g s (gaussianLeafValue k (labelGaussianStep q) (labelGaussianRoot q) t.1.2 l))+
      F (gaussianLeafValue k C T t.2 l))) (indexedLeafProbability k b) := by
    convert hiGW using 1
    all_goals try with_reducible_and_instances rfl
    funext l
    congr 1
    exact add_comm _ _
  rw [←labelRestoration_ratio q s g.f (fun _ : Fin 2 => v) (fun _ => w)
    (μ.prod (indexedLeafProbability k b)) J hJ hi _ t.1]
  have he := product_leaf_restore μ (indexedLeafProbability k b) J G W hJ
    (measurable_of_countable G) (measurable_of_countable W) hi hp hW 2 O (measurable_of_countable O)
  have hr := tripleGaussianPair_replica k (labelGaussianStep q) (labelGaussianStep q) C
    (labelGaussianRoot q) (labelGaussianRoot q) T (labelProfileTerminal g s) (labelProfileTerminal g s) F
    (labelProfileTerminal_lipschitz g s).continuous.measurable
    (labelProfileTerminal_lipschitz g s).continuous.measurable hF d
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w) b t hie
  rw [hr]
  refine (gibbsReplicaMean_congr _ _ _ ?_ 2 _ _ ?_).trans (he.trans ?_)
  · intro x
    simp only [labelProfileField_leaf,W,labelProfileTerminal,labelEvaluation]
  · intro xs
    simp only [Fin.prod_univ_two,labelProfileField_leaf,O,labelResidualObservable]
    split_ifs <;> ring
  · apply gibbsReplicaMean_congr
    · intro l; exact add_comm _ _
    · intro l; rfl

lemma enrichedIndexedHamiltonian_joint_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p e : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) :
    Measurable (Function.uncurry (enrichedIndexedHamiltonian n M k f a p e h u)) := by
  unfold enrichedIndexedHamiltonian
  exact countableGaussianHamiltonian_measurable (enrichedIndexedBoundedEnergy_measurable n M k f a h)
    (sourceGaussianRow_measurable p e h u) (indexedGaussianRowLength_measurable (I:=EnrichedIndex (n+1) (n+1) p) k)

lemma sourceLabelPair_exp_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) :
    ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
      Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p e h u t.2.2 x))
        (enrichedIndexedBaseMeasure n k t.1) := by
  let D := IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
  let κ : Kernel D (NormalizedSpin (n+1)×IndexedLeaf k) :=
    (Kernel.const D (unitSphereLaw (n+1))).prod ((indexedLeafKernel k).comap Prod.fst measurable_fst)
  have hκ (t : D) : κ t=enrichedIndexedBaseMeasure n k t.1 := by
    rw [Kernel.prod_apply]; rfl
  let H : D→NormalizedSpin (n+1)×IndexedLeaf k→ℝ :=
    fun t => enrichedIndexedHamiltonian n M k f a p e h u t.2.2
  have hbase := enrichedIndexedHamiltonian_joint_measurable n M k f a p e h u
  have ht : Measurable (fun p : D×(NormalizedSpin (n+1)×IndexedLeaf k) => (p.1.2.2,p.2)) :=
    measurable_fst.snd.snd.prodMk measurable_snd
  have hc := hbase.comp ht
  have hH : Measurable (Function.uncurry H) := hc
  have hm : MeasurableSet {t : D | Integrable (fun x => Real.exp (H t x)) (κ t)} :=
    measurableSet_kernel_integrable (κ:=κ) (f:=fun t x => Real.exp (H t x)) hH.exp.stronglyMeasurable
  have hi : ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
      ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
      Integrable (fun x => Real.exp (H t x)) (κ t) := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    refine ae_of_all _ fun b => ?_
    have hi := (measurePreserving_snd (μ:=countableGaussianLaw.prod countableGaussianLaw)
      (ν:=countableGaussianLaw)).quasiMeasurePreserving.ae
      (enrichedIndexedHamiltonian_exp_ae n M k f a p e h hh0 hh u b)
    simpa only [hκ,H] using hi
  simpa only [hκ,H] using hi

lemma sourceLabelPairRatio_eq_triple (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) (t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)))
    (hi : Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p e h u t.2.2 x))
      (enrichedIndexedBaseMeasure n k t.1)) :
    sourceLabelPairRatio n M k f a p e h u q g s d v w t =
      tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k))) d
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  have hbase := enrichedIndexedHamiltonian_joint_measurable n M k f a p e h u
  have hmJ : Measurable (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) :=
    hbase.of_uncurry_left
  have he := labelRestorationPair_eq_terminal (unitSphereLaw (n+1)) k t.1
    (enrichedIndexedHamiltonian n M k f a p e h u t.2.2) hmJ
    (enrichedIncrementMap p e h) (enrichedRootMap p e h) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))).continuous.measurable t.2 hi
    (enrichedIndexedHamiltonian_leaf_partition n M k f a p e h u t.2.2) q g s d v w
  exact he

lemma sourceLabelPairRatio_eq_triple_ae (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (_hz : StrictMono z) (_hz0 : ∀ i, 0<z i) (_hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    ∀ᵐ t ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw),
    sourceLabelPairRatio n M k f a p e h u q g s d v w t =
      tripleGaussianPair k (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
        (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
        (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k))) d
        (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
        (tripleGaussianCountableData k (I:=Fin 1) (J:=Fin 1) (K:=EnrichedIndex (n+1) (n+1) p) t.1 t.2) := by
  filter_upwards [sourceLabelPair_exp_ae n M k f a p e h hh0 hh u z] with t ht
  exact sourceLabelPairRatio_eq_triple n M k f a p e h u q g s d v w t ht

lemma sourceLabelPairRatio_value (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p e : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ) :
    (∫ t, sourceLabelPairRatio n M k f a p e h u q g s d v w t
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal * (labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
  have he := countable_three_terminal_pair_value k z hz hz0 hz1
    (labelGaussianStep q) (labelGaussianStep q) (enrichedIncrementMap p e h)
    (labelGaussianRoot q) (labelGaussianRoot q) (enrichedRootMap p e h)
    (labelProfileTerminal g s) (labelProfileTerminal g s) (enrichedTerminal n M f a p u (h (Fin.last k)))
    (labelProfileTerminal_lipschitz g s) (labelProfileTerminal_lipschitz g s)
    (enrichedTerminal_lipschitz n M f a p u (h (Fin.last k))) d
    (labelResidualObservable s g.f v) (labelResidualObservable s g.f w)
    (labelResidualObservable_measurable s g.f v) (labelResidualObservable_measurable s g.f w)
    ‖v‖ ‖w‖ (norm_nonneg _) (norm_nonneg _)
    (labelResidualObservable_bound s g.f v) (labelResidualObservable_bound s g.f w)
  exact (integral_congr_ae (sourceLabelPairRatio_eq_triple_ae n M k f a p e h hh0 hh u z hz hz0 hz1 q g s d v w)).trans he

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestoredValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceLabelPairReassoc_preserving (n k : ℕ) (z : Fin k→ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceLabelPairReassoc n k)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw))
      ((poissonMeasure ((n+1:ℕ)*t)).prod ((infinitePatternRowsLaw (n+1)).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)))) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  exact ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B ((G.prod G).prod G))).comp
    ((measurePreserving_prodAssoc K (R.prod B) ((G.prod G).prod G)).comp
      (((MeasurePreserving.id (K.prod (R.prod B))).prod
        (Measure.measurePreserving_swap (μ:=G) (ν:=G.prod G))).comp
        (measurePreserving_prodAssoc (K.prod (R.prod B)) G (G.prod G))))

lemma labelDepthTest_measurable {S : Type} [MeasurableSpace S] (k : ℕ) (d : Fin (k+1)) :
    Measurable (labelDepthTest (S:=S) k d) := by
  have hc : Measurable (fun x : Fin 2 → S×IndexedLeaf k => ((x 0).2,(x 1).2)) :=
    ((measurable_pi_apply 0).snd).prodMk ((measurable_pi_apply 1).snd)
  exact (measurable_of_countable (fun p : IndexedLeaf k×IndexedLeaf k =>
    if indexedCommonDepth k p.1 p.2=d then (1:ℝ) else 0)).comp hc

lemma labelDepthTest_bound {S : Type} (k : ℕ) (d : Fin (k+1)) (x : Fin 2 → S×IndexedLeaf k) :
    |labelDepthTest k d x|≤1 := by unfold labelDepthTest; split <;> norm_num

lemma sourceLabelPairIntegrand_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (t : ℝ≥0) :
    Integrable (sourceLabelPairIntegrand n k f p e h u q g s d v w)
      (((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) :=
  labelKernelRestoredRatio_integrable _ _ _ _ _ _ _ _
    (sourceCouplingHamiltonian_measurable n k f p e h u) (labelDepthTest_measurable k d)
    (by norm_num) (labelDepthTest_bound k d) _ (sourceFresh_exp_ae n k f p e h hh0 hh u z t)

lemma sourceLabelPairIntegrand_value (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) (v w : ℝ →ᵇ ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    (∫ a, sourceLabelPairIntegrand n k f p e h u q g s d v w a
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
  let F := sourceLabelPairIntegrand n k f p e h u q g s d v w
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  let G := countableGaussianLaw
  have hi := sourceLabelPairIntegrand_integrable n k f p e h hh0 hh u q g s d v w z t
  have hre := sourceLabelPairReassoc_preserving n k z t
  have hi' := (hre.symm (sourceLabelPairReassoc n k)).integrable_comp_of_integrable hi
  have he := hre.integral_comp (sourceLabelPairReassoc n k).measurableEmbedding
    (fun a => F ((sourceLabelPairReassoc n k).symm a))
  simp only [MeasurableEquiv.symm_apply_apply] at he
  change Integrable (fun a => F ((sourceLabelPairReassoc n k).symm a)) (K.prod (R.prod (B.prod ((G.prod G).prod G)))) at hi'
  change (∫ a, F a ∂_) = _
  rw [he,integral_prod _ hi']
  have ha := hi'.prod_right_ae
  have hval : ∀ᵐ M ∂K, (∫ a, F ((sourceLabelPairReassoc n k).symm (M,a)) ∂(R.prod (B.prod ((G.prod G).prod G)))) =
      (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
    filter_upwards [ha] with M hM
    rw [integral_prod _ hM]
    have hir (a : ℕ→Fin (n+1)→ℝ) :
        (∫ b, F ((sourceLabelPairReassoc n k).symm (M,(a,b))) ∂(B.prod ((G.prod G).prod G))) =
          (twoVisitMass k z d).toReal*(labelPairCoefficient k z q g s v d*labelPairCoefficient k z q g s w d) := by
      refine (integral_congr_ae (ae_of_all _ fun b => ?_)).trans
        (sourceLabelPairRatio_value n M k f (patternPrefix (n+1) M a) p e h hh0 hh u z hz hz0 hz1 q g s d v w)
      change sourceLabelPairIntegrand n k f p e h u q g s d v w (((M,(a,b.1)),b.2.2),b.2.1)=_
      simp only [sourceLabelPairIntegrand,labelKernelRestoredRatio,labelKernelNumerator,labelKernelDenominator,
        sourceFullSpinLeafKernel,Kernel.comap_apply,sourceSpinLeafKernel_apply,sourceCouplingHamiltonian,
        sourceLabelPairRatio]
      rfl
    simp_rw [hir]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [integral_congr_ae hval]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]


lemma labelKernelRestoredRatio_depth {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (k : ℕ) (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
    (H : A → S×IndexedLeaf k → ℝ) (hH : Measurable (Function.uncurry H))
    (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f v w : ℝ →ᵇ ℝ) (c : Fin (k+1)→ℝ)
    (a : A×((ℕ→ℝ)×(ℕ→ℝ))) (hi : Integrable (fun x => Real.exp (H a.1 x)) (κ a.1)) :
    labelKernelRestoredRatio κ H q s f (fun _ : Fin 2 => v) (fun _ => w)
      (fun x => c (indexedCommonDepth k (x 0).2 (x 1).2)) a =
    ∑ d, c d * labelKernelRestoredRatio κ H q s f (fun _ : Fin 2 => v) (fun _ => w)
      (labelDepthTest k d) a := by
  let T (d : Fin (k+1)) : (Fin 2→S×IndexedLeaf k)→ℝ := labelRestorationTest q s f (fun _ : Fin 2 => v) (fun _ => w) (labelDepthTest k d) a.2
  have hT d : Measurable (T d) := labelRestorationTest_measurable q s f _ _ (labelDepthTest_measurable k d) a.2
  let D := (∏ _ : Fin 2, ‖gaussianAverageBCF s (expBCF 1 f*v)‖)*(∏ _ : Fin 2, ‖gaussianAverageBCF s (expBCF 1 f*w)‖)
  have hb d x : |T d x|≤D := by
    simpa only [one_mul] using labelRestorationTest_bound q s f (fun _ : Fin 2 => v) (fun _ => w)
      (by norm_num : (0:ℝ)≤1) (labelDepthTest_bound k d) a.2 x
  have he (x : Fin 2→S×IndexedLeaf k) :
      labelRestorationTest q s f (fun _ : Fin 2 => v) (fun _ => w)
        (fun x => c (indexedCommonDepth k (x 0).2 (x 1).2)) a.2 x = ∑ d, c d*T d x := by
    simp only [T,labelRestorationTest,labelDepthTest]
    simp only [mul_ite,ite_mul,mul_zero,zero_mul]
    simp [mul_assoc]
  let := tilt_law_probability_of_integrable (κ a.1) (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H a.1 x)) (κ a.1))
  have hiT d : Integrable (T d) (Measure.pi fun _ : Fin 2 => tiltLaw (κ a.1) (H a.1) 1) :=
    Integrable.of_bound (hT d).aestronglyMeasurable D (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb d x)
  simp only [labelKernelRestoredRatio,labelKernelNumerator,gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi]
  simp_rw [he]
  rw [integral_finsetSum _ (fun d _ => (hiT d).const_mul (c d)),Finset.sum_div]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [T]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma labelProfilePairTest_source (N k : ℕ) (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ)
    (x : Fin 2→NormalizedSpin N×IndexedLeaf k) :
    labelProfilePairTest q F (fun i j => sourceJointOverlap (x i) (x j))=
      F (timeSpin (q (indexedCommonDepth k (x 0).2 (x 1).2))) := by
  change F (labelProfileSpin q (sourceLabelLevel k (indexedCommonDepth k (x 0).2 (x 1).2)))=_
  rw [labelProfileSpin_node]

lemma sourceLabelRestorationRatio_pair_value_oai (n k : ℕ) (f : ℝ →ᵇ ℝ) (g : Jet3)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (F : CompactOverlap →ᵇ ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    sourceLabelRestorationRatio n k 2 (fun i => (q i:ℝ)) s f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) p e h u z t =
      ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
        (labelPairCoefficient k z (fun i => (q i:ℝ)) g s v d *
          labelPairCoefficient k z (fun i => (q i:ℝ)) g s w d) := by
  rw [sourceLabelRestorationRatio_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh0 hh]
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  have hae := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae
    (sourceFresh_exp_ae n k f p e h hh0 hh u z t)
  have he : (fun a => labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
      (sourceCouplingHamiltonian n k f p e h u) (fun i => (q i:ℝ)) s g.f (fun _ : Fin 2 => v) (fun _ => w)
      (fun x => labelProfilePairTest q F (fun i j => sourceJointOverlap (x i) (x j))) a) =ᵐ[P.prod (countableGaussianLaw.prod countableGaussianLaw)]
    (fun a => ∑ d, F (timeSpin (q d))*sourceLabelPairIntegrand n k f p e h u (fun i => (q i:ℝ)) g s d v w a) := by
    filter_upwards [hae] with a ha
    simp only [labelProfilePairTest_source]
    exact labelKernelRestoredRatio_depth k _ _ (sourceCouplingHamiltonian_measurable n k f p e h u)
      _ s g.f v w (fun d => F (timeSpin (q d))) a ha
  rw [integral_congr_ae he,integral_finsetSum _ (fun d _ =>
    (sourceLabelPairIntegrand_integrable n k f p e h hh0 hh u (fun i => (q i:ℝ)) g s d v w z t).const_mul _)]
  simp only [integral_const_mul,sourceLabelPairIntegrand_value n k f p e h hh0 hh u _ g s _ v w z hz hz0 hz1 t,mul_assoc]

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value_oai := @OAI.SphericalPerceptronFreeEnergy.sourceLabelRestorationRatio_pair_value_oai
