-- Prove2me | solution 1 for OAI.InvariantIsing.magnetic_entropy_sequence_of_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:02:35.078501+00:00
-- url     : https://prove2.me/submissions/5b57b0df-c386-4c6b-b727-886d13819290

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_IsingPerceptron_enrichedMeanPressure_field_add_le
import Theorems.Thm_OAI_IsingPerceptron_enrichedMeanPressure_recursion
import Theorems.Thm_OAI_IsingPerceptron_enriched_poisson_root_variance

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma gaussian_pullback_measurePreserving {ι : Type*} (tag : ι → ℕ)
    (ht : Function.Injective tag) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i => g (tag i)) gaussianCoordinates
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp ht).map_fun_eq_infinitePi_map (fun _ => by fun_prop)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma integral_comp_preserving_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have h := integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hF)
  rw [hf.map_eq] at h
  exact h.symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma spinSign_integral (z : ℝ) :
    (∫ x : Fin 2, Real.exp (z*spinValue x) ∂(PMF.uniformOfFintype (Fin 2)).toMeasure) = Real.cosh z := by
  rw [integral_fintype (Integrable.of_finite),Fin.sum_univ_two]
  simp only [measureReal_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,spinValue]
  norm_num
  rw [Real.cosh_eq]
  ring

lemma finiteLogIntegral_magnetic {N : ℕ} (z : Fin N → ℝ) :
    finiteLogIntegral (spinLaw N) (magneticEnergy z) = ∑ i, Real.log (Real.cosh (z i)) := by
  unfold finiteLogIntegral magneticEnergy spinLaw
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (z i*spinValue x))]
  simp only [spinSign_integral]
  rw [Real.log_prod (fun i _ => (Real.cosh_pos _).ne')]

lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticEnergy_add {N : ℕ} (z w : Fin N → ℝ) :
    magneticEnergy (z+w) = magneticEnergy z+magneticEnergy w := by
  ext x
  simp [magneticEnergy,add_mul,Finset.sum_add_distrib]

lemma enrichedIncrement_zero {N n : ℕ} (h : ℕ → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) :
    enrichedIncrement N n h 0 i g =
      magneticEnergy (fun j => pathAmplitude h i*g ((Fintype.equivFin (EnrichedBlock N)) (.inl j))) := by
  ext x
  unfold enrichedIncrement enrichedCoefficientsFin
  have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun j => enrichedLevelCoefficient n h 0 i x j*g ((Fintype.equivFin (EnrichedBlock N)) j))
  simp only [Equiv.apply_symm_apply] at he
  rw [he]
  simp only [Fintype.sum_sum_type,enrichedLevelCoefficient,Pi.zero_apply,mul_zero,
    zero_mul,Finset.sum_const_zero,add_zero, magneticEnergy]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedIncrementLaw_zero (N n : ℕ) (h : ℕ → ℝ) (i : ℕ) :
    enrichedIncrementLaw N n h 0 i = magneticIncrementLaw N (pathAmplitude h i) := by
  let e := Fintype.equivFin (EnrichedBlock N)
  let tag : Fin N → ℕ := fun j => (e (.inl j)).val
  have ht : Function.Injective tag := fun j k hjk => Sum.inl_injective (e.injective (Fin.ext hjk))
  have hf := gaussian_pullback_measurePreserving (fun j : Fin (Fintype.card (EnrichedBlock N)) => j.val)
    Fin.val_injective
  have hg := gaussian_pullback_measurePreserving tag ht
  rw [Measure.infinitePi_eq_pi] at hf hg
  apply Subtype.ext
  change (Measure.pi _).map (enrichedIncrement N n h 0 i) = (Measure.pi _).map _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun j => pathAmplitude h i*z j)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [← hf.map_eq,← hg.map_eq,Measure.map_map (measurable_enrichedIncrement N n h 0 i)
     hf.measurable,Measure.map_map hm hg.measurable]
  congr 1
  ext g x
  rw [Function.comp_apply,Function.comp_apply,enrichedIncrement_zero]

lemma logMean_magneticIncrement {N : ℕ} (a b : ℝ) (F : (Spin N → ℝ) → ℝ)
    (hF : Measurable F) :
    logMean b (magneticIncrementLaw N a : Measure (Spin N → ℝ)) F =
      logMean b (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        (fun z => F (magneticEnergy (fun i => a*z i))) := by
  unfold logMean
  change Real.log (∫ H, Real.exp (b*F H) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)))/b = _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => a*z i)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [integral_map hm.aemeasurable
    ((hF.const_mul b).exp.aestronglyMeasurable)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticRecursion_growth (n : ℕ) (a b : ℕ → ℝ) (hb : ∀ i < n, 0 < b i) :
    Measurable (magneticRecursion n a b) ∧ HasLinearGrowth (magneticRecursion n a b) := by
  induction n generalizing a b with
  | zero => exact ⟨measurable_logCosh,logCosh_linearGrowth⟩
  | succ n ih =>
    have H := ih (fun i => a (i+1)) (fun i => b (i+1)) (fun i hi => hb (i+1) (by omega))
    exact ⟨measurable_gaussianTransform H.1 _ _,gaussianTransform_positive_linearGrowth H.1 H.2 _ (hb 0 (by omega))⟩

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

lemma energyRecursion_magnetic (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N) (magneticEnergy z) =
      ∑ i, magneticRecursion n a b (z i) := by
  induction n generalizing a b z with
  | zero => exact finiteLogIntegral_magnetic z
  | succ n ih =>
    let U := magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1))
    have hU := magneticRecursion_growth n (fun i => a (i+1)) (fun i => b (i+1))
      (fun i hi => hb (i+1) (by omega))
    change logMean (b 0) (magneticIncrementLaw N (a 0) : Measure (Spin N → ℝ))
      (fun H => energyRecursion n (fun i => b (i+1)) (fun i => magneticIncrementLaw N (a (i+1)))
        (spinLaw N) (magneticEnergy z+H)) = _
    have hm : Measurable (fun H : Spin N → ℝ => energyRecursion n (fun i => b (i+1))
        (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N) (magneticEnergy z+H)) :=
      (measurable_energyRecursion _ _ _ _).comp (measurable_const.add measurable_id)
    rw [logMean_magneticIncrement _ _ _ hm]
    have H (g : Fin N → ℝ) : energyRecursion n (fun i => b (i+1))
      (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N)
        (magneticEnergy z+magneticEnergy (fun i => a 0*g i)) = ∑ i, U (z i+a 0*g i) := by
      rw [← magneticEnergy_add]
      exact ih _ _ (fun i hi => ha (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) _
    simp_rw [H]
    rw [logMean_independent_sum (fun _ : Fin N => gaussianReal 0 1)
      (fun i t => U (z i+a 0*t)) (hb 0 (by omega)).ne']
    · apply Finset.sum_congr rfl
      intro i _
      simp only [magneticRecursion,gaussianTransform,(hb 0 (by omega)).ne',ite_false, if_false,
        Real.sqrt_sq (ha 0 (by omega)),logMean,U]
    · intro i
      exact hU.1.comp (measurable_const.add (measurable_id.const_mul _))
    · intro i
      exact integrable_exp_of_linearGrowth (gaussianReal 0 1)
        (gaussianReal_exponentialNormMoments _ _)
        (hU.1.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hU.2.add_left (z i)).scale_argument (a 0)) _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n with
  | zero => simp
  | succ n => simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron



lemma integral_magnetic_energyRecursion (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (a₀ : ℝ) :
    (∫ z, energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N)
       (magneticEnergy (fun i => a₀*z i)) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (N:ℝ)*(∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) := by
  have hU := magneticRecursion_growth n a b hb
  have hm : Measurable (fun z : ℝ => magneticRecursion n a b (a₀*z)) :=
    hU.1.comp (measurable_id.const_mul _)
  have hi := gaussian_linearGrowth_integrable hm (hU.2.scale_argument a₀) 0 1
  have hpi (i : Fin N) : Integrable (fun z : Fin N → ℝ => magneticRecursion n a b (a₀*z i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      (g := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable).mpr hi
  simp_rw [energyRecursion_magnetic N n a b ha hb]
  rw [integral_finsetSum _ (fun i _ => hpi i)]
  have he (i : Fin N) :
    (∫ z : Fin N → ℝ, magneticRecursion n a b (a₀*z i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) :=
    integral_comp_preserving_ae (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)
      (F := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 

theorem enrichedMeanPressure_initial_zero {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    enrichedMeanPressure P 0 n b h 0 (spinLaw N) φ = magneticFieldValue n b h := by
  have hu : ∀ j : Fin N, |(0 : Fin N → ℝ) j| ≤ 2 := by intro j; norm_num
  let μ := fun i => enrichedIncrementLaw N n h 0 (i+1)
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let ρ := Measure.infinitePi (fun _ : ℕ => P)
  have hL := (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1)
    hh h0 0 hu (spinLaw N) P hm hK hφ 0).1
  have hi : Integrable (fun p => energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p))
      ((poissonMeasure 0).prod (γ.prod ρ)) := hL.integrable (by norm_num)
  rw [enrichedMeanPressure_recursion hN n b hb hh h0 0 hu (spinLaw N) P hm hK hφ 0]
  change ((∫ p, energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p)
    ∂(poissonMeasure 0).prod (γ.prod ρ))-(N:ℝ)*h n/2)/(N:ℝ) = _
  rw [integral_prod _ hi,poissonMeasure_zero_eq_dirac,integral_dirac]
  have hbase (p : (Fin (EnrichedRootSize N) → ℝ) × (ℕ → A)) :
      enrichedPoissonBase n h 0 φ (0,p) = enrichedIncrement N n h 0 0 p.1 := by
    ext x
    simp [enrichedPoissonBase,enrichedBaseEnergy,rootPrefix,patternBase]
  simp_rw [hbase]
  rw [integral_fun_fst (fun z => energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z))]
  simp only [probReal_univ,one_smul]
  have hmap : (∫ z, energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z) ∂γ) =
      ∫ H, energyRecursion n b μ (spinLaw N) H ∂(enrichedIncrementLaw N n h 0 0 : Measure (Spin N → ℝ)) := by
    symm
    exact integral_map (measurable_enrichedIncrement N n h 0 0).aemeasurable
      (measurable_energyRecursion _ _ _ _).aestronglyMeasurable
  rw [hmap]
  dsimp only [μ]
  simp_rw [enrichedIncrementLaw_zero]
  have hmag : (∫ H, energyRecursion n b
        (fun i => magneticIncrementLaw N (pathAmplitude h (i+1))) (spinLaw N) H
      ∂(magneticIncrementLaw N (pathAmplitude h 0) : Measure (Spin N → ℝ))) =
      (N:ℝ)*(∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
        ∂gaussianReal 0 1) := by
    change (∫ H, energyRecursion n b (fun i => magneticIncrementLaw N (pathAmplitude h (i+1)))
      (spinLaw N) H ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
        (fun z => magneticEnergy (fun i => pathAmplitude h 0*z i))) = _
    have hme : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => pathAmplitude h 0*z i)) :=
      (measurable_magneticEnergy N).comp (by fun_prop)
    rw [integral_map hme.aemeasurable (measurable_energyRecursion _ _ _ _).aestronglyMeasurable]
    exact integral_magnetic_energyRecursion N n _ b (fun i _ => Real.sqrt_nonneg _)
      (fun i hi => (hb.1 i hi).1) _
  rw [hmag]
  unfold magneticFieldValue
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma measurable_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) :
    Measurable (finiteStepFunction ζ v) := by
  unfold finiteStepFunction
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Finiteness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_zero_variance (d : ℝ) (U : ℝ → ℝ) :
    gaussianTransform 0 d U = U := by
  ext x
  by_cases hd : d = 0
  · simp [gaussianTransform, hd]
  · simp [gaussianTransform, hd]

lemma magneticRecursion_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticRecursion n (fun _ => 0) b = fun x => Real.log (Real.cosh x) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [magneticRecursion, ih, zero_pow (by decide : 2 ≠ 0),
      gaussianTransform_zero_variance]

lemma magneticFieldValue_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticFieldValue n b (fun _ => 0) = 0 := by
  simp [magneticFieldValue, pathAmplitude, pathIncrement, magneticRecursion_zero]


lemma magneticFieldValue_nonpos (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) :
    magneticFieldValue n b h ≤ 0 := by
  let P : Measure Unit := Measure.dirac ()
  let φ : Unit → Spin 1 → ℝ := fun _ _ => 0
  have hm : Measurable φ := measurable_const
  have hφ : ∀ y x, |φ y x| ≤ (0 : ℝ) := by intros; simp [φ]
  have hu : ∀ j : Fin 1, |(0 : Fin 1 → ℝ) j| ≤ 2 := by simp
  have he := enrichedMeanPressure_field_add_le (N := 1) (by decide) n b hb
    (h := fun _ => 0) monotone_const le_rfl hh h0 0 hu (spinLaw 1) P hm le_rfl hφ 0
  simp only [zero_add] at he
  rw [enrichedMeanPressure_initial_zero (by decide) n b hb hh h0 P hm le_rfl hφ,
    enrichedMeanPressure_initial_zero (by decide) n b hb monotone_const le_rfl P hm le_rfl hφ,
    magneticFieldValue_zero] at he
  exact he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldBounds
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma heightSequence_mono (h : FieldStep) : Monotone (heightSequence h) := by
  intro i j hij
  apply h.ordered_height
  exact min_le_min_right h.depth hij

lemma heightSequence_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ heightSequence h i :=
  h.nonneg _

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

/-- Equality with the scalar recursion, including its root Gaussian average
and diagonal covariance subtraction. -/
lemma fieldValue_eq_magneticFieldValue (h : FieldStep) :
    fieldValue h 0 = IsingPerceptron.magneticFieldValue h.depth
      (IsingPerceptron.chainExponent h.cut) (heightSequence h) := by
  let w := heightSequence h
  have hw : Monotone w := heightSequence_mono h
  have hw0 : 0 ≤ w 0 := heightSequence_nonneg h 0
  have htail : List.ofFn (fun i : Fin h.depth =>
      ((fieldIncrement h i.succ).2, (fieldIncrement h i.succ).1)) =
      List.ofFn (fun i : Fin h.depth =>
        ((IsingPerceptron.pathAmplitude w (i + 1)) ^ 2,
          IsingPerceptron.chainExponent h.cut i)) := by
    apply congrArg List.ofFn
    funext i
    rw [IsingPerceptron.pathAmplitude_sq hw hw0]
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, IsingPerceptron.pathIncrement,
      IsingPerceptron.chainExponent_apply h.cut i.isLt]
    congr 1
    change h.height i.succ - h.height ⟨i.val, by omega⟩ =
      heightSequence h (i.val + 1) - heightSequence h i.val
    rw [heightSequence_eq h _ (by omega), heightSequence_eq h _ (by omega)]
    rfl
  have hfold : (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) =
      IsingPerceptron.magneticRecursion h.depth
        (fun i => IsingPerceptron.pathAmplitude w (i + 1))
        (IsingPerceptron.chainExponent h.cut) := by
    simp_rw [gaussianOperator_eq_transform]
    rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
      (g := fun sd f => IsingPerceptron.gaussianTransform sd.1 sd.2 f)]
    rw [List.map_ofFn]
    simp only [Function.comp_def]
    rw [htail]
    exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
      (fun i => IsingPerceptron.pathAmplitude w (i + 1))
      (IsingPerceptron.chainExponent h.cut)).symm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    dsimp only [fieldIncrement]
    simp [h.first]
  have hzero : w 0 = h.height 0 := heightSequence_eq h 0 (Nat.zero_le _)
  have hlast : w h.depth = h.height (Fin.last h.depth) := heightSequence_eq h _ le_rfl
  have hamp : IsingPerceptron.pathAmplitude w 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, hzero]
  rw [fieldValue, List.ofFn_succ, List.foldr_cons, hfold, hroot]
  simp only [gaussianOperator, ite_true, if_true, zero_add, IsingPerceptron.magneticFieldValue]
  dsimp only [w] at hamp hlast ⊢
  rw [hamp, hlast]

lemma fieldValue_nonpos (h : FieldStep) : fieldValue h 0 ≤ 0 := by
  rw [fieldValue_eq_magneticFieldValue]
  exact IsingPerceptron.magneticFieldValue_nonpos _ _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last)
    (heightSequence_mono h) (heightSequence_nonneg h 0)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp one-step Gaussian estimate for the entropy-domain majorant. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

/-- Jensen at exponent zero, under the same actual moment assumptions. -/
lemma mean_le_log_moment_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hi : Integrable F μ)
    {d : ℝ} (hd : 0 < d) (he : Integrable (fun x => Real.exp (d * F x)) μ) :
    (∫ x, F x ∂μ) ≤ d⁻¹ * Real.log (∫ x, Real.exp (d * F x) ∂μ) := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun x => mem_univ (d * F x))) (hi.const_mul d) he
  have hl := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp, integral_const_mul] at hl
  have ht := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd.le)
  have heq : d⁻¹ * (d * ∫ x, F x ∂μ) = ∫ x, F x ∂μ := by field_simp
  rwa [heq] at ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDomain
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-step entropy is finite for trial paths bounded strictly below one. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma measurable_fieldFunction (h : FieldStep) : Measurable (fieldFunction h) :=
  IsingPerceptron.measurable_finiteStepFunction h.cut h.height

lemma fieldFunction_le_last (h : FieldStep) (s : ℝ) :
    fieldFunction h s ≤ h.height (Fin.last h.depth) := by
  classical
  by_cases hex : ∃ i : Fin (h.depth + 1), h.cut i.castSucc < s ∧ s < h.cut i.succ
  · obtain ⟨i, hi⟩ := hex
    have he := IsingPerceptron.finiteStepFunction_on_cell h.ordered_cut h.height hi
    change IsingPerceptron.finiteStepFunction h.cut h.height s ≤ _
    rw [he]
    exact h.ordered_height (Fin.le_last _)
  · have he : fieldFunction h s = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hi => hex ⟨i, hi⟩)
    rw [he]
    exact h.nonneg _

lemma integrable_fieldFunction (h : FieldStep) : Integrable (fieldFunction h) pathMeasure := by
  apply (integrable_const (h.height (Fin.last h.depth))).mono'
    (measurable_fieldFunction h).aestronglyMeasurable
  filter_upwards [] with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fieldFunction_nonneg h s)] using
    fieldFunction_le_last h s

lemma integrable_path_mul_field (p : OverlapPath) (h : FieldStep) :
    Integrable (fun s => p s * fieldFunction h s) pathMeasure := by
  apply (integrable_fieldFunction h).mono'
    (p.measurable.mul (measurable_fieldFunction h)).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (p.nonneg s),
    abs_of_nonneg (fieldFunction_nonneg h s)]
  exact mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_value (h : FieldStep) (z : ℝ) :
    fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
      h.height (Fin.last h.depth) / 2 = fieldValue h z := by
  unfold fieldScalarValue fieldAllIncrements fieldValue
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldAllIncrements_root (h : FieldStep) :
    fieldAllIncrements h = (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
      scalarFieldIncrements h := by
  unfold fieldAllIncrements scalarFieldIncrements
  rw [List.ofFn_succ]
  congr 1
  apply Prod.ext
  · exact h.first
  · apply Subtype.ext
    simp [fieldIncrement]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPairingPathError
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing error for the weighted magnetic overlap path. The estimate
depends only on path bounds and the heights of the two fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_pairing_path_support_error (p B : OverlapPath) (h k : FieldStep) :
    |fieldPairing p k - fieldPairing p h -
      ∫ s, B s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure| ≤
      (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) *
        ∫ s, |B s - p s| ∂pathMeasure := by
  let D := fun s => fieldFunction k s - fieldFunction h s
  have hiB : Integrable (fun s => B s * D s) pathMeasure := by
    apply ((integrable_path_mul_field B k).sub (integrable_path_mul_field B h)).congr
    apply ae_of_all
    intro s
    change B s * fieldFunction k s - B s * fieldFunction h s = B s * D s
    dsimp only [D]
    ring
  have hip : Integrable (fun s => p s * D s) pathMeasure := by
    apply ((integrable_path_mul_field p k).sub (integrable_path_mul_field p h)).congr
    apply ae_of_all
    intro s
    change p s * fieldFunction k s - p s * fieldFunction h s = p s * D s
    dsimp only [D]
    ring
  have he : fieldPairing p k - fieldPairing p h -
      (∫ s, B s * D s ∂pathMeasure) = ∫ s, (p s - B s) * D s ∂pathMeasure := by
    rw [fieldPairing, fieldPairing, ← integral_sub (integrable_path_mul_field p k)
      (integrable_path_mul_field p h)]
    simp_rw [← mul_sub]
    rw [← integral_sub hip hiB]
    congr 1
    funext s
    ring
  have hiabs : Integrable (fun s => |B s - p s|) pathMeasure := (B.integrable.sub p.integrable).abs
  have hib := hiabs.const_mul (k.height (Fin.last k.depth) + h.height (Fin.last h.depth))
  rw [he]
  calc
    _ ≤ ∫ s, |(p s - B s) * D s| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) * |B s - p s|
        ∂pathMeasure := by
      apply integral_mono ((hip.sub hiB).congr (ae_of_all _ (fun s => by
        dsimp only [Pi.sub_apply]
        ring))).abs hib
      intro s
      dsimp only
      rw [abs_mul, abs_sub_comm (p s) (B s)]
      have hD : |D s| ≤ k.height (Fin.last k.depth) + h.height (Fin.last h.depth) := by
        dsimp only [D]
        exact (abs_sub _ _).trans (by
          rw [abs_of_nonneg (fieldFunction_nonneg k s), abs_of_nonneg (fieldFunction_nonneg h s)]
          exact add_le_add (fieldFunction_le_last k s) (fieldFunction_le_last h s))
      exact (mul_le_mul_of_nonneg_left hD (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

lemma trial_le_of_path_support (p B : OverlapPath) (h k : FieldStep) (u v : ℝ)
    (hsupport : v ≤ u -
      (∫ s, B s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure) / 2) :
    v + fieldPairing p k / 2 ≤ u + fieldPairing p h / 2 +
      (k.height (Fin.last k.depth) + h.height (Fin.last h.depth)) / 2 *
        ∫ s, |B s - p s| ∂pathMeasure := by
  have hb := (abs_le.mp (field_pairing_path_support_error p B h k)).2
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldBias
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical mean spin is the bias derivative of the actual finite
field functional, including its zero-exponent root Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldValue_root (h : FieldStep) (b : ℝ) :
    fieldValue h b =
      gaussianOperator 0 (h.height 0)
        (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b -
      h.height (Fin.last h.depth) / 2 := by
  rw [← fieldAllIncrements_value h b, fieldAllIncrements_root]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLowerBound
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear bias coercivity for the finite magnetic field functional.
The lower estimate is preserved by the actual Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma affine_le_gaussianOperator {F : ℝ → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {a : ℝ} (ha : 0 ≤ a) (v : ℝ≥0)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ gaussianOperator a v F z := by
  have hi : Integrable (fun u : ℝ => u) (gaussianReal z v) := IsGaussian.integrable_id
  have hmean : m * z + c ≤ ∫ u, F u ∂gaussianReal z v := by
    calc
      _ = ∫ u, m * u + c ∂gaussianReal z v := by
        rw [integral_add (hi.const_mul m) (integrable_const c),
          integral_const_mul, integral_id_gaussianReal, integral_const]
        simp
      _ ≤ _ := integral_mono ((hi.const_mul m).add (integrable_const c))
        (field_gaussian_linear_integrable v z hF hG) hl
  by_cases ha0 : a = 0
  · subst a
    rwa [gaussianOperator_eq_gaussian_integral v hF]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_gaussian_exp_integral ha0 v hF]
    exact hmean.trans (mean_le_log_moment_div (gaussianReal z v)
      (field_gaussian_linear_integrable v z hF hG) hap
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG a))

lemma affine_le_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ fieldScalarValue L F z := by
  induction L generalizing z with
  | nil => exact hl z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htail := fieldScalarValue_regular L ht hF hG
    exact affine_le_gaussianOperator htail.1 htail.2 (hL av (List.mem_cons_self)).le
      av.2 m c (ih ht) z

lemma signed_bias_le_logcosh (b : ℝ) :
    b - Real.log 2 ≤ Real.log (Real.cosh b) := by
  have he : Real.exp b ≤ 2 * Real.cosh b := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-b)]
  have hl := Real.log_le_log (Real.exp_pos b) he
  rw [Real.log_exp, Real.log_mul (by norm_num) (Real.cosh_pos b).ne'] at hl
  linarith

lemma fieldValue_bias_lower (h : FieldStep) (b : ℝ) :
    |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤ fieldValue h b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hplus : ∀ z, (1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [one_mul, sub_eq_add_neg] using signed_bias_le_logcosh z
  have hminus : ∀ z, (-1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [Real.cosh_neg, neg_mul, one_mul, sub_eq_add_neg]
      using signed_bias_le_logcosh (-z)
  have hp := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) 1 (-Real.log 2) hplus b
  have hm := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (-1) (-Real.log 2) hminus b
  change 1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hp
  change -1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hm
  rw [fieldValue_root]
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos hb]
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldMinimum
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite prescribed-magnetization functional has an attained bias
minimum at every interior magnetization. No optimizer or concavity premise
is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticBiasObjective_lower (h : FieldStep) (s b : ℝ) :
    (1 - |s|) * |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤
      magneticBiasObjective h s b := by
  have hp : b * s ≤ |b| * |s| := by
    simpa only [abs_mul] using le_abs_self (b * s)
  have hl := fieldValue_bias_lower h b
  unfold magneticBiasObjective
  nlinarith

lemma magneticBiasObjective_bddBelow (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) :
    BddBelow (Set.range (magneticBiasObjective h s)) := by
  refine ⟨-Real.log 2 - h.height (Fin.last h.depth) / 2, ?_⟩
  rintro _ ⟨b, rfl⟩
  have hp : 0 ≤ (1 - |s|) * |b| := mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg b)
  linarith [magneticBiasObjective_lower h s b]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldParameter
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bias infimum is finite and concave in the prescribed magnetization.
Its actual minimizing bias supplies the supporting slope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma constrainedFieldValue_le_trial (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) (b : ℝ) :
    constrainedFieldValue h s ≤ fieldValue h b - b * s :=
  csInf_le (magneticBiasObjective_bddBelow h hs) ⟨b, rfl⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariational
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed-magnetization variational expression in (7.3)--(7.4).
One common covariance path is used for every field group. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma magneticGroupValue_le {A : Type*} [Fintype A] (γ m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hm : ∀ a, |m a| ≤ 1) (h : FieldStep) :
    magneticGroupValue γ m h ≤ fieldValue h 0 := by
  calc
    _ ≤ ∑ a, γ a * fieldValue h 0 := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (by
        simpa only [zero_mul, sub_zero] using constrainedFieldValue_le_trial h (hm a) 0) (hγ a))
    _ = _ := by rw [← Finset.sum_mul, hγsum, one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticEntropySequence
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
attribute [-simp] _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate self-consistency makes the weighted magnetic field values
approach the entropy supremum. Uniform height bounds avoid needing a limit
of the fields themselves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_group_trial_upper {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (hmag : ∀ a, |mag a| ≤ 1)
    (p : OverlapPath) (h : FieldStep) :
    magneticGroupValue γ mag h + fieldPairing p h / 2 ≤ h.height (Fin.last h.depth) / 2 := by
  have hp : fieldPairing p h ≤ h.height (Fin.last h.depth) := by
    have hh := integral_mono (integrable_path_mul_field p h) (integrable_const (h.height (Fin.last h.depth)))
      (fun s => (mul_le_of_le_one_left (fieldFunction_nonneg h s) (p.le_one s)).trans
        (fieldFunction_le_last h s))
    simpa only [fieldPairing, integral_const, probReal_univ, one_smul] using hh
  linarith [magneticGroupValue_le γ mag hγ hγsum hmag h, fieldValue_nonpos h]

theorem magnetic_entropy_sequence_of_support_oai {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s * (fieldFunction k s - fieldFunction (h n) s)
        ∂pathMeasure) / 2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2)
      atTop (𝓝 (magneticEntropyFunctional γ mag p).toReal) := by
  let V := fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2
  let e := fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure
  have he0 n : 0 ≤ e n := integral_nonneg (fun _ => abs_nonneg _)
  have hV n : V n ≤ C / 2 := (magnetic_group_trial_upper γ mag hγ hγsum hmag p (h n)).trans (by linarith [hC n])
  have happrox (n : ℕ) (k : FieldStep) :
      magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ V n +
        ((k.height (Fin.last k.depth) + C) / 2) * e n := by
    have hb := trial_le_of_path_support p (magneticGroupPath γ mag hγ hγsum (h n)) (h n) k _ _ (hsupport n k)
    change magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ V n +
      ((k.height (Fin.last k.depth) + (h n).height (Fin.last (h n).depth)) / 2) * e n at hb
    have hc : (k.height (Fin.last k.depth) + (h n).height (Fin.last (h n).depth)) / 2 ≤
        (k.height (Fin.last k.depth) + C) / 2 := by linarith [hC n]
    exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (he0 n)))
  have hall (k : FieldStep) : magneticGroupValue γ mag k + fieldPairing p k / 2 ≤ C / 2 := by
    have ht : Tendsto (fun n => C / 2 +
        ((k.height (Fin.last k.depth) + C) / 2) * e n) atTop (𝓝 (C / 2)) := by
      simpa only [mul_zero, add_zero] using
        (hself.const_mul ((k.height (Fin.last k.depth) + C) / 2)).const_add (C / 2)
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n => (happrox n k).trans (add_le_add (hV n) le_rfl))
  have hE : magneticEntropyFunctional γ mag p ≤ ((C / 2 : ℝ) : EReal) := by
    apply iSup_le
    intro k
    exact_mod_cast hall k
  have htop : magneticEntropyFunctional γ mag p ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hE
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      (le_iSup (fun k : FieldStep => ((magneticGroupValue γ mag k + fieldPairing p k / 2 : ℝ) : EReal))
        zeroField)
  let S := (magneticEntropyFunctional γ mag p).toReal
  have hS : magneticEntropyFunctional γ mag p = (S : EReal) := (EReal.coe_toReal htop hbot).symm
  have hVS n : V n ≤ S := by
    have hh := le_iSup (fun k : FieldStep =>
      ((magneticGroupValue γ mag k + fieldPairing p k / 2 : ℝ) : EReal)) (h n)
    change (V n : EReal) ≤ magneticEntropyFunctional γ mag p at hh
    rw [hS] at hh
    exact_mod_cast hh
  refine ⟨htop, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have hlt : ((S - ε / 2 : ℝ) : EReal) < magneticEntropyFunctional γ mag p := by
    rw [hS]
    exact_mod_cast (show S - ε / 2 < S by linarith)
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  have hk' : S - ε / 2 < magneticGroupValue γ mag k + fieldPairing p k / 2 := by exact_mod_cast hk
  have hsmall := (hself.const_mul ((k.height (Fin.last k.depth) + C) / 2)).eventually
    (gt_mem_nhds (show ((k.height (Fin.last k.depth) + C) / 2) * 0 < ε / 2 by
      simpa using half_pos hε))
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hVS n))]
  have hb := happrox n k
  change ((k.height (Fin.last k.depth) + C) / 2) * e n < ε / 2 at hn
  change -(V n - S) < ε
  linarith

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.magnetic_entropy_sequence_of_support_oai.{u_1} := @OAI.InvariantIsing.magnetic_entropy_sequence_of_support_oai.{u_1}
