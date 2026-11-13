-- Prove2me | solution 1 for OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:02:36.519216+00:00
-- url     : https://prove2.me/submissions/2c5b337d-1429-4023-b531-6e0fbd671176

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
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
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
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
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
import Theorems.Thm_OAI_InvariantIsing_fieldBiasMean_magneticBias
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_magneticEntropyFunctional_lower
import Theorems.Thm_OAI_InvariantIsing_magneticFieldLevel_radial
import Theorems.Thm_OAI_InvariantIsing_magneticHeightLevel_coordinate_right_order
import Theorems.Thm_OAI_InvariantIsing_magnetic_entropy_sequence_of_support

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

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

/-- Equation (4.10): uniform deficit error is bounded by the L¹ path error. -/
lemma abs_deficit_sub_path_le (p q : OverlapPath) (r : ℝ) :
    |deficit p r - deficit q r| ≤ ∫ s, |p s - q s| ∂pathMeasure := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (q.integrable_complement_max r)]
  calc
    _ ≤ ∫ s, |(1 - max (p s) r) - (1 - max (q s) r)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, |p s - q s| ∂pathMeasure := by
      apply integral_mono
        ((p.integrable_complement_max r).sub (q.integrable_complement_max r)).abs
        (p.integrable.sub q.integrable).abs
      intro s
      have he : (1 - max (p s) r) - (1 - max (q s) r) =
          -(max (p s) r - max (q s) r) := by ring
      change |(1 - max (p s) r) - (1 - max (q s) r)| ≤ |p s - q s|
      rw [he, abs_neg]
      exact abs_max_sub_max_le_abs (p s) (q s) r

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma gaussianTransform_const_add {U : ℝ → ℝ} (hU : Measurable U) (hG : HasLinearGrowth U)
    (s d c : ℝ) :
    gaussianTransform s d (fun x => c+U x) = fun x => c+gaussianTransform s d U x := by
  ext x
  by_cases hd : d=0
  · simp only [gaussianTransform,hd,ite_true, if_true]
    have hi : Integrable (fun z : ℝ => U (x+Real.sqrt s*z)) (gaussianReal 0 1) :=
      gaussian_linearGrowth_integrable
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) _ _
    rw [integral_add (integrable_const c) hi]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [gaussianTransform,hd,ite_false, if_false]
    exact logMean_const_add (gaussianReal 0 1) hd
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d) c

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_BoundedTiltAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Tilt Average. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTiltAverage_zero (s : ℝ) (U A : ℝ → ℝ) (x : ℝ) :
    gaussianTiltAverage s 0 U A x = ∫ z, A (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  simp [gaussianTiltAverage]

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

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

lemma finiteStepFunction_mul {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v w : Fin k → ℝ) :
    (fun u => finiteStepFunction ζ v u*finiteStepFunction ζ w u) = finiteStepFunction ζ (fun i => v i*w i) := by
  ext u
  unfold finiteStepFunction
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ζ i.castSucc<u ∧ u<ζ i.succ
  · simp only [hi]
    change v i*finiteStepFunction ζ w u=v i*w i
    rw [finiteStepFunction_on_cell hz w hi]
  · simp only [hi,ite_false, if_false,zero_mul]

lemma integral_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u ∂pathMeasure) = ∑ i, (ζ i.succ-ζ i.castSucc)*v i := by
  classical
  let : IsFiniteMeasure pathMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs (i : Fin k) : Ioo (ζ i.castSucc) (ζ i.succ) ⊆ Ioo (0:ℝ) 1 := by
    intro u hu
    have h0 : 0≤ζ i.castSucc := by rw [← hz0]; exact hz.monotone (Fin.zero_le _)
    have h1 : ζ i.succ≤1 := by rw [← hz1]; exact hz.monotone (Fin.le_last _)
    exact ⟨h0.trans_lt hu.1,hu.2.trans_le h1⟩
  have hind (i : Fin k) : (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) =
      (Ioo (ζ i.castSucc) (ζ i.succ)).indicator (fun _ : ℝ => v i) := by
    ext u
    simp only [Set.indicator_apply,Set.mem_Ioo]
  have hi (i : Fin k) : Integrable (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) pathMeasure := by
    rw [hind]
    exact (integrable_const (v i)).indicator measurableSet_Ioo
  unfold finiteStepFunction
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hind]
  rw [integral_indicator measurableSet_Ioo]
  have he : pathMeasure.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) = volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (hs i)]
  rw [he,integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hz.monotone (Fin.castSucc_le_succ i))),smul_eq_mul]

lemma integral_finiteStepFunction_mul {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v w : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u*finiteStepFunction ζ w u ∂pathMeasure) =
      ∑ i, (ζ i.succ-ζ i.castSucc)*v i*w i := by
  rw [finiteStepFunction_mul hz,integral_finiteStepFunction ζ hz hz0 hz1]
  apply Finset.sum_congr rfl
  intro i _
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_linearGrowth : HasLinearGrowth (fun x : ℝ => |x|) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun x => ?_⟩
  simp only [abs_abs,zero_add,one_mul,Real.norm_eq_abs,le_refl]

lemma gaussian_abs_exp_bound (a x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ z, Real.exp (d*|x+a*z|) ∂gaussianReal 0 1) ≤
      2*Real.exp (d*|x|+(d*a)^2/2) := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+a*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument a) d
  have hj : Integrable (fun z : ℝ => Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z))) (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal (d*a)).add (integrable_exp_mul_gaussianReal (-d*a))).const_mul _
  have hp (z : ℝ) : Real.exp (d*|x+a*z|) ≤ Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) := by
    calc
      _ ≤ Real.exp (d*(|x|+|a*z|)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le _ _) hd)
      _ = Real.exp (d*|x|)*Real.exp (d*|a*z|) := by rw [mul_add,Real.exp_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        by_cases h : 0 ≤ a*z
        · rw [abs_of_nonneg h]
          have he : d*(a*z) = (d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_neg (lt_of_not_ge h)]
          have he : d*-(a*z) = (-d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ ∫ z, Real.exp (d*|x|)*(Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) ∂gaussianReal 0 1 :=
      integral_mono hi hj hp
    _ = _ := by
      rw [integral_const_mul,integral_add (integrable_exp_mul_gaussianReal _) (integrable_exp_mul_gaussianReal _)]
      have hmgf (t : ℝ) : (∫ z : ℝ, Real.exp (t*z) ∂gaussianReal 0 1) = Real.exp (t^2/2) := by
        simpa [mgf] using mgf_gaussianReal (p := gaussianReal 0 1) (μ := 0) (v := 1) (X := fun z : ℝ => z) (by simp) t
      rw [hmgf,hmgf]
      have hs : (-d*a)^2 = (d*a)^2 := by ring
      rw [hs,Real.exp_add]
      ring

lemma gaussianTransform_abs_bound {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (x : ℝ) :
    gaussianTransform s d (fun y => |y|) x ≤ |x|+d*s/2+Real.log 2/d := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+Real.sqrt s*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument (Real.sqrt s)) d
  change (if d=0 then _ else _/d) ≤ _
  rw [ite_eq_right hd.ne']
  apply (div_le_iff₀ hd).2
  have H := Real.log_le_log (integral_exp_pos (gaussianReal 0 1) _ hi)
    (gaussian_abs_exp_bound (Real.sqrt s) x hd.le)
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at H
  have hsq := Real.sq_sqrt hs
  apply H.trans_eq
  rw [mul_pow,hsq]
  field_simp
  ring

end IsingPerceptron

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deficit and cumulative masses of a genuine finite overlap
quantile, with atoms retained at all cell values. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma ae_finite_overlap_cell {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1) :
    ∀ᵐ s ∂pathMeasure, ∃ j : Fin (n + 1), s ∈ Ioo (cut j.castSucc) (cut j.succ) := by
  let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
  have hne : ∀ᵐ s ∂pathMeasure, ∀ j, s ≠ cut j :=
    ae_all_iff.mpr (fun j => Measure.ae_ne pathMeasure (cut j))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
  obtain ⟨j, hlo, hhi⟩ := IsingPerceptron.finite_partition_cell cut
    (by simpa only [hfirst] using hs.1.le) (by simpa only [hlast] using hs.2)
  exact ⟨j, lt_of_le_of_ne hlo (hns j.castSucc).symm, hhi⟩

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_zero_variance (ζ : ℝ) (F a : ℝ → ℝ) (z : ℝ) :
    fieldSpinTransition ζ 0 F a z = a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianReal_zero_var]
  simp only [integral_dirac]
  exact mul_div_cancel_left₀ (a z) (Real.exp_ne_zero _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_mono {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFG : IsingPerceptron.HasLinearGrowth F) (hGG : IsingPerceptron.HasLinearGrowth G)
    (h : ∀ z, F z ≤ G z) {a : ℝ} (ha : 0 ≤ a) (v z : ℝ) :
    gaussianOperator a v F z ≤ gaussianOperator a v G z := by
  by_cases ha0 : a = 0
  · simp only [gaussianOperator, ha0, ite_true, if_true]
    apply integral_mono
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) _ _)
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) _ _)
    exact fun y => h _
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_transform, gaussianOperator_eq_transform]
    simp only [IsingPerceptron.gaussianTransform, ha0, ite_false, if_false]
    exact IsingPerceptron.logMean_mono (gaussianReal 0 1) hap
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) a)
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) a)
      (fun y => h _)

lemma linearGrowth_const_add {F : ℝ → ℝ} (hF : IsingPerceptron.HasLinearGrowth F)
    (c : ℝ) : IsingPerceptron.HasLinearGrowth (fun z => c + F z) := by
  obtain ⟨C, L, hC, hL, h⟩ := hF
  refine ⟨|c| + C, L, add_nonneg (abs_nonneg _) hC, hL, fun z => ?_⟩
  exact (abs_add_le _ _).trans (by linarith [h z])

lemma gaussianOperator_const_add {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) (c a v z : ℝ) :
    gaussianOperator a v (fun x => c + F x) z = c + gaussianOperator a v F z := by
  simp only [gaussianOperator_eq_transform]
  exact congrFun (IsingPerceptron.gaussianTransform_const_add hF hFG v a c) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite scalar log-cosh recursion with affine covariance
increments is a smooth field family on its strict covariance interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldAffineFamily_value (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) :
    (fieldAffineFamily I hI L hL).U = fieldAffineValue L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    funext p
    simp only [fieldAffineFamily, FieldSmoothFamily.transform, FieldSmoothFamily.value,
      fieldAffineValue]
    rw [ih]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear identities for the actual tilted scalar transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_const_mul (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ)
    (c z : ℝ) :
    fieldSpinTransition ζ v F (fun u => c * a u) z = c * fieldSpinTransition ζ v F a z := by
  exact integral_const_mul c _

lemma fieldSpinTransition_add (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u + b u) z =
      fieldSpinTransition ζ v F a z + fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  exact integral_add
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbB u))

lemma fieldSpinTransition_const (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    fieldSpinTransition ζ v F (fun _ => c) z = c := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  simp only [fieldSpinTransition, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCompensatedTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compensation of the covariance derivative by the spatial generator.
The identity telescopes adjacent covariance increments; it uses the actual
Gaussian transition and does not require exchanging mixed derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_gaussianTiltAverage_const (s ζ : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    gaussianTiltAverage s ζ F (fun _ => c) z = c := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF measurable_const]
  exact fieldSpinTransition_const ζ (Real.toNNReal s) hF hg c z

lemma field_gaussianTiltAverage_const_mul (s ζ : ℝ) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (c z : ℝ) :
    gaussianTiltAverage s ζ F (fun y => c * a y) z =
      c * gaussianTiltAverage s ζ F a z := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF (ha.const_mul c),
    field_gaussianTiltAverage_eq_transition s ζ hF ha]
  exact fieldSpinTransition_const_mul ζ (Real.toNNReal s) F a c z

lemma field_gaussianTiltAverage_add (s ζ : ℝ) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ y, |a y| ≤ A) (hbB : ∀ y, |b y| ≤ B) (z : ℝ) :
    gaussianTiltAverage s ζ F (fun y => a y + b y) z =
      gaussianTiltAverage s ζ F a z + gaussianTiltAverage s ζ F b z := by
  have hm : Measurable (fun y => a y + b y) := ha.add hb
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hm,
    field_gaussianTiltAverage_eq_transition s ζ hF ha,
    field_gaussianTiltAverage_eq_transition s ζ hF hb]
  exact fieldSpinTransition_add ζ (Real.toNNReal s) hF hg ha hb haB hbB z

namespace FieldSmoothFamily

theorem compensated_tangent {I : Set ℝ} (F : FieldSmoothFamily I)
    (a d dprev ζ η : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    F.tangent a (d - dprev) ζ p + dprev / 2 *
        (F.curvature a (d - dprev) ζ p + ζ * (F.mean a (d - dprev) ζ p) ^ 2) =
      gaussianTiltAverage (a + (d - dprev) * p.1) ζ (fun y => F.U (p.1, y))
        (fun y => F.T (p.1, y) + d / 2 * (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) p.2 -
      d / 2 * (η - ζ) *
        gaussianTiltAverage (a + (d - dprev) * p.1) ζ (fun y => F.U (p.1, y))
          (fun y => (F.X (p.1, y)) ^ 2) p.2 := by
  let s := a + (d - dprev) * p.1
  have hU : Measurable (fun y => F.U (p.1, y)) := F.mU.comp (by fun_prop)
  have hT : Measurable (fun y => F.T (p.1, y)) := F.mT.comp (by fun_prop)
  have hXX : Measurable (fun y => F.XX (p.1, y)) := F.mXX.comp (by fun_prop)
  have hXsq : Measurable (fun y => (F.X (p.1, y)) ^ 2) :=
    (F.mX.comp (by fun_prop)).pow_const 2
  have hsq : ∀ y, |(F.X (p.1, y)) ^ 2| ≤ F.KX ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (F.bX (p.1, y)) 2
  have hm (r : ℝ) : Measurable (fun y => F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2) :=
    hXX.add (hXsq.const_mul r)
  have hb (r : ℝ) : ∀ y, |F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2| ≤
      F.KXX + |r| * F.KX ^ 2 :=
    bounded_generator (fun y => F.bX (p.1, y)) (fun y => F.bXX (p.1, y)) r
  have hexpand (r : ℝ) :
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
          (fun y => F.XX (p.1, y) + r * (F.X (p.1, y)) ^ 2) p.2 =
        gaussianTiltAverage s ζ (fun y => F.U (p.1, y)) (fun y => F.XX (p.1, y)) p.2 +
          r * gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
            (fun y => (F.X (p.1, y)) ^ 2) p.2 := by
    rw [field_gaussianTiltAverage_add s ζ hU (F.growth p.1) hXX (hXsq.const_mul r)
      (fun y => F.bXX (p.1, y)) (fun y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hsq y) (abs_nonneg r)),
      field_gaussianTiltAverage_const_mul s ζ hU hXsq]
  have hfull :
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
        (fun y => F.T (p.1, y) + d / 2 * (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) p.2 =
      gaussianTiltAverage s ζ (fun y => F.U (p.1, y)) (fun y => F.T (p.1, y)) p.2 +
        d / 2 * gaussianTiltAverage s ζ (fun y => F.U (p.1, y))
          (fun y => F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2) p.2 := by
    rw [field_gaussianTiltAverage_add s ζ hU (F.growth p.1) hT ((hm η).const_mul (d / 2))
      (fun y => F.bT (p.1, y) hp) (fun y => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb η y) (abs_nonneg (d / 2))),
      field_gaussianTiltAverage_const_mul s ζ hU (hm η)]
  change F.tangent a (d - dprev) ζ p + dprev / 2 *
      (F.curvature a (d - dprev) ζ p + ζ * (F.mean a (d - dprev) ζ p) ^ 2) = _
  rw [hfull, hexpand η]
  unfold tangent curvature
  rw [show a + (d - dprev) * p.1 = s from rfl, hexpand ζ]
  ring

end FieldSmoothFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAdjacentDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjacent-variance cancellation for a single field height. Its
derivative is the negative conditional squared spin mean. This proves
the local identity underlying `fld:backward-derivative` directly from
the Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing.FieldSmoothFamily

theorem parameter_derivative {I : Set ℝ} (F : FieldSmoothFamily I)
    (t z : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => F.U (s, z)) (F.T (t, z)) t := by
  have hmap : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hd := (F.derivative (t, z) ht).comp_hasDerivAt t hmap
  simpa [pairLinear, Function.comp_def] using hd

theorem negative_variance_compensation {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : IsOpen I) (b η : ℝ) (hv : ∀ t ∈ I, 0 < b - t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) (hT : ∀ y, F.T (p.1, y) = 0) :
    (F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).T p +
      (1 / 2 : ℝ) *
        ((F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).XX p + η *
          ((F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).X p) ^ 2) = 0 := by
  have hc := F.compensated_tangent b 0 1 η η hp
  have hz : (fun y => F.T (p.1, y) + (0 : ℝ) / 2 *
      (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) = fun _ => 0 := by
    funext y
    simp only [hT y, zero_div, zero_mul, add_zero]
  have hm : Measurable (fun y => F.U (p.1, y)) := F.mU.comp (by fun_prop)
  rw [hz, field_gaussianTiltAverage_const _ _ hm (F.growth p.1)] at hc
  change F.tangent b (-1) η p + (1 / 2 : ℝ) *
    (F.curvature b (-1) η p + η * (F.mean b (-1) η p) ^ 2) = 0
  simpa only [sub_self, sub_zero, zero_sub, zero_div, zero_mul] using hc

theorem adjacent_tangent {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : IsOpen I) (a b ζ η : ℝ)
    (hplus : ∀ t ∈ I, 0 < a + t) (hminus : ∀ t ∈ I, 0 < b - t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) (hT : ∀ y, F.T (p.1, y) = 0) :
    let G := F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hminus)
    let H := G.transform hI a 1 ζ (by simpa only [one_mul] using hplus)
    H.T p = -(η - ζ) / 2 * gaussianTiltAverage (a + p.1) ζ
      (fun y => G.U (p.1, y)) (fun y => (G.X (p.1, y)) ^ 2) p.2 := by
  let G := F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hminus)
  change G.tangent a 1 ζ p = -(η - ζ) / 2 *
    gaussianTiltAverage (a + p.1) ζ (fun y => G.U (p.1, y))
      (fun y => (G.X (p.1, y)) ^ 2) p.2
  have hc := G.compensated_tangent a 1 0 ζ η hp
  have hz : (fun y => G.T (p.1, y) + (1 : ℝ) / 2 *
      (G.XX (p.1, y) + η * (G.X (p.1, y)) ^ 2)) = fun _ => 0 := by
    funext y
    exact F.negative_variance_compensation hI b η hminus hp hT
  have hm : Measurable (fun y => G.U (p.1, y)) := G.mU.comp (by fun_prop)
  rw [hz, field_gaussianTiltAverage_const _ _ hm (G.growth p.1)] at hc
  simp only [sub_zero, one_mul, zero_div, zero_mul, add_zero] at hc
  calc
    G.tangent a 1 ζ p = _ := hc
    _ = _ := by ring

end InvariantIsing.FieldSmoothFamily

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the affine family with the already constructed
finite scalar values and physical conditional means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldAffineValue_scalar (L : List FieldAffineStep) (t : ℝ) :
    (fun z => fieldAffineValue L (t, z)) =
      fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    change gaussianTransform (av.base + av.slope * t) av.exponent
        (fun z => fieldAffineValue L (t, z)) = _
    rw [field_gaussianTransform_eq_operator, ih]
    rfl

theorem fieldAffineFamily_mean (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) (t : ℝ) :
    (fun z => (fieldAffineFamily I hI L hL).X (t, z)) =
      fieldScalarMean (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldAffineFamily I hI L htail
    have hU : (fun z => G.U (t, z)) =
        fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
      rw [show G.U = fieldAffineValue L from fieldAffineFamily_value I hI L htail]
      exact fieldAffineValue_scalar L t
    have hX : (fun z => G.X (t, z)) =
        fieldScalarMean (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) Real.tanh :=
      ih htail
    change gaussianTiltAverage (av.base + av.slope * t) av.exponent
      (fun z => G.U (t, z)) (fun z => G.X (t, z)) = _
    have hmU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
    have hmX : Measurable (fun z => G.X (t, z)) := G.mX.comp (by fun_prop)
    rw [field_gaussianTiltAverage_eq_transition _ _
      hmU hmX, hU, hX]
    rfl

theorem fieldAffineFamily_stationary (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t)
    (hs : ∀ av ∈ L, av.slope = 0) (p : ℝ × ℝ) :
    (fieldAffineFamily I hI L hL).T p = 0 := by
  induction L generalizing p with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldAffineFamily I hI L htail
    have hT : (fun y => G.T (p.1, y)) = fun _ => 0 := by
      funext y
      exact ih htail (fun bv hb => hs bv (List.mem_cons_of_mem av hb)) (p.1, y)
    change G.tangent av.base av.slope av.exponent p = 0
    unfold FieldSmoothFamily.tangent
    rw [hs av List.mem_cons_self, hT]
    simp only [zero_mul, add_zero, zero_div]
    have hmU : Measurable (fun z => G.U (p.1, z)) := G.mU.comp (by fun_prop)
    exact field_gaussianTiltAverage_const _ _ hmU (G.growth p.1) 0 p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldConstantPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation of a covariance derivative through the unchanged earlier
levels. The propagated tangent is the actual conditional expectation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldConstantPrefix_value {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldConstantPrefix hI F L hL).U (t, z)) =
      fieldScalarValue L (fun z => F.U (t, z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F L htail
    change gaussianTransform ((av.2 : ℝ) + 0 * t) av.1 (fun z => G.U (t, z)) = _
    rw [field_gaussianTransform_eq_operator]
    simp only [zero_mul, add_zero, Real.toNNReal_coe]
    rw [show (fun z => G.U (t, z)) = fieldScalarValue L (fun z => F.U (t, z)) from ih htail]
    rfl

theorem fieldConstantPrefix_tangent {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldConstantPrefix hI F L hL).T (t, z)) =
      fieldScalarMean L (fun z => F.U (t, z)) (fun z => F.T (t, z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F L htail
    have hU := fieldConstantPrefix_value hI F L htail t
    have hT := ih htail
    have hmU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
    have hmT : Measurable (fun z => G.T (t, z)) := G.mT.comp (by fun_prop)
    change (fun z => G.tangent av.2 0 av.1 (t, z)) = _
    simp only [FieldSmoothFamily.tangent, zero_mul, zero_div, add_zero]
    rw [field_gaussianTiltAverage_eq_transition _ _ hmU hmT]
    simp only [Real.toNNReal_coe]
    rw [hU, hT]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAdjacentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual internal-height comparison in `fld:mixed`. The fixed
tail is the finite log-cosh recursion. Increasing one height adds its
parameter to one variance and subtracts it from the next variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAdjacentTail_stationary (a b : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (p : ℝ × ℝ) :
    (fieldAdjacentTail a b L hb hs).T p = 0 :=
  fieldAffineFamily_stationary (Ioo (-a) b) isOpen_Ioo L _ hs p

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact concatenation and linear propagation identities for the finite
scalar field recursion. The exponents may include the zero root level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_append (P S : List (ℝ × ℝ≥0)) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ S) F = fieldScalarValue P (fieldScalarValue S F) := by
  exact List.foldr_append

lemma fieldScalarMean_append (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) :
    fieldScalarMean (P ++ S) F a =
      fieldScalarMean P (fieldScalarValue S F) (fieldScalarMean S F a) := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    simp only [List.cons_append, fieldScalarMean, fieldScalarValue_append, ih]

lemma fieldScalarMean_const_mul (P : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ) (c : ℝ) :
    fieldScalarMean P F (fun z => c * a z) = fun z => c * fieldScalarMean P F a z := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    simp only [fieldScalarMean, ih]
    funext z
    exact fieldSpinTransition_const_mul av.1 av.2 _ _ c z

lemma fieldScalarSquares_append (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ)
    (i : Fin (S.length + 1)) :
    fieldScalarSquares (P ++ S) F a (fieldAppendIndex P S i) =
      fieldScalarMean P (fieldScalarValue S F) (fieldScalarSquares S F a i) := by
  induction P with
  | nil =>
    have hi : fieldAppendIndex [] S i = i := by apply Fin.ext; simp [fieldAppendIndex]
    rw [hi]
    rfl
  | cons av P ih =>
    have hi : fieldAppendIndex (av :: P) S i = (fieldAppendIndex P S i).succ := by
      apply Fin.ext
      simp only [fieldAppendIndex, List.length_cons, Fin.val_succ]
      omega
    rw [hi]
    change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
      (fieldScalarSquares (P ++ S) F a (fieldAppendIndex P S i)) = _
    rw [fieldScalarValue_append, ih]
    rfl

lemma fieldConstantPrefix_test_regular {I : Set ℝ} (hI : IsOpen I)
    (F : FieldSmoothFamily I) (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ)) (t : ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) {B : ℝ} (haB : ∀ z, |a z| ≤ B) :
    Measurable (fieldScalarMean P (fun z => F.U (t, z)) a) ∧
      ∀ z, |fieldScalarMean P (fun z => F.U (t, z)) a z| ≤ B := by
  induction P with
  | nil => exact ⟨ha, haB⟩
  | cons av P ih =>
    let hp := fun bv hb => hP bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F P hp
    have hv := fieldConstantPrefix_value hI F P hp t
    have hm : Measurable (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.mU.comp (by fun_prop)
    have hg : HasLinearGrowth (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.growth t
    have ht := ih hp
    exact ⟨measurable_fieldSpinTransition av.1 av.2 hm ht.1,
      fieldSpinTransition_bound av.1 av.2 hm hg ht.2⟩

lemma fieldConstantPrefix_test_affine {I : Set ℝ} (hI : IsOpen I)
    (F : FieldSmoothFamily I) (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ)) (t : ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) {B : ℝ} (haB : ∀ z, |a z| ≤ B) (c k : ℝ) :
    fieldScalarMean P (fun z => F.U (t, z)) (fun z => c + k * a z) =
      fun z => c + k * fieldScalarMean P (fun z => F.U (t, z)) a z := by
  induction P with
  | nil => rfl
  | cons av P ih =>
    let hp := fun bv hb => hP bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F P hp
    have hv := fieldConstantPrefix_value hI F P hp t
    have hm : Measurable (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.mU.comp (by fun_prop)
    have hg : HasLinearGrowth (fieldScalarValue P (fun z => F.U (t, z))) := by
      rw [← hv]
      exact G.growth t
    have hr := fieldConstantPrefix_test_regular hI F P hp t ha haB
    change fieldSpinTransition av.1 av.2 _
      (fieldScalarMean P (fun z => F.U (t, z)) (fun z => c + k * a z)) = _
    rw [ih hp]
    funext z
    rw [fieldSpinTransition_add av.1 av.2 hm hg measurable_const (hr.1.const_mul k)
      (fun _ => le_rfl) (fun u => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hr.2 u) (abs_nonneg k)),
      fieldSpinTransition_const av.1 av.2 hm hg,
      fieldSpinTransition_const_mul]
    rfl

lemma fieldScalarSquares_congr_list {P Q : List (ℝ × ℝ≥0)} (he : P = Q)
    (F a : ℝ → ℝ) (i : Fin (P.length + 1)) (j : Fin (Q.length + 1))
    (hij : i.val = j.val) : fieldScalarSquares P F a i = fieldScalarSquares Q F a j := by
  subst Q
  have hi : i = j := Fin.ext hij
  rw [hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTerminalGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal Ising identity gives the constant term at the last
covariance level of the backward derivative. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_tanh_generator_one (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h := Real.cosh_sq_sub_sinh_sq z
  field_simp [(Real.cosh_pos z).ne']
  nlinarith

lemma field_tanh_generator (ζ z : ℝ) :
    1 / (Real.cosh z) ^ 2 + ζ * (Real.tanh z) ^ 2 =
      1 + (ζ - 1) * (Real.tanh z) ^ 2 := by
  have h := field_tanh_generator_one z
  nlinarith

lemma fieldSpinTransition_terminal_generator (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    fieldSpinTransition ζ v (fun x => Real.log (Real.cosh x))
      (fun x => 1 / (Real.cosh x) ^ 2 + ζ * (Real.tanh x) ^ 2) z =
      1 + (ζ - 1) * fieldSpinTransition ζ v (fun x => Real.log (Real.cosh x))
        (fun x => (Real.tanh x) ^ 2) z := by
  have ht : Measurable (fun x : ℝ => (Real.tanh x) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hB : ∀ x : ℝ, |(ζ - 1) * (Real.tanh x) ^ 2| ≤ |ζ - 1| := by
    intro x
    rw [abs_mul, abs_pow]
    have hsq : |Real.tanh x| ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (field_abs_tanh_le_one x) 2
    exact (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)).trans_eq (mul_one _)
  have he : (fun x => 1 / (Real.cosh x) ^ 2 + ζ * (Real.tanh x) ^ 2) =
      (fun x => (1 : ℝ) + (ζ - 1) * (Real.tanh x) ^ 2) := by
    funext x
    exact field_tanh_generator ζ x
  have hm : Measurable (fun x : ℝ => (ζ - 1) * (Real.tanh x) ^ 2) :=
    ht.const_mul (ζ - 1)
  rw [he, fieldSpinTransition_add (A := 1) ζ v measurable_logCosh logCosh_linearGrowth
    measurable_const hm (fun _ => by norm_num) hB,
    fieldSpinTransition_const ζ v measurable_logCosh logCosh_linearGrowth,
    fieldSpinTransition_const_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTerminalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final covariance coordinate has the same mixed monotonicity;
its backward derivative has the additional constant one half. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldTerminalFamily_value_eq_operator (a ζ t : ℝ) :
    (fun z => (fieldTerminalFamily a ζ).U (t, z)) =
      gaussianOperator ζ (Real.toNNReal (a + t)) (fun y => Real.log (Real.cosh y)) := by
  funext z
  change gaussianTransform (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) z = _
  rw [one_mul, field_gaussianTransform_eq_operator]

theorem fieldTerminalFamily_tangent (a ζ t z : ℝ) :
    (fieldTerminalFamily a ζ).T (t, z) = (1 : ℝ) / 2 - (1 - ζ) / 2 *
      gaussianTiltAverage (a + t) ζ (fun y => Real.log (Real.cosh y))
        (fun y => (Real.tanh y) ^ 2) z := by
  have hm : Measurable (fun y : ℝ => 1 / (Real.cosh y) ^ 2 + ζ * (Real.tanh y) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hx : Measurable (fun y : ℝ => (Real.tanh y) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hgen := fieldSpinTransition_terminal_generator ζ (Real.toNNReal (a + t)) z
  rw [← field_gaussianTiltAverage_eq_transition (a + t) ζ measurable_logCosh hm,
    ← field_gaussianTiltAverage_eq_transition (a + t) ζ measurable_logCosh hx] at hgen
  change gaussianTiltAverage (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) (fun _ => 0) z +
      (1 : ℝ) / 2 * gaussianTiltAverage (a + 1 * t) ζ
        (fun y => Real.log (Real.cosh y))
        (fun y => 1 / (Real.cosh y) ^ 2 + ζ * (Real.tanh y) ^ 2) z = _
  rw [one_mul, field_gaussianTiltAverage_const _ _ measurable_logCosh logCosh_linearGrowth,
    hgen]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCoordinateDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact single-height derivatives of the finite Gaussian field value.
An interior height changes its two adjacent covariance increments with
opposite signs. The final height includes the diagonal subtraction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldFixedAffine_increments (S : List (ℝ × ℝ≥0)) (t : ℝ) :
    fieldAffineIncrements (fieldFixedAffine S) t = S := by
  simp only [fieldAffineIncrements, fieldFixedAffine, List.map_map, Function.comp_def]
  have he : (fun av : ℝ × ℝ≥0 =>
      (((⟨av.2, 0, av.1⟩ : FieldAffineStep).exponent),
        Real.toNNReal ((⟨av.2, 0, av.1⟩ : FieldAffineStep).base +
          (⟨av.2, 0, av.1⟩ : FieldAffineStep).slope * t))) = id := by
    funext av
    simp
  rw [he, List.map_id]

private lemma adjacent_value (a b ζ η : ℝ) (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) =
    fieldScalarValue ((ζ, Real.toNNReal (a + t)) ::
      (η, Real.toNNReal (b - t)) :: S) (fun z => Real.log (Real.cosh z)) := by
  change gaussianTransform (a + 1 * t) ζ
    (fun y => gaussianTransform (b + -1 * t) η
      (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
        (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) y) = _
  rw [one_mul, neg_one_mul, ← sub_eq_add_neg, field_gaussianTransform_eq_operator]
  have he : (fun y => gaussianTransform (b - t) η
      (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
        (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) y) =
      gaussianOperator η (Real.toNNReal (b - t))
        (fieldScalarValue S (fun z => Real.log (Real.cosh z))) := by
    rw [field_gaussianTransform_eq_operator]
    rw [show (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) =
      (fun z => fieldAffineValue (fieldFixedAffine S) (t, z)) from
      congrArg (fun f => fun z => f (t, z))
        (fieldAffineFamily_value _ _ _ _),
      fieldAffineValue_scalar, fieldFixedAffine_increments]
  rw [he]
  rfl

private lemma adjacent_inner_mean (a b η : ℝ) (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldAdjacentInner a b η (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).X (t, z)) =
    fieldScalarMean ((η, Real.toNNReal (b - t)) :: S)
      (fun z => Real.log (Real.cosh z)) Real.tanh := by
  let av : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: fieldFixedAffine S, ∀ q ∈ Ioo (-a) b,
      0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.2]
    · rw [fieldFixedAffine_slope S v hv, zero_mul, add_zero]
      exact fieldFixedAffine_base S hS v hv
  have h := fieldAffineFamily_mean (Ioo (-a) b) isOpen_Ioo
    (av :: fieldFixedAffine S) hv t
  change (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo
    (av :: fieldFixedAffine S) hv).X (t, z)) = _
  rw [h]
  simp only [fieldAffineIncrements, List.map_cons]
  rw [← fieldAffineIncrements, fieldFixedAffine_increments]
  simp only [av, neg_one_mul, ← sub_eq_add_neg]

/-- The manuscript's finite interior-height gradient before the fixed
normalizing diagonal term. The derivative is minus half the cell width
multiplied by its actual conditional squared spin mean. -/
theorem hasDerivAt_fieldAdjacentValue
    (P S : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ))
    (a b ζ η t z : ℝ) (ht : t ∈ Ioo (-a) b) :
    HasDerivAt (fun q => fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
      (fun y => Real.log (Real.cosh y)) z)
      (-(η - ζ) / 2 * fieldScalarSquares (fieldAdjacentIncrements P S a b ζ η t)
        (fun y => Real.log (Real.cosh y)) Real.tanh
        (fieldAdjacentLevel P S a b ζ η t) z) t := by
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S hS
  let hs := fieldFixedAffine_slope S
  let F := fieldAdjacentTail a b L hb hs
  let G := fieldAdjacentInner a b η L hb hs
  let H := fieldAdjacentFamily a b ζ η L hb hs
  let K := fieldConstantPrefix isOpen_Ioo H P hP
  have hval (q : ℝ) : (fun y => K.U (q, y)) =
      fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
        (fun y => Real.log (Real.cosh y)) := by
    rw [show (fun y => K.U (q, y)) =
      fieldScalarValue P (fun y => H.U (q, y)) from
        fieldConstantPrefix_value isOpen_Ioo H P hP q,
      adjacent_value a b ζ η S hS q]
    exact (fieldScalarValue_append P _ _).symm
  have htan : (fun y => H.T (t, y)) = fun y =>
      -(η - ζ) / 2 * gaussianTiltAverage (a + t) ζ
        (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) y := by
    funext y
    exact F.adjacent_tangent isOpen_Ioo a b ζ η
      (fun q hq => by linarith [hq.1]) (fun q hq => by linarith [hq.2])
      (p := (t, y)) ht (fun x => fieldAdjacentTail_stationary a b L hb hs (t, x))
  have hsquare : gaussianTiltAverage (a + t) ζ
      (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) =
      fieldScalarSquares ((ζ, Real.toNNReal (a + t)) ::
        (η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh 1 := by
    have hm : Measurable (fun x => (G.X (t, x)) ^ 2) :=
      (G.mX.comp (by fun_prop)).pow_const 2
    have hmG : Measurable (fun x => G.U (t, x)) := G.mU.comp (by fun_prop)
    have htrans : gaussianTiltAverage (a + t) ζ
        (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) =
        fieldSpinTransition ζ (Real.toNNReal (a + t))
          (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) := by
      exact field_gaussianTiltAverage_eq_transition _ _ hmG hm
    rw [htrans]
    have hG : (fun x => G.U (t, x)) = fieldScalarValue
        ((η, Real.toNNReal (b - t)) :: S) (fun y => Real.log (Real.cosh y)) := by
      change gaussianTransform (b + -1 * t) η
        (fun x => F.U (t, x)) = _
      rw [neg_one_mul, ← sub_eq_add_neg, field_gaussianTransform_eq_operator]
      congr 1
      rw [show (fun x => F.U (t, x)) = (fun x => fieldAffineValue L (t, x)) from
        congrArg (fun f => fun x => f (t, x)) (fieldAffineFamily_value _ _ _ _),
        fieldAffineValue_scalar, fieldFixedAffine_increments]
      rfl
    rw [hG]
    have hGX : (fun x => G.X (t, x)) = fieldScalarMean
        ((η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh := adjacent_inner_mean a b η S hS t
    have hpow : (fun x => (G.X (t, x)) ^ 2) = fun x => (fieldScalarMean
        ((η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh x) ^ 2 := by
      funext x
      rw [congrFun hGX x]
    rw [hpow]
    rfl
  have hd := K.parameter_derivative t z ht
  have hfun : (fun q => K.U (q, z)) = fun q =>
      fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
        (fun y => Real.log (Real.cosh y)) z := by
    funext q
    exact congrFun (hval q) z
  rw [hfun] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [show K.T (t, z) = fieldScalarMean P (fun y => H.U (t, y))
      (fun y => H.T (t, y)) z from
      congrFun (fieldConstantPrefix_tangent isOpen_Ioo H P hP t) z,
    htan, fieldScalarMean_const_mul, hsquare, adjacent_value a b ζ η S hS t]
  simp only [fieldAdjacentLevel, fieldAdjacentIncrements]
  rw [fieldScalarSquares_append]

theorem hasDerivAt_fieldTerminalValue
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < (av.2 : ℝ))
    (a ζ d t z : ℝ) (ht : t ∈ Ioi (-a)) :
    HasDerivAt (fun q => fieldScalarValue (fieldTerminalIncrements P a ζ q)
      (fun y => Real.log (Real.cosh y)) z - (d + q) / 2)
      (-(1 - ζ) / 2 * fieldScalarSquares (fieldTerminalIncrements P a ζ t)
        (fun y => Real.log (Real.cosh y)) Real.tanh (fieldTerminalLevel P a ζ t) z) t := by
  let H := fieldTerminalFamily a ζ
  let K := fieldConstantPrefix isOpen_Ioi H P hP
  let A : ℝ → ℝ := fun y => gaussianTiltAverage (a + t) ζ
    (fun x => Real.log (Real.cosh x)) (fun x => (Real.tanh x) ^ 2) y
  have hm : Measurable (fun x : ℝ => (Real.tanh x) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hA : Measurable A :=
    measurable_gaussianTiltAverage_param (measurable_logCosh.comp measurable_snd)
      (hm.comp measurable_snd) measurable_const measurable_id ζ
  have hAb : ∀ y, |A y| ≤ 1 := by
    intro y
    apply field_gaussianTiltAverage_bound _ _ measurable_logCosh logCosh_linearGrowth hm
    intro x
    rw [abs_pow]
    nlinarith [field_abs_tanh_le_one x, abs_nonneg (Real.tanh x)]
  have hval (q : ℝ) : (fun y => K.U (q, y)) =
      fieldScalarValue (fieldTerminalIncrements P a ζ q)
        (fun y => Real.log (Real.cosh y)) := by
    rw [show (fun y => K.U (q, y)) =
      fieldScalarValue P (fun y => H.U (q, y)) from
        fieldConstantPrefix_value isOpen_Ioi H P hP q,
      fieldTerminalFamily_value_eq_operator]
    change fieldScalarValue P (fieldScalarValue [(ζ, Real.toNNReal (a + q))]
      (fun y => Real.log (Real.cosh y))) = _
    exact (fieldScalarValue_append P [(ζ, Real.toNNReal (a + q))]
      (fun y => Real.log (Real.cosh y))).symm
  have htangent : (fun y => H.T (t, y)) = fun y => 1 / 2 + (-(1 - ζ) / 2) * A y := by
    funext y
    rw [fieldTerminalFamily_tangent]
    dsimp only [A]
    ring
  have hsquare : A = fieldScalarSquares [(ζ, Real.toNNReal (a + t))]
      (fun y => Real.log (Real.cosh y)) Real.tanh 1 := by
    dsimp only [A]
    rw [field_gaussianTiltAverage_eq_transition _ _ measurable_logCosh hm]
    rfl
  have hd := (K.parameter_derivative t z ht).sub
    (((hasDerivAt_const t d).add (hasDerivAt_id t)).div_const 2)
  change HasDerivAt (fun q => K.U (q, z) - (d + q) / 2)
    (K.T (t, z) - (0 + 1) / 2) t at hd
  have hfun : (fun q => K.U (q, z) - (d + q) / 2) = fun q =>
      fieldScalarValue (fieldTerminalIncrements P a ζ q)
        (fun y => Real.log (Real.cosh y)) z - (d + q) / 2 := by
    funext q
    rw [congrFun (hval q) z]
  rw [hfun] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [show K.T (t, z) = fieldScalarMean P (fun y => H.U (t, y))
      (fun y => H.T (t, y)) z from
      congrFun (fieldConstantPrefix_tangent isOpen_Ioi H P hP t) z,
    htangent, fieldConstantPrefix_test_affine isOpen_Ioi H P hP t hA hAb,
    hsquare, fieldTerminalFamily_value_eq_operator]
  simp only [fieldTerminalLevel, fieldTerminalIncrements]
  rw [fieldScalarSquares_append]
  change _ = (1 / 2 + -(1 - ζ) / 2 * _) - (0 + 1) / 2
  simp only [fieldScalarValue, List.foldr_cons, List.foldr_nil]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLevelPath
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded monotone representative on the field partition. Endpoint
values are immaterial to integration; the representative is defined globally. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma fieldLevelIndex_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelIndex h s = i := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _hj
    by_cases hj : h.cut j.castSucc ≤ s
    · simp only [hj, ite_true, if_true]
      by_contra hji
      have hij : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        have : i < j := lt_of_not_ge hji
        exact this
      have hc := h.ordered_cut.monotone hij
      linarith [hs.2]
    · simp only [hj, ite_false, if_false]
      exact bot_le
  · have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i)
    simpa only [fieldLevelIndex, hs.1.le, ite_true, if_true] using hi

lemma fieldLevelPath_on_cell (h : FieldStep) (q : Fin (h.depth + 1) → ℝ)
    (hq : Monotone q) (hunit : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) {s : ℝ}
    (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldLevelPath h q hq hunit s = q i := by
  change q (fieldLevelIndex h s) = q i
  rw [fieldLevelIndex_on_cell h i hs]

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

lemma fieldAllIncrements_strict (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ fieldAllIncrements h, 0 < (av.2 : ℝ) := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hstrict i

private lemma list_split_two {α : Type*} (L : List α) (i : ℕ)
    (hi : i + 1 < L.length) :
    L = L.take i ++ L[i] :: L[i + 1] :: L.drop (i + 2) := by
  rw [← List.drop_eq_getElem_cons (show i + 1 < L.length from hi)]
  rw [← List.drop_eq_getElem_cons (show i < L.length by omega)]
  exact (List.take_append_drop i L).symm

private lemma interior_list_zero (h : FieldStep) (i : Fin h.depth) :
    fieldAdjacentIncrements ((fieldAllIncrements h).take i.val)
      ((fieldAllIncrements h).drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 0 =
      fieldAllIncrements h := by
  let L := fieldAllIncrements h
  have hlen : L.length = h.depth + 1 := fieldAllIncrements_length h
  have hget (j : Fin (h.depth + 1)) : L[j.val] =
      ((fieldIncrement h j).1,
        NNReal.mk (fieldIncrement h j).2 (fieldIncrement_nonneg h j)) := by
    exact List.getElem_ofFn _
  unfold fieldAdjacentIncrements
  simp only [add_zero, sub_zero]
  have hcast : i.castSucc.val = i.val := rfl
  have hsucc : i.succ.val = i.val + 1 := rfl
  rw [show (Real.toNNReal (fieldIncrement h i.castSucc).2) =
      NNReal.mk (fieldIncrement h i.castSucc).2 (fieldIncrement_nonneg h i.castSucc) by
        change Real.toNNReal (↑(NNReal.mk (fieldIncrement h i.castSucc).2
          (fieldIncrement_nonneg h i.castSucc))) = _
        exact Real.toNNReal_coe,
    show (Real.toNNReal (fieldIncrement h i.succ).2) =
      NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ) by
        change Real.toNNReal (↑(NNReal.mk (fieldIncrement h i.succ).2
          (fieldIncrement_nonneg h i.succ))) = _
        exact Real.toNNReal_coe]
  rw [← hget i.castSucc, ← hget i.succ]
  exact (list_split_two L i.val (by rw [hlen]; omega)).symm

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

lemma hasDerivAt_fieldInteriorChart (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (z : ℝ) :
    HasDerivAt (fun t => fieldInteriorChart h i t z)
      (-((fieldIncrement h i.succ).1 - (fieldIncrement h i.castSucc).1) / 2 *
        fieldScalarSquares (fieldAllIncrements h) (fun y => Real.log (Real.cosh y))
          Real.tanh ⟨i.val + 1, by simp⟩ z) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take i.val, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have hS : ∀ av ∈ L.drop (i.val + 2), 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_drop hav)
  have ht : (0 : ℝ) ∈ Ioo (-(fieldIncrement h i.castSucc).2)
      (fieldIncrement h i.succ).2 := ⟨by linarith [hstrict i.castSucc], hstrict i.succ⟩
  have hd := (hasDerivAt_fieldAdjacentValue (L.take i.val) (L.drop (i.val + 2)) hP hS
    (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
    (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 0 z ht).sub_const
      (h.height (Fin.last h.depth) / 2)
  change HasDerivAt _ _ 0
  refine hd.congr_deriv (Eq.symm ?_)
  · apply congrArg (fun r : ℝ => -((fieldIncrement h i.succ).1 -
      (fieldIncrement h i.castSucc).1) / 2 * r)
    apply congrFun
    apply fieldScalarSquares_congr_list (interior_list_zero h i).symm
    simp only [fieldAdjacentLevel, fieldAppendIndex, List.length_take,
      fieldAllIncrements_length, L, List.length_cons, Fin.val_one]
    omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldZeroIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inserting a zero covariance increment preserves the scalar Ising
value and spin mean. Its adjacent overlap levels are the same. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F : ℝ → ℝ) :
    fieldScalarValue (P ++ (a, 0) :: S) F = fieldScalarValue (P ++ S) F := by
  rw [fieldScalarValue_append, fieldScalarValue_append]
  change fieldScalarValue P (gaussianOperator a 0 (fieldScalarValue S F)) = _
  rw [gaussianOperator_zero_variance]

lemma fieldScalarMean_insert_zero (P S : List (ℝ × ℝ≥0)) (a : ℝ) (F b : ℝ → ℝ) :
    fieldScalarMean (P ++ (a, 0) :: S) F b = fieldScalarMean (P ++ S) F b := by
  rw [fieldScalarMean_append, fieldScalarMean_append]
  change fieldScalarMean P (gaussianOperator a 0 (fieldScalarValue S F))
    (fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b)) = _
  rw [gaussianOperator_zero_variance]
  have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
      fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
  rw [hs]

lemma fieldScalarSquareAt_eq (L : List (ℝ × ℝ≥0)) (F b : ℝ → ℝ)
    (i : Fin (L.length + 1)) :
    fieldScalarSquareAt L F b i.val = fieldScalarSquares L F b i := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
        (fieldScalarSquareAt L F b j.val) = _
      rw [ih]
      rfl

lemma fieldScalarSquareAt_insert_zero (P S : List (ℝ × ℝ≥0))
    (a : ℝ) (F b : ℝ → ℝ) (i : ℕ) :
    fieldScalarSquareAt (P ++ (a, 0) :: S) F b i =
      fieldScalarSquareAt (P ++ S) F b (if i ≤ P.length then i else i - 1) := by
  induction P generalizing i with
  | nil =>
    cases i with
    | zero =>
      simp only [List.nil_append, List.length_nil, le_refl, ite_true, if_true,
        fieldScalarSquareAt, fieldScalarMean]
      have hs : fieldSpinTransition a 0 (fieldScalarValue S F) (fieldScalarMean S F b) =
          fieldScalarMean S F b := funext (fieldSpinTransition_zero_variance _ _ _)
      rw [hs]
      cases S <;> rfl
    | succ i =>
      simp only [List.nil_append, List.length_nil,
        Nat.add_sub_cancel, fieldScalarSquareAt]
      exact funext (fieldSpinTransition_zero_variance _ _ _)
  | cons av P ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_le, ite_true, if_true, List.cons_append, fieldScalarSquareAt]
      have he := fieldScalarMean_insert_zero (av :: P) S a F b
      simpa only [List.cons_append] using congrArg (fun f : ℝ → ℝ => fun z => f z ^ 2) he
    | succ i =>
      have hv := fieldScalarValue_insert_zero P S a F
      simp only [List.cons_append, List.length_cons, Nat.succ_le_succ_iff]
      by_cases hi : i ≤ P.length
      · simp only [hi, ite_true, if_true, fieldScalarSquareAt]
        rw [hv, ih, ite_eq_left hi]
      · have hp : 0 < i := by omega
        simp only [hi, ite_false, if_false, fieldScalarSquareAt]
        have he : i + 1 - 1 = (i - 1) + 1 := by omega
        rw [he]
        change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ (a, 0) :: S) F)
          (fieldScalarSquareAt (P ++ (a, 0) :: S) F b i) =
          fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
            (fieldScalarSquareAt (P ++ S) F b (i - 1))
        rw [hv, ih, ite_eq_right hi]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineCut
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting one interval of a finite field without changing its height. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_ofFn_insertNth {α : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : α) (f : Fin n → α) :
    List.ofFn (Fin.insertNth i a f) =
      (List.ofFn f).take i.val ++ a :: (List.ofFn f).drop i.val := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hf : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
      rw [hf, Fin.insertNth_succ_cons]
      simp only [List.ofFn_cons, Fin.val_succ, List.take_succ_cons,
        List.drop_succ_cons, ih, List.cons_append]

lemma fieldInsertCut_last_height (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) =
      h.height (Fin.last h.depth) := by
  change fieldSplitHeight h i (Fin.last (h.depth + 1)) = _
  simp only [fieldSplitHeight, Fin.val_last]
  rw [dite_eq_right (show ¬h.depth + 1 ≤ i.val by omega)]
  rfl

lemma fieldInsertCut_cut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : j.val ≤ i.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_below (α := fun _ => ℝ) (show j < i.castSucc.succ by
    change j.val < i.val + 1; omega)]
  simp only [eq_rec_constant]
  rfl

lemma fieldInsertCut_cut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    (fieldInsertCut h i c hc₀ hc₁).cut i.castSucc.succ = c := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut i.castSucc.succ = c
  exact Fin.insertNth_apply_same _ _ _

lemma fieldInsertCut_cut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 3)) (hj : i.val + 1 < j.val) :
    (fieldInsertCut h i c hc₀ hc₁).cut j = h.cut ⟨j.val - 1, by omega⟩ := by
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = _
  rw [Fin.insertNth_apply_above (α := fun _ => ℝ) (show i.castSucc.succ < j by exact hj)]
  simp only [eq_rec_constant]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineIncrements
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A one-cut refinement inserts exactly one zero covariance increment. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut i.succ.castSucc = c
    simpa only [Fin.succ_castSucc] using fieldInsertCut_cut_at h i c hc₀ hc₁
  · change fieldSplitHeight h i i.succ -
      (if hz : i.succ.val = 0 then 0 else
        fieldSplitHeight h i ⟨i.succ.val - 1, by change i.val + 1 - 1 < h.depth + 2; omega⟩) = 0
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel]
    unfold fieldSplitHeight
    simp only [Fin.val_succ]
    rw [dite_eq_right (show ¬i.val + 1 ≤ i.val by omega),
      dite_eq_left (show i.val ≤ i.val by omega)]
    simp

lemma fieldIncrement_insertCut_below (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : j.val ≤ i.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.castSucc = fieldIncrement h j := by
  apply Prod.ext
  · exact fieldInsertCut_cut_below h i c hc₀ hc₁ _ hj
  · change fieldSplitHeight h i j.castSucc -
      (if hz : j.val = 0 then 0 else fieldSplitHeight h i ⟨j.val - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    have hp : fieldSplitHeight h i j.castSucc = h.height j := by
      unfold fieldSplitHeight
      exact dite_eq_left hj
    rw [hp]
    split_ifs with hz
    · rfl
    · have hp' : fieldSplitHeight h i ⟨j.val - 1, by omega⟩ =
          h.height ⟨j.val - 1, by omega⟩ := by
        unfold fieldSplitHeight
        exact dite_eq_left (show j.val - 1 ≤ i.val by omega)
      rw [hp']

lemma fieldIncrement_insertCut_above (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 1)) (hj : i.val < j.val) :
    fieldIncrement (fieldInsertCut h i c hc₀ hc₁) j.succ = fieldIncrement h j := by
  apply Prod.ext
  · change (fieldInsertCut h i c hc₀ hc₁).cut j.succ.castSucc = h.cut j.castSucc
    convert fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ.castSucc (by
      change i.val + 1 < j.val + 1; omega) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  · change fieldSplitHeight h i j.succ -
      (if hz : j.val + 1 = 0 then 0 else fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩) =
        h.height j - (if hz : j.val = 0 then 0 else h.height ⟨j.val - 1, by omega⟩)
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    have hp : fieldSplitHeight h i j.succ = h.height j := by
      unfold fieldSplitHeight
      rw [dite_eq_right (show ¬j.succ.val ≤ i.val by change ¬j.val + 1 ≤ i.val; omega)]
      rfl
    have hp' : fieldSplitHeight h i ⟨j.val + 1 - 1, by omega⟩ =
        h.height ⟨j.val - 1, by omega⟩ := by
      unfold fieldSplitHeight
      rw [dite_eq_right (by change ¬j.val + 1 - 1 ≤ i.val; omega)]
      rfl
    rw [hp, hp']

lemma fieldNNIncrement_eq_of_real {h k : FieldStep} {i : Fin (h.depth + 1)}
    {j : Fin (k.depth + 1)} (he : fieldIncrement h i = fieldIncrement k j) :
    fieldNNIncrement h i = fieldNNIncrement k j := by
  apply Prod.ext
  · exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldNNIncrement_insertCut_at (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ = (c, 0) := by
  have he := fieldIncrement_insertCut_at h i c hc₀ hc₁
  apply Prod.ext
  · change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).1 = c
    exact congrArg (fun p : ℝ × ℝ => p.1) he
  · apply Subtype.ext
    change (fieldIncrement (fieldInsertCut h i c hc₀ hc₁) i.succ).2 = 0
    exact congrArg (fun p : ℝ × ℝ => p.2) he

lemma fieldAllIncrements_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldAllIncrements (fieldInsertCut h i c hc₀ hc₁) =
      (fieldAllIncrements h).take (i.val + 1) ++
        (c, 0) :: (fieldAllIncrements h).drop (i.val + 1) := by
  let f : Fin (h.depth + 1) → ℝ × ℝ≥0 := fieldNNIncrement h
  let g : Fin (h.depth + 2) → ℝ × ℝ≥0 :=
    fieldNNIncrement (fieldInsertCut h i c hc₀ hc₁)
  have he : g = Fin.insertNth i.succ (c, 0) f := by
    apply (Fin.eq_insertNth_iff).mpr
    constructor
    · exact fieldNNIncrement_insertCut_at h i c hc₀ hc₁
    · funext j
      change g (i.succ.succAbove j) = f j
      by_cases hj : j.val ≤ i.val
      · have hs : i.succ.succAbove j = j.castSucc :=
          Fin.succAbove_of_castSucc_lt _ _ (by change j.val < i.val + 1; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_below h i c hc₀ hc₁ j hj)
      · have hs : i.succ.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc _ _ (by change i.val + 1 ≤ j.val; omega)
        rw [hs]
        exact fieldNNIncrement_eq_of_real (fieldIncrement_insertCut_above h i c hc₀ hc₁ j (by omega))
  change List.ofFn g = (List.ofFn f).take (i.val + 1) ++ (c, 0) :: (List.ofFn f).drop (i.val + 1)
  rw [he, field_ofFn_insertNth]
  rfl

lemma fieldValue_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (z : ℝ) :
    fieldValue (fieldInsertCut h i c hc₀ hc₁) z = fieldValue h z := by
  rw [← fieldAllIncrements_value, fieldAllIncrements_insertCut,
    fieldScalarValue_insert_zero, List.take_append_drop]
  change fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
    (fieldInsertCut h i c hc₀ hc₁).height (Fin.last (h.depth + 1)) / 2 = _
  rw [fieldInsertCut_last_height, fieldAllIncrements_value]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefineMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact magnetization levels under a one-cut field refinement. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSplitHeight_eq (h : FieldStep) (i : Fin (h.depth + 1))
    (j : Fin (h.depth + 2)) : fieldSplitHeight h i j = h.height (fieldSplitIndex i j) := by
  unfold fieldSplitHeight fieldSplitIndex
  split_ifs <;> rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRefinePaths
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height and physical magnetization paths survive a one-cut refinement. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldInsertCut_cell_subset (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ)
    (j : Fin (h.depth + 2)) :
    Ioo ((fieldInsertCut h i c hc₀ hc₁).cut j.castSucc)
        ((fieldInsertCut h i c hc₀ hc₁).cut j.succ) ⊆
      Ioo (h.cut (fieldSplitIndex i j).castSucc) (h.cut (fieldSplitIndex i j).succ) := by
  have hlo : h.cut (fieldSplitIndex i j).castSucc ≤
      (fieldInsertCut h i c hc₀ hc₁).cut j.castSucc := by
    by_cases hj : j.val ≤ i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.castSucc hj]
      simp only [fieldSplitIndex, hj, dite_true]
      rfl
    · by_cases he : j.val = i.val + 1
      · have hjc : j.castSucc = i.castSucc.succ := Fin.ext he
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₀.le using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, hj, dite_false, Fin.val_castSucc]
        omega
      · rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.castSucc (by
          change i.val + 1 < j.val; omega)]
        simp only [fieldSplitIndex, hj, dite_false]
        rfl
  have hhi : (fieldInsertCut h i c hc₀ hc₁).cut j.succ ≤
      h.cut (fieldSplitIndex i j).succ := by
    by_cases hj : j.val < i.val
    · rw [fieldInsertCut_cut_below h i c hc₀ hc₁ j.succ (by
        change j.val + 1 ≤ i.val; omega)]
      simp only [fieldSplitIndex, show j.val ≤ i.val from hj.le, dite_true]
      rfl
    · by_cases he : j.val = i.val
      · have hjc : j.succ = i.castSucc.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        rw [hjc, fieldInsertCut_cut_at]
        convert hc₁.le using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply Fin.ext
        simp only [fieldSplitIndex, show j.val ≤ i.val by omega, dite_true, Fin.val_succ]
        omega
      · have hgt : i.val < j.val := by omega
        rw [fieldInsertCut_cut_above h i c hc₀ hc₁ j.succ (by
          change i.val + 1 < j.val + 1; omega)]
        simp only [fieldSplitIndex, show ¬j.val ≤ i.val by omega, dite_false,
          Fin.val_succ, Nat.add_sub_cancel]
        apply le_of_eq
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
  intro s hs
  exact ⟨hlo.trans_lt hs.1, hs.2.trans_le hhi⟩

lemma fieldFunction_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldFunction (fieldInsertCut h i c hc₀ hc₁) =ᵐ[pathMeasure] fieldFunction h := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with s hs
  obtain ⟨j, hj⟩ := hs
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  change finiteStepFunction _ _ s = finiteStepFunction _ _ s
  rw [finiteStepFunction_on_cell (fieldInsertCut h i c hc₀ hc₁).ordered_cut _ hj,
    finiteStepFunction_on_cell h.ordered_cut _ hi]
  exact fieldSplitHeight_eq h i j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCommonRefinement
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite common refinements, built only by duplicating constant-height cells. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldCutSet_bounds (h : FieldStep) {s : ℝ} (hs : s ∈ fieldCutSet h) :
    s ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨i, rfl⟩ := (mem_fieldCutSet h s).mp hs
  constructor
  · rw [← h.first]; exact h.ordered_cut.monotone (Fin.zero_le i)
  · rw [← h.last]; exact h.ordered_cut.monotone (Fin.le_last i)

lemma fieldCutSet_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) :
    fieldCutSet (fieldInsertCut h i c hc₀ hc₁) = insert c (fieldCutSet h) := by
  classical
  have he := Fin.range_insertNth i.castSucc.succ c h.cut
  ext s
  simp only [mem_fieldCutSet, Finset.mem_insert]
  change (∃ j, Fin.insertNth (α := fun _ => ℝ) i.castSucc.succ c h.cut j = s) ↔
    s = c ∨ ∃ j, h.cut j = s
  simpa only [Set.insert, Set.mem_ofPred_eq, Set.mem_range] using Set.ext_iff.mp he s

lemma FieldRefines.value {h k : FieldStep} (hk : FieldRefines h k) (z : ℝ) :
    fieldValue k z = fieldValue h z := by
  induction hk with
  | refl => rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldValue_insertCut _ i c hc₀ hc₁ z).trans ih

lemma FieldRefines.field_ae {h k : FieldStep} (hk : FieldRefines h k) :
    fieldFunction k =ᵐ[pathMeasure] fieldFunction h := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih => exact (fieldFunction_insertCut_ae _ i c hc₀ hc₁).trans ih

lemma field_exists_refinement (h : FieldStep) (S : Finset ℝ)
    (hS : ∀ s ∈ S, s ∈ Icc (0 : ℝ) 1) :
    ∃ k, FieldRefines h k ∧ fieldCutSet k = fieldCutSet h ∪ S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨h, FieldRefines.refl h, by simp⟩
  | @insert c S hc ih =>
    obtain ⟨k, hk, hcuts⟩ := ih (fun s hs => hS s (Finset.mem_insert_of_mem hs))
    by_cases hck : c ∈ fieldCutSet k
    · refine ⟨k, hk, ?_⟩
      rw [hcuts] at hck ⊢
      ext s
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · intro hs; rcases hs with hs | hs
        · exact Or.inl hs
        · exact Or.inr (Or.inr hs)
      · intro hs; rcases hs with hs | rfl | hs
        · exact Or.inl hs
        · simpa only [Finset.mem_union] using hck
        · exact Or.inr hs
    · have hcb := hS c (Finset.mem_insert_self c S)
      have hc0 : 0 < c := by
        have hne : c ≠ 0 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨0, k.first.trans he.symm⟩
        exact lt_of_le_of_ne hcb.1 (Ne.symm hne)
      have hc1 : c < 1 := by
        have hne : c ≠ 1 := by
          intro he; apply hck
          apply (mem_fieldCutSet k c).mpr
          exact ⟨Fin.last (k.depth + 1), k.last.trans he.symm⟩
        exact lt_of_le_of_ne hcb.2 hne
      obtain ⟨i, hi₀, hi₁⟩ := finite_partition_cell k.cut
        (by simpa only [k.first] using hc0.le) (by simpa only [k.last] using hc1)
      have hi : k.cut i.castSucc < c := lt_of_le_of_ne hi₀ (by
        intro he; exact hck ((mem_fieldCutSet k c).mpr ⟨i.castSucc, he⟩))
      refine ⟨fieldInsertCut k i c hi hi₁, FieldRefines.insert hk i c hi hi₁, ?_⟩
      rw [fieldCutSet_insertCut, hcuts]
      ext s
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

lemma field_cutList_eq_of_set_eq {h k : FieldStep} (he : fieldCutSet h = fieldCutSet k) :
    List.ofFn h.cut = List.ofFn k.cut := by
  have hh : (List.ofFn h.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr h.ordered_cut)
  have hk : (List.ofFn k.cut).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (List.pairwise_ofFn.mpr k.ordered_cut)
  apply hh.eq_of_mem_iff hk
  intro s
  have hs := Finset.ext_iff.mp he s
  simpa only [mem_fieldCutSet, List.mem_ofFn] using hs

lemma field_common_refinement (h k : FieldStep) :
    ∃ h' k', FieldRefines h h' ∧ FieldRefines k k' ∧
      List.ofFn h'.cut = List.ofFn k'.cut := by
  obtain ⟨h', hh', hhcut⟩ := field_exists_refinement h (fieldCutSet k)
    (fun _ hs => fieldCutSet_bounds k hs)
  obtain ⟨k', hk', hkcut⟩ := field_exists_refinement k (fieldCutSet h)
    (fun _ hs => fieldCutSet_bounds h hs)
  refine ⟨h', k', hh', hk', field_cutList_eq_of_set_eq ?_⟩
  rw [hhcut, hkcut, Finset.union_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint finite-height derivative data for the scalar Ising recursion.
Only the covariance coordinates required by a finite subdivision occur. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma spatial_mean_derivative (h : Fin n → ℝ) (hh : h ∈ I) (z : ℝ) :
    HasDerivAt (fun y => F.X (h, y)) (F.XX (h, z)) z := by
  have hmap : HasDerivAt (fun y : ℝ => (h, y)) ((0 : Fin n → ℝ), (1 : ℝ)) z :=
    (hasDerivAt_const z h).prodMk (hasDerivAt_id z)
  have hd := (F.derivativeX (h, z) hh).comp_hasDerivAt z hmap
  simpa [Function.comp_def] using hd

end FieldFiniteFamily

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closure of the finite scalar Ising recursion under joint height and
spatial derivatives. The Hessian symmetry is part of the constructed data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem fieldFiniteFamily_value {n : ℕ} (I : Set (Fin n → ℝ)) (hI : IsOpen I)
    (V R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (L : List (FieldFiniteStep n))
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < fieldFiniteVariance av.base av.slope t ∧
      fieldFiniteVariance av.base av.slope t ≤ V)
    (hc : ∀ av ∈ L, ∀ t ∈ I, ∀ i, |fieldFiniteSlope av.base av.slope t i| ≤ R)
    (hd : ∀ av ∈ L, ∀ t ∈ I, ∀ i j, |fieldFiniteCurvature av.base av.slope t i j| ≤ D) :
    (fieldFiniteFamily I hI V R D hR hD L hL hc hd).U = fieldFiniteValue L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    funext p
    simp only [fieldFiniteFamily, FieldFiniteFamily.transform, FieldFiniteFamily.value,
      fieldFiniteValue]
    rw [ih]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every strictly positive finite covariance list admits the joint
height derivative construction on a neighborhood of its parameter vector. -/

noncomputable section
open Set IsingPerceptron
open scoped Topology BigOperators

namespace InvariantIsing

lemma fieldFinite_coefficient_bound {n : ℕ} (L : List (FieldFiniteStep n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ av ∈ L, ∀ i, |av.slope i| ≤ B := by
  classical
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons av L ih =>
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨max B (∑ i, |av.slope i|), hB.trans (le_max_left _ _), ?_⟩
    intro bv hv i
    rcases List.mem_cons.mp hv with heq | hv
    · subst bv
      exact (Finset.single_le_sum (fun j _ => abs_nonneg (av.slope j)) (Finset.mem_univ i)).trans
        (le_max_right _ _)
    · exact (hb bv hv i).trans (le_max_left _ _)

lemma fieldFinite_slope_bound {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    {m B : ℝ} (hm : 0 < m) (hs : m ≤ fieldFiniteVariance a v h)
    (hb : ∀ i, |v i| ≤ B) (i : Fin n) :
    |fieldFiniteSlope a v h i| ≤ B / (2 * Real.sqrt m) :=
  (abs_div_two_sqrt_le hm hs (v i)).trans (div_le_div_of_nonneg_right (hb i) (by positivity))

lemma fieldFinite_curvature_bound {n : ℕ} (a : ℝ) (v h : Fin n → ℝ)
    {m B : ℝ} (hm : 0 < m) (hB : 0 ≤ B) (hs : m ≤ fieldFiniteVariance a v h)
    (hb : ∀ i, |v i| ≤ B) (i j : Fin n) :
    |fieldFiniteCurvature a v h i j| ≤ (B / 2) * m⁻¹ * (B / (2 * Real.sqrt m)) := by
  have hS := hm.trans_le hs
  have hj := fieldFinite_slope_bound a v h hm hs hb j
  unfold fieldFiniteCurvature
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_inv, abs_of_pos hS]
  gcongr
  exact hb i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate and line derivatives extracted from the actual joint
finite-height derivative data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma coordinate_derivative (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I) (i : Fin n) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), z))
      (F.P i (r, z)) 0 := by
  classical
  have hv : HasDerivAt (fun t : ℝ => Function.update r i (r i + t)) (Pi.single i 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (r i)
    · simpa [Function.update_of_ne hji, Pi.single_eq_of_ne hji] using
        hasDerivAt_const (0 : ℝ) (r j)
  have hp := hv.prodMk (hasDerivAt_const (0 : ℝ) z)
  have hF : HasFDerivAt F.U (fieldFiniteLinear (fun k => F.P k (r, z)) (F.X (r, z)))
      (Function.update r i (r i + 0), z) := by simpa using F.derivative (r, z) hr
  have hd := hF.comp_hasDerivAt 0 hp
  simpa [fieldFiniteLinear_apply, Function.comp_def, Pi.single_apply] using hd

end FieldFiniteFamily
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the scalar Gaussian step at zero variance. The payoff
has a uniform linear envelope; the physical-spin observable is bounded.
This is the dominated-convergence input for closed height cones. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_shift_linear_envelope {E : Type*} [TopologicalSpace E]
    {U : E → ℝ → ℝ} {s x : E → ℝ} (hs : Continuous s) (hx : Continuous x)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (t₀ : E) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ᶠ t in 𝓝 t₀, ∀ u, |U t (x t + Real.sqrt (s t) * u)| ≤ A + B * ‖u‖ := by
  let X := |x t₀| + 1
  let R := |Real.sqrt (s t₀)| + 1
  have hX0 : |x t₀| < X := by dsimp only [X]; linarith
  have hR0 : |Real.sqrt (s t₀)| < R := by dsimp only [R]; linarith
  have hxB : ∀ᶠ t in 𝓝 t₀, |x t| < X :=
    (isOpen_lt hx.abs continuous_const).mem_nhds hX0
  have hsB : ∀ᶠ t in 𝓝 t₀, |Real.sqrt (s t)| < R :=
    (isOpen_lt (Real.continuous_sqrt.comp hs).abs continuous_const).mem_nhds
      hR0
  refine ⟨C + L * X, L * R, by dsimp only [X] <;> positivity,
    by dsimp only [R] <;> positivity, ?_⟩
  filter_upwards [hxB, hsB] with t ht hs'
  intro u
  have harg : |x t + Real.sqrt (s t) * u| ≤ X + R * |u| :=
    (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
  calc
    _ ≤ C + L * (X + R * |u|) := (hB t _).trans (by gcongr)
    _ = C + L * X + L * R * ‖u‖ := by rw [Real.norm_eq_abs]; ring

lemma continuous_field_gaussian_integral {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2)) (hs : Continuous s)
    (hx : Continuous x) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) :
    Continuous (fun t => ∫ u, U t (x t + Real.sqrt (s t) * u) ∂gaussianReal 0 1) := by
  let A := fun t u => U t (x t + Real.sqrt (s t) * u)
  have hA : Continuous (fun p : E × ℝ => A p.1 p.2) :=
    hU.comp (continuous_fst.prodMk ((hx.comp continuous_fst).add
      (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd)))
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨D, B, hD, hBB, hb⟩ := field_shift_linear_envelope hs hx hC hL hB t₀
  apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => D + B * ‖u‖)
  · exact Eventually.of_forall (fun t =>
      (hA.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using ht u)
  · exact gaussian_linearGrowth_integrable (by fun_prop)
      ⟨D, B, hD, hBB, fun u => by rw [abs_of_nonneg (by positivity)]⟩ _ _
  · exact ae_of_all _ (fun u =>
      (hA.comp (continuous_id.prodMk continuous_const)).continuousAt)

lemma continuous_field_gaussian_weighted {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (_hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u)) *
      A t (x t + Real.sqrt (s t) * u) ∂gaussianReal 0 1) := by
  let q := fun p : E × ℝ => (p.1, x p.1 + Real.sqrt (s p.1) * p.2)
  have hq : Continuous q := continuous_fst.prodMk ((hx.comp continuous_fst).add
    (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd))
  have hF : Continuous (fun p : E × ℝ =>
      Real.exp (ζ * U p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) *
        A p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) :=
    (Real.continuous_exp.comp ((hU.comp hq).const_mul ζ)).mul (hA.comp hq)
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨D, B, _hD, _hBB, hb⟩ := field_shift_linear_envelope hs hx hC hL hB t₀
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (|ζ| * D) * Real.exp ((|ζ| * B) * ‖u‖) * M)
  · exact Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have harg : ζ * U t (x t + Real.sqrt (s t) * u) ≤
        |ζ| * D + (|ζ| * B) * ‖u‖ := by
      calc
        _ ≤ |ζ * U t (x t + Real.sqrt (s t) * u)| := le_abs_self _
        _ = |ζ| * |U t (x t + Real.sqrt (s t) * u)| := abs_mul _ _
        _ ≤ |ζ| * (D + B * ‖u‖) := mul_le_mul_of_nonneg_left (ht u) (abs_nonneg _)
        _ = _ := by ring
    rw [← Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr harg) (haB t _)
      (abs_nonneg _) (Real.exp_pos _).le
  · exact (((gaussianReal_exponentialNormMoments 0 1) (|ζ| * B)).const_mul
      (Real.exp (|ζ| * D))).mul_const M
  · exact ae_of_all _ (fun u =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt)

lemma continuous_field_gaussian_transform {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2)) (hs : Continuous s)
    (hx : Continuous x) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (ζ : ℝ) :
    Continuous (fun t => gaussianTransform (s t) ζ (U t) (x t)) := by
  by_cases hζ : ζ = 0
  · subst ζ
    simpa only [gaussianTransform, ite_true, if_true] using
      continuous_field_gaussian_integral hU hs hx hC hL hB
  · have hZ := continuous_field_gaussian_weighted (A := fun _ _ => 1) hU
      (show Continuous (fun _ : E × ℝ => (1 : ℝ)) from continuous_const)
      hs hx hC hL zero_le_one hB (fun _ _ => by norm_num) ζ
    simp only [mul_one] at hZ
    have hp (t : E) : 0 < ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u))
        ∂gaussianReal 0 1 := by
      apply IsingPerceptron.integral_exp_pos
      have hm : Measurable (U t) :=
        (hU.comp (continuous_const.prodMk continuous_id)).measurable
      have hg : HasLinearGrowth (U t) :=
        ⟨C, L, hC, hL, by simpa only [Real.norm_eq_abs] using hB t⟩
      exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
        (hm.comp (by fun_prop)) ((hg.add_left (x t)).scale_argument (Real.sqrt (s t))) ζ
    simpa only [gaussianTransform, hζ, ite_false, if_false] using
      (hZ.log (fun t => (hp t).ne')).div_const ζ

lemma continuous_field_gaussian_tilt_average {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => gaussianTiltAverage (s t) ζ (U t) (A t) (x t)) := by
  have hn := continuous_field_gaussian_weighted hU hA hs hx hC hL hM hB haB ζ
  have hd := continuous_field_gaussian_weighted (A := fun _ _ => 1) hU
    (show Continuous (fun _ : E × ℝ => (1 : ℝ)) from continuous_const)
    hs hx hC hL zero_le_one hB (fun _ _ => by norm_num) ζ
  simp only [mul_one] at hd
  have hp (t : E) : 0 < ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u))
      ∂gaussianReal 0 1 := by
    apply IsingPerceptron.integral_exp_pos
    have hm : Measurable (U t) :=
      (hU.comp (continuous_const.prodMk continuous_id)).measurable
    have hg : HasLinearGrowth (U t) :=
      ⟨C, L, hC, hL, by simpa only [Real.norm_eq_abs] using hB t⟩
    exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
      (hm.comp (by fun_prop)) ((hg.add_left (x t)).scale_argument (Real.sqrt (s t))) ζ
  simp only [gaussianTiltAverage_eq_div]
  convert hn.div hd (fun t => (hp t).ne') using 1
  all_goals try with_reducible_and_instances rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite covariance charts with literal updates
of a field height. The formula is defined without choosing proofs of the
order constraints; whenever the updated heights are admissible it is the
original `fieldValue` of that field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

private lemma list_set_two {α : Type*} (L : List α) (i : ℕ)
    (A B : α) (hi : i + 1 < L.length) :
    (L.set i A).set (i + 1) B = L.take i ++ A :: B :: L.drop (i + 2) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      cases L with
      | nil => simp at hi
      | cons y L => rfl
    | succ i =>
      have hh : i + 1 < L.length := by simp only [List.length_cons] at hi; omega
      simpa only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append, Nat.succ_eq_add_one, Nat.add_assoc] using
        congrArg (List.cons x) (ih i hh)

lemma gaussianOperator_toNNReal (ζ v : ℝ) (F : ℝ → ℝ) :
    gaussianOperator ζ (Real.toNNReal v) F = gaussianOperator ζ v F := by
  rw [gaussianOperator_eq_transform ζ v F]
  exact (field_gaussianTransform_eq_operator v ζ F).symm

lemma updated_increments_interior (h : FieldStep) (i : Fin h.depth) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
    fieldAdjacentIncrements ((fieldAllIncrements h).take i.val)
      ((fieldAllIncrements h).drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h i.castSucc).1,
    Real.toNNReal ((fieldIncrement h i.castSucc).2 + t))
  let B : ℝ × ℝ≥0 := ((fieldIncrement h i.succ).1,
    Real.toNNReal ((fieldIncrement h i.succ).2 - t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
      (L.set i.val A).set (i.val + 1) B := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_castSucc, fieldHeightIncrement_eq]
      by_cases he : j = i.val
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · by_cases hs : j = i.val + 1
        · subst j
          simp [B, fieldIncrement, sub_eq_add_neg]
          constructor <;> rfl
        · have he' : i.val ≠ j := Ne.symm he
          have hs' : i.val + 1 ≠ j := Ne.symm hs
          simp only [he, hs, he', hs', ite_false, if_false, add_zero]
          change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
            Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
          rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
            NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
              List.getElem_ofFn _]
          apply Prod.ext
          · rfl
          · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, list_set_two L i.val A B (by simp only [L, fieldAllIncrements_length]; omega)]
  rfl

lemma fieldHeightCoordinateValue_interior (h : FieldStep) (i : Fin h.depth) (t z : ℝ) :
    fieldHeightCoordinateValue h i.castSucc t z = fieldInteriorChart h i t z := by
  dsimp only [fieldHeightCoordinateValue, fieldInteriorChart]
  rw [updated_increments_interior]
  have hn : Fin.last h.depth ≠ i.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  rw [Function.update_of_ne hn]

lemma updated_increments_final (h : FieldStep) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h (Fin.last h.depth)).1,
    Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
      L.set h.depth A := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      have hn : j ≠ h.depth + 1 := by omega
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_last, hn, ite_false, if_false, fieldHeightIncrement_eq]
      by_cases he : j = h.depth
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · have he' : h.depth ≠ j := Ne.symm he
        simp only [he, he', ite_false, if_false, add_zero]
        change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
          Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
        rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
          NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
            List.getElem_ofFn _]
        apply Prod.ext
        · rfl
        · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, List.set_eq_take_append_cons_drop]
  simp only [L, fieldAllIncrements_length, Nat.lt_succ_self, ite_true, if_true]
  rw [List.drop_eq_nil_of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  rfl

lemma fieldHeightCoordinateValue_final (h : FieldStep) (t z : ℝ) :
    fieldHeightCoordinateValue h (Fin.last h.depth) t z = fieldFinalChart h t z := by
  dsimp only [fieldHeightCoordinateValue, fieldFinalChart]
  rw [updated_increments_final, Function.update_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightJoint
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal field-height chart as a finite joint affine covariance
recursion. No admissibility proof is built into this chart. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldHeightSlope_variance {n : ℕ} (j : Fin (n + 1)) (r : Fin (n + 1) → ℝ) :
    fieldFiniteVariance 0 (fieldHeightSlope j) r = fieldHeightIncrement r j := by
  classical
  unfold fieldFiniteVariance fieldHeightSlope fieldHeightIncrement
  rw [zero_add]
  simp only [sub_mul, Finset.sum_sub_distrib]
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj]

lemma fieldFiniteValue_scalar_list {n : ℕ} (L : List (FieldFiniteStep n))
    (r : Fin n → ℝ) (z : ℝ) :
    fieldFiniteValue L (r, z) =
      fieldScalarValue (L.map (fun av =>
        (av.exponent, Real.toNNReal (fieldFiniteVariance av.base av.slope r))))
        (fun y => Real.log (Real.cosh y)) z := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    change gaussianTransform (fieldFiniteVariance av.base av.slope r) av.exponent
      (fun y => fieldFiniteValue L (r, y)) z =
      gaussianOperator av.exponent (Real.toNNReal (fieldFiniteVariance av.base av.slope r))
        (fieldScalarValue (L.map fun bv =>
          (bv.exponent, Real.toNNReal (fieldFiniteVariance bv.base bv.slope r)))
          (fun y => Real.log (Real.cosh y))) z
    rw [gaussianOperator_toNNReal]
    rw [field_gaussianTransform_eq_operator]
    rw [gaussianOperator_toNNReal]
    congr 2
    funext y
    exact ih y

lemma fieldHeightJointValue_scalar (h : FieldStep) (r : Fin (h.depth + 1) → ℝ) (z : ℝ) :
    fieldHeightJointValue h r z =
      fieldScalarValue (List.ofFn fun j : Fin (h.depth + 1) =>
        (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j)))
        (fun y => Real.log (Real.cosh y)) z - r (Fin.last h.depth) / 2 := by
  unfold fieldHeightJointValue
  rw [fieldFiniteValue_scalar_list]
  congr 2
  rw [fieldHeightFiniteList, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change (h.cut j.castSucc, Real.toNNReal (fieldFiniteVariance 0 (fieldHeightSlope j) r)) = _
  rw [fieldHeightSlope_variance]

lemma fieldHeightJointValue_update (h : FieldStep) (i : Fin (h.depth + 1)) (t z : ℝ) :
    fieldHeightJointValue h (Function.update h.height i (h.height i + t)) z =
      fieldHeightCoordinateValue h i t z :=
  fieldHeightJointValue_scalar h _ z

lemma fieldHeightJointValue_eq_fieldValue (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) (z : ℝ) :
    fieldHeightJointValue h r z = fieldValue (fieldWithHeights h r hr0 hrmono) z := by
  let k := fieldWithHeights h r hr0 hrmono
  have he : (List.ofFn fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j))) = fieldAllIncrements k := by
    unfold fieldAllIncrements
    apply congrArg List.ofFn
    funext j
    apply Prod.ext
    · rfl
    · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg k j)
  rw [fieldHeightJointValue_scalar, he]
  exact fieldAllIncrements_value k z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightCone
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict finite field-height cone and its original FieldStep
representatives. Positive increments give every height and order constraint. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma continuous_fieldHeightIncrement {n : ℕ} (j : Fin (n + 1)) :
    Continuous (fun r : Fin (n + 1) → ℝ => fieldHeightIncrement r j) := by
  unfold fieldHeightIncrement
  split_ifs <;> fun_prop

lemma isOpen_fieldStrictHeightCone (n : ℕ) : IsOpen (fieldStrictHeightCone n) := by
  simpa only [fieldStrictHeightCone, ofPred_forall] using
    isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
      isOpen_lt continuous_const (continuous_fieldHeightIncrement j))

lemma fieldStepOfStrictHeights_strict (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (j : Fin (h.depth + 1)) :
    0 < (fieldIncrement (fieldStepOfStrictHeights h r hr) j).2 := hr j

lemma fieldHeightJointValue_strict (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (z : ℝ) :
    fieldHeightJointValue h r z = fieldValue (fieldStepOfStrictHeights h r hr) z :=
  fieldHeightJointValue_eq_fieldValue h r (fieldStrictHeightCone_nonneg hr)
    (fieldStrictHeightCone_strictMono hr).monotone z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightBox
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A convex increment box carrying one joint derivative family for two
strict field-height vectors and the segment joining them. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma isOpen_fieldHeightBox (n : ℕ) (m V : ℝ) : IsOpen (fieldHeightBox n m V) := by
  simpa only [fieldHeightBox, ofPred_forall, Set.preimage] using
    isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
      isOpen_Ioo.preimage (continuous_fieldHeightIncrement j))

lemma convex_fieldHeightBox (n : ℕ) (m V : ℝ) : Convex ℝ (fieldHeightBox n m V) := by
  intro r hr s hs a b ha hb hab j
  have he : fieldHeightIncrement (a • r + b • s) j =
      a * fieldHeightIncrement r j + b * fieldHeightIncrement s j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  exact (convex_Ioo m V) (hr j) (hs j) ha hb hab

lemma fieldHeightBox_subset_strict {n : ℕ} {m V : ℝ} (hm : 0 ≤ m) :
    fieldHeightBox n m V ⊆ fieldStrictHeightCone n := by
  intro r hr j
  exact hm.trans_lt (hr j).1

lemma fieldHeightBox_pair {n : ℕ} (r s : Fin (n + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone n) (hs : s ∈ fieldStrictHeightCone n) :
    ∃ m V : ℝ, 0 < m ∧ r ∈ fieldHeightBox n m V ∧ s ∈ fieldHeightBox n m V := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ
  have hS : S.Nonempty := ⟨0, Finset.mem_univ _⟩
  let lo := S.inf' hS (fun j => min (fieldHeightIncrement r j) (fieldHeightIncrement s j))
  let hi := S.sup' hS (fun j => max (fieldHeightIncrement r j) (fieldHeightIncrement s j))
  have hlo : 0 < lo := (Finset.lt_inf'_iff hS).mpr (fun j _ => lt_min (hr j) (hs j))
  have hl (j : Fin (n + 1)) : lo ≤ min (fieldHeightIncrement r j) (fieldHeightIncrement s j) :=
    Finset.inf'_le (s := S)
      (fun j => min (fieldHeightIncrement r j) (fieldHeightIncrement s j)) (Finset.mem_univ j)
  have hu (j : Fin (n + 1)) : max (fieldHeightIncrement r j) (fieldHeightIncrement s j) ≤ hi :=
    Finset.le_sup' (s := S)
      (fun j => max (fieldHeightIncrement r j) (fieldHeightIncrement s j)) (Finset.mem_univ j)
  refine ⟨lo / 2, hi + 1, by positivity, ?_, ?_⟩
  · intro j
    have hlj := (hl j).trans (min_le_left _ _)
    have huj := (le_max_left _ _).trans (hu j)
    constructor <;> linarith
  · intro j
    have hlj := (hl j).trans (min_le_right _ _)
    have huj := (le_max_right _ _).trans (hu j)
    constructor <;> linarith

theorem fieldHeightBox_family (h : FieldStep) (m V : ℝ) (hm : 0 < m) :
    ∃ F : FieldFiniteFamily (h.depth + 1) (fieldHeightBox h.depth m V),
      F.U = fieldFiniteValue (fieldHeightFiniteList h) := by
  let I := fieldHeightBox h.depth m V
  let L := fieldHeightFiniteList h
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  obtain ⟨B, hB, hb⟩ := fieldFinite_coefficient_bound L
  let R := B / (2 * Real.sqrt m)
  let D := (B / 2) * m⁻¹ * R
  have hR : 0 ≤ R := by dsimp only [R] <;> positivity
  have hD : 0 ≤ D := by dsimp only [D] <;> positivity
  have hbracket (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) :
      m < fieldFiniteVariance av.base av.slope r ∧ fieldFiniteVariance av.base av.slope r < V := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hav
    change m < fieldFiniteVariance 0 (fieldHeightSlope j) r ∧
      fieldFiniteVariance 0 (fieldHeightSlope j) r < V
    rw [fieldHeightSlope_variance]
    exact hr j
  have hv (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) :
      0 < fieldFiniteVariance av.base av.slope r ∧ fieldFiniteVariance av.base av.slope r ≤ V :=
    ⟨hm.trans (hbracket av hav r hr).1, (hbracket av hav r hr).2.le⟩
  have hc (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) :
      |fieldFiniteSlope av.base av.slope r i| ≤ R :=
    fieldFinite_slope_bound av.base av.slope r hm (hbracket av hav r hr).1.le (hb av hav) i
  have hd (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ L)
      (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i j : Fin (h.depth + 1)) :
      |fieldFiniteCurvature av.base av.slope r i j| ≤ D :=
    fieldFinite_curvature_bound av.base av.slope r hm hB (hbracket av hav r hr).1.le (hb av hav) i j
  exact ⟨fieldFiniteFamily I hI V R D hR hD L hv hc hd,
    fieldFiniteFamily_value I hI V R D hR hD L hv hc hd⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHessianAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional Hessian argument in `fld:concavity`: a
symmetric matrix with nonpositive off-diagonal entries and nonnegative
row sums is nonnegative as a quadratic form, also after positive scaling. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma field_quadratic_nonneg_of_row_sums {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 ≤ ∑ j, M i j) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  let S := ∑ i, ∑ j, M i j * (x i - x j) ^ 2
  let R := ∑ i, ∑ j, M i j * (x i) ^ 2
  let Q := ∑ i, ∑ j, M i j * x i * x j
  have hS : S ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (sq_nonneg _)
  have hR : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro i _
    rw [← Finset.sum_mul]
    exact mul_nonneg (hrow i) (sq_nonneg _)
  have hswap : (∑ i, ∑ j, M i j * (x j) ^ 2) = R := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have he : S = 2 * R - 2 * Q := by
    calc
      S = ∑ i, ∑ j, ((M i j * (x i) ^ 2 + M i j * (x j) ^ 2) -
          2 * (M i j * x i * x j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = R + (∑ i, ∑ j, M i j * (x j) ^ 2) - 2 * Q := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, R, Q]
      _ = 2 * R - 2 * Q := by rw [hswap]; ring
  dsimp only [Q] at he
  linarith

theorem field_quadratic_nonneg_of_positive_scaling {n : ℕ}
    (M : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hpos : ∀ i, 0 < h i) (hrow : ∀ i, 0 ≤ ∑ j, M i j * h j)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  let A := fun i j => h i * M i j * h j
  have hAsym : ∀ i j, A i j = A j i := by
    intro i j
    dsimp only [A]
    rw [hsym i j]
    ring
  have hAoff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hpos i).le (hoff i j hij)) (hpos j).le
  have hArow : ∀ i, 0 ≤ ∑ j, A i j := by
    intro i
    have he : (∑ j, A i j) = h i * ∑ j, M i j * h j := by
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact mul_nonneg (hpos i).le (hrow i)
  have hq := field_quadratic_nonneg_of_row_sums A hAsym hAoff hArow (fun i => x i / h i)
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [A]
  field_simp [(hpos i).ne', (hpos j).ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRadialHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial row sign of the actual finite-height Hessian. The proof
transports the already proved covariance-scaling order of magnetization,
using the literal gradient identity on a neighborhood of a strict field. -/

noncomputable section
open IsingPerceptron Set Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma fieldStrictHeightCone_smul {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) {a : ℝ} (ha : 0 < a) :
    a • r ∈ fieldStrictHeightCone n := by
  intro j
  have he : fieldHeightIncrement (a • r) j = a * fieldHeightIncrement r j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  exact mul_pos ha (hr j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVaryingRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite cascade exponents with varying nonnegative scalar
variances. These are the actual log-cosh recursion and spin observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldVaryingValue_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) :
    fieldVaryingValue L t = fieldScalarValue (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) := by
  simp only [fieldVaryingValue, fieldScalarValue, List.foldr_map]

lemma fieldVaryingMean_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) :
    fieldVaryingMean L t = fieldScalarMean (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    simp only [fieldVaryingMean, List.map_cons, fieldScalarMean,
      fieldVaryingValue_eq_scalar, ih]

lemma fieldVaryingSquares_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (t : E) (i : Fin (L.length + 1)) :
    fieldVaryingSquares L t i = fieldScalarSquares (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) i) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [fieldVaryingSquares, Fin.cons_zero, Fin.cast_zero]
      funext z
      rw [fieldScalarSquares_zero, fieldVaryingMean_eq_scalar]
    · change fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
        (fieldVaryingSquares L t j) =
          fieldSpinTransition av.1 (av.2 t)
            (fieldScalarValue (L.map (fun bv => (bv.1, bv.2 t)))
              (fun z => Real.log (Real.cosh z)))
            (fieldScalarSquares (L.map (fun bv => (bv.1, bv.2 t)))
              (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) j))
      rw [fieldVaryingValue_eq_scalar, ih]

lemma fieldVaryingValue_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) :
    Measurable (fieldVaryingValue L t) ∧ HasLinearGrowth (fieldVaryingValue L t) := by
  rw [fieldVaryingValue_eq_scalar]
  apply fieldScalarValue_regular _ _ measurable_logCosh logCosh_linearGrowth
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingMean_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) :
    Measurable (fieldVaryingMean L t) ∧ ∀ z, |fieldVaryingMean L t z| ≤ 1 := by
  rw [fieldVaryingMean_eq_scalar]
  apply fieldScalarMean_regular (a := Real.tanh) _ _ measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun z : ℝ => Real.tanh z); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingSquares_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (i : Fin (L.length + 1)) :
    Measurable (fieldVaryingSquares L t i) ∧
      ∀ z, fieldVaryingSquares L t i z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fieldVaryingSquares_eq_scalar]
  apply fieldScalarSquares_regular (a := Real.tanh) _ _ measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun z : ℝ => Real.tanh z); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingValue_nonneg {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (z : ℝ) :
    0 ≤ fieldVaryingValue L t z := by
  induction L generalizing z with
  | nil => exact Real.log_nonneg (Real.one_le_cosh z)
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldVaryingValue_regular L ht t
    have hg : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) := by
      refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
      simp
    have hm := gaussianOperator_mono measurable_const hr.1 hg hr.2
      (fun y => ih ht y) (hL av List.mem_cons_self).le (av.2 t) z
    simpa only [fieldVaryingValue, List.foldr_cons, gaussianOperator, ite_self,
      mul_zero, Real.exp_zero, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul, Real.log_one, mul_zero] using hm

lemma fieldVaryingValue_bound {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    0 ≤ fieldVaryingCap L V ∧
      ∀ t z, |fieldVaryingValue L t z| ≤ fieldVaryingCap L V + |z| := by
  induction L with
  | nil =>
    refine ⟨le_rfl, fun t z => ?_⟩
    simpa only [fieldVaryingValue, fieldVaryingCap, List.map_nil, List.sum_nil,
      List.foldr_nil, zero_add] using abs_log_cosh_le z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    obtain ⟨hc, hb⟩ := ih ht hvt
    have ha := hL av List.mem_cons_self
    have hav := hv av List.mem_cons_self
    have hcap : 0 ≤ fieldVaryingCap (av :: L) V := by
      change 0 ≤ (av.1 * V / 2 + Real.log 2 / av.1) + fieldVaryingCap L V
      positivity
    refine ⟨hcap, fun t z => ?_⟩
    have hr := fieldVaryingValue_regular L ht t
    have hg := linearGrowth_const_add abs_linearGrowth (fieldVaryingCap L V)
    have hm := gaussianOperator_mono (G := fun y : ℝ => fieldVaryingCap L V + |y|)
      hr.1 (by fun_prop)
      hr.2 hg (fun y => (le_abs_self _).trans (hb t y)) ha.le (av.2 t) z
    rw [gaussianOperator_const_add (F := fun y : ℝ => |y|)
      (by fun_prop) abs_linearGrowth] at hm
    have habs : gaussianOperator av.1 (av.2 t) (fun y : ℝ => |y|) z ≤
        |z| + av.1 * (av.2 t : ℝ) / 2 + Real.log 2 / av.1 := by
      rw [gaussianOperator_eq_transform]
      exact gaussianTransform_abs_bound (av.2 t).coe_nonneg ha z
    rw [abs_of_nonneg (fieldVaryingValue_nonneg (av :: L) hL t z)]
    change gaussianOperator av.1 (av.2 t) (fieldVaryingValue L t) z ≤ _
    have hvar := mul_le_mul_of_nonneg_left (hav t) ha.le
    change _ ≤ (av.1 * V / 2 + Real.log 2 / av.1) + fieldVaryingCap L V + |z|
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldVaryingContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the actual finite scalar recursion and its
physical-spin second moments, including zero variance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal

namespace InvariantIsing

lemma field_continuous_tanh : Continuous Real.tanh := by
  change Continuous (fun z : ℝ => Real.tanh z)
  simp only [Real.tanh_eq]
  exact (Real.continuous_exp.sub (Real.continuous_exp.comp continuous_neg)).div
    (Real.continuous_exp.add (Real.continuous_exp.comp continuous_neg))
    (fun z => (add_pos (Real.exp_pos z) (Real.exp_pos (-z))).ne')

theorem continuous_fieldVaryingValue {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    Continuous (fun p : E × ℝ => fieldVaryingValue L p.1 p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => Real.log (Real.cosh p.2))
    exact (Real.continuous_cosh.comp continuous_snd).log (fun p => (Real.cosh_pos p.2).ne')
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    have hval := ih hLt hct hvt
    obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
    change Continuous (fun p : E × ℝ => gaussianOperator av.1 (av.2 p.1)
      (fieldVaryingValue L p.1) p.2)
    simp_rw [gaussianOperator_eq_transform]
    exact continuous_field_gaussian_transform (E := E × ℝ)
      (U := fun p y => fieldVaryingValue L p.1 y)
      (hval.comp (continuous_fst.fst.prodMk continuous_snd))
      ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
      hcap zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y) av.1

theorem continuous_fieldVaryingMean {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    Continuous (fun p : E × ℝ => fieldVaryingMean L p.1 p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => Real.tanh p.2)
    exact field_continuous_tanh.comp continuous_snd
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    have hval := continuous_fieldVaryingValue L hLt hct hV hvt
    have hmean := ih hLt hct hvt
    obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
    have hcont := continuous_field_gaussian_tilt_average (E := E × ℝ)
      (U := fun p y => fieldVaryingValue L p.1 y)
      (A := fun p y => fieldVaryingMean L p.1 y)
      (hval.comp (continuous_fst.fst.prodMk continuous_snd))
      (hmean.comp (continuous_fst.fst.prodMk continuous_snd))
      ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
      hcap zero_le_one zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
      (fun p y => (fieldVaryingMean_regular L hLt p.1).2 y) av.1
    convert hcont using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact fieldSpinTransition_eq_standard av.1 (av.2 p.1)
      (fieldVaryingValue_regular L hLt p.1).1 (fieldVaryingMean_regular L hLt p.1).1 p.2

theorem continuous_fieldVaryingSquares {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V)
    (i : Fin (L.length + 1)) :
    Continuous (fun p : E × ℝ => fieldVaryingSquares L p.1 i p.2) := by
  induction L with
  | nil =>
    change Continuous (fun p : E × ℝ => (Real.tanh p.2) ^ 2)
    exact (field_continuous_tanh.comp continuous_snd).pow 2
  | cons av L ih =>
    have hLt : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hct := fun bv hb => hc bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (continuous_fieldVaryingMean (av :: L) hL hc hV hv).pow 2
    · have hval := continuous_fieldVaryingValue L hLt hct hV hvt
      have hsq := ih hLt hct hvt j
      obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hLt hV hvt
      have hcont := continuous_field_gaussian_tilt_average (E := E × ℝ)
        (U := fun p y => fieldVaryingValue L p.1 y)
        (A := fun p y => fieldVaryingSquares L p.1 j y)
        (hval.comp (continuous_fst.fst.prodMk continuous_snd))
        (hsq.comp (continuous_fst.fst.prodMk continuous_snd))
        ((NNReal.continuous_coe.comp (hc av List.mem_cons_self)).comp continuous_fst) continuous_snd
        hcap zero_le_one zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
        (fun p y => by
          have hr := (fieldVaryingSquares_regular L hLt p.1 j).2 y
          rw [abs_of_nonneg hr.1]
          exact hr.2) av.1
      convert hcont using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      exact fieldSpinTransition_eq_standard av.1 (av.2 p.1)
        (fieldVaryingValue_regular L hLt p.1).1
        (fieldVaryingSquares_regular L hLt p.1 j).1 p.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded strict-height approximation of an arbitrary finite field.
Every variance increment is increased by the same small scalar. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldHeightEpsilon_le_one (t : ℝ) : fieldHeightEpsilon t ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

lemma continuous_fieldHeightEpsilon : Continuous fieldHeightEpsilon := by
  unfold fieldHeightEpsilon
  fun_prop

lemma fieldHeightEpsilon_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : fieldHeightEpsilon t = t := by
  exact (congrArg (max 0) (min_eq_left ht.2)).trans (max_eq_right ht.1)

lemma fieldRegularized_increment (h : FieldStep) (t : ℝ) (i : Fin (h.depth + 1)) :
    (fieldIncrement (fieldRegularized h t) i).2 =
      (fieldIncrement h i).2 + fieldHeightEpsilon t := by
  change fieldHeightIncrement (fieldRegularizedHeight h t) i =
    fieldHeightIncrement h.height i + fieldHeightEpsilon t
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [fieldHeightIncrement, fieldRegularizedHeight]
  · rw [fieldHeightIncrement_succ, fieldHeightIncrement_succ]
    simp only [fieldRegularizedHeight, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
      Nat.cast_one]
    ring

lemma fieldRegularized_strict (h : FieldStep) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (i : Fin (h.depth + 1)) : 0 < (fieldIncrement (fieldRegularized h t) i).2 := by
  rw [fieldRegularized_increment, fieldHeightEpsilon_eq ⟨ht.1.le, ht.2⟩]
  exact add_pos_of_nonneg_of_pos (fieldIncrement_nonneg h i) ht.1

lemma fieldRegularized_zero (h : FieldStep) : fieldRegularized h 0 = h := by
  have he : fieldRegularizedHeight h 0 = h.height := by
    funext i
    simp [fieldRegularizedHeight, fieldHeightEpsilon]
  unfold fieldRegularized fieldWithHeights
  congr 1

lemma fieldIncrement_le_last (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 ≤ h.height (Fin.last h.depth) := by
  have hh := h.ordered_height (Fin.le_last i)
  change h.height i - (if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩) ≤ _
  split_ifs with hi
  · simpa only [sub_zero] using hh
  · exact (sub_le_self _ (h.nonneg _)).trans hh

lemma fieldRegularizedIncrements_positive (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact fieldIncrement_tail_positive h i

lemma fieldRegularizedIncrements_continuous (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, Continuous av.2 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact (continuous_const.add continuous_fieldHeightEpsilon).subtype_mk _

lemma fieldRegularizedIncrements_bound (h : FieldStep) :
    ∀ av ∈ fieldRegularizedIncrements h, ∀ t, (av.2 t : ℝ) ≤ h.height (Fin.last h.depth) + 1 := by
  intro av hav t
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact add_le_add (fieldIncrement_le_last h i.succ) (fieldHeightEpsilon_le_one t)

lemma fieldRegularizedIncrements_eval (h : FieldStep) (t : ℝ) :
    (fieldRegularizedIncrements h).map (fun av => (av.1, av.2 t)) =
      scalarFieldIncrements (fieldRegularized h t) := by
  rw [fieldRegularizedIncrements, List.map_ofFn, scalarFieldIncrements]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact (fieldRegularized_increment h t i.succ).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightBoundaryContinuity
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict regularization converges in the actual field value and
every actual magnetization level. No endpoint derivative is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma continuous_fieldRegularizedRoot (h : FieldStep) : Continuous (fieldRegularizedRoot h) :=
  (continuous_const.add continuous_fieldHeightEpsilon).subtype_mk _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPairingContinuity
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing errors for the rounded quantile paths used in the cavity
calculation. A uniform field-height bound suffices for L1 stability. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

lemma field_pairing_path_error (p q : OverlapPath) (h : FieldStep) :
    |fieldPairing p h - fieldPairing q h| ≤ h.height (Fin.last h.depth) *
      ∫ s, |p s - q s| ∂pathMeasure := by
  have hi : Integrable (fun s => (p s - q s) * fieldFunction h s) pathMeasure := by
    apply ((integrable_path_mul_field p h).sub (integrable_path_mul_field q h)).congr
    apply ae_of_all
    intro s
    change p s * fieldFunction h s - q s * fieldFunction h s = _
    ring
  have he : fieldPairing p h - fieldPairing q h =
      ∫ s, (p s - q s) * fieldFunction h s ∂pathMeasure := by
    rw [fieldPairing, fieldPairing, ← integral_sub (integrable_path_mul_field p h)
      (integrable_path_mul_field q h)]
    congr 1
    funext s
    ring
  rw [he]
  calc
    _ ≤ ∫ s, |(p s - q s) * fieldFunction h s| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, h.height (Fin.last h.depth) * |p s - q s| ∂pathMeasure := by
      apply integral_mono hi.abs (((p.integrable.sub q.integrable).abs).const_mul _)
      intro s
      dsimp only
      rw [abs_mul, abs_of_nonneg (fieldFunction_nonneg h s)]
      exact (mul_le_mul_of_nonneg_left (fieldFunction_le_last h s) (abs_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem field_pairing_path_tendsto (p : OverlapPath) (q : ℕ → OverlapPath)
    (h : ℕ → FieldStep) {C : ℝ}
    (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hq : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => fieldPairing (q n) (h n) - fieldPairing p (h n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => C * ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0) by
      simpa only [mul_zero] using hq.const_mul C)
  rw [Real.norm_eq_abs]
  exact (field_pairing_path_error (q n) p (h n)).trans
    (mul_le_mul_of_nonneg_right (hC n) (integral_nonneg (fun _ => abs_nonneg _)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldPartitionSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar-field supporting inequality, independent of the finite partition. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma field_eq_withHeights_of_cutList {h k : FieldStep}
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    ∃ (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r),
      k = fieldWithHeights h r hr0 hrmono := by
  have hl := congrArg List.length he
  simp only [List.length_ofFn] at hl
  have hd : h.depth = k.depth := by omega
  rcases h with ⟨n, cut, hcut, hfirst, hlast, v, hv0, hvm⟩
  rcases k with ⟨m, cut', hcut', hfirst', hlast', w, hw0, hwm⟩
  dsimp only at hd
  subst m
  have hcut_eq : cut = cut' := List.ofFn_injective he
  subst cut'
  exact ⟨w, hw0, hwm, rfl⟩

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

lemma hasDerivAt_fieldValue_bias (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldValue h) (fieldBiasMean h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hD := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hd := hasDerivAt_gaussianOperator 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hF.1 hF.2 hD.1 zero_le_one hD.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL) b
  refine ((hd.sub_const (h.height (Fin.last h.depth) / 2)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact fieldValue_root h z
  · rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict bias convexity follows from the positive terminal curvature
and the nonnegative conditional variance terms in the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_pos (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ z, |a z| ≤ B) (hap : ∀ z, 0 < a z) (z : ℝ) :
    0 < fieldSpinTransition ζ v F a z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hG ζ
  let μ := (gaussianReal z v).tilted (fun u => ζ * F u)
  have : IsProbabilityMeasure μ := MeasureTheory.isProbabilityMeasure_tilted hw
  have hi : Integrable a μ := (integrable_const B).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hs : Function.support a = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hap u).ne'
  change 0 < ∫ u, a u ∂μ
  apply (integral_pos_iff_support_of_nonneg (fun u => (hap u).le) hi).mpr
  rw [hs, measure_univ]
  exact (zero_lt_one : (0 : ENNReal) < 1)

lemma fieldScalarLogCoshSecond_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    0 < fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos z))
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hs := fieldScalarLogCoshSecond_regular L ht
    have hp := fieldSpinTransition_pos av.1 av.2 hv.1 hv.2 hs.1 hs.2 (ih ht) z
    have hm : Measurable Real.tanh := by
      change Measurable (fun z : ℝ => Real.tanh z)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hc := fieldSpinTransition_square_le av.1 av.2 hv.1 hv.2 ha.1 ha.2 z
    have hζ := (hL av List.mem_cons_self).le
    change 0 < fieldSpinTransition av.1 av.2 _ _ z + av.1 *
      (fieldSpinTransition av.1 av.2 _ _ z - (fieldScalarMean (av :: L) _ _ z) ^ 2)
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hc))

lemma fieldBiasCurvature_pos (h : FieldStep) (b : ℝ) : 0 < fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  exact fieldSpinTransition_pos 0 _ hv.1 hv.2 hs.1 hs.2
    (fieldScalarLogCoshSecond_pos (scalarFieldIncrements h) hL) b

lemma hasDerivAt_fieldBiasMean (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldBiasMean h) (fieldBiasCurvature h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  have hd := hasDerivAt_fieldSpinTransition 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 ha.1 hs.1
    zero_le_one zero_le_one ha.2 ha.2 hs.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL)
    (hasDerivAt_fieldScalarLogCoshMean (scalarFieldIncrements h) hL) b
  simpa only [zero_mul, add_zero, fieldBiasMean, fieldBiasCurvature] using hd

lemma strictMono_fieldBiasMean (h : FieldStep) : StrictMono (fieldBiasMean h) := by
  apply strictMono_of_deriv_pos
  intro b
  rw [(hasDerivAt_fieldBiasMean h b).deriv]
  exact fieldBiasCurvature_pos h b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLevels
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conditional squared spin means at prescribed magnetization.
The root Gaussian is averaged at the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma magneticLevelAtBias_allSquares (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) :
    magneticLevelAtBias h b i =
      fieldScalarSquares (fieldAllIncrements h) (fun z => Real.log (Real.cosh z)) Real.tanh
        ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ b := by
  let j : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have he := fieldScalarSquares_congr_list (fieldAllIncrements_root h) (fun z => Real.log (Real.cosh z)) Real.tanh
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ j.succ (by rfl)
  rw [congrFun he b]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticImplicitBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parametric inversion of a strictly increasing physical mean spin.
This supplies the finite-dimensional inverse-coordinate and envelope steps
without assuming differentiability of the minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma parametric_bias_continuousAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s : ℝ}
    (hc : ∀ z, ContinuousAt (fun q => A (q, z)) t)
    (hm : ∀ᶠ q in 𝓝 t, StrictMono (fun z => A (q, z)))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) : ContinuousAt b t := by
  have het := he.self_of_nhds
  have hmt := hm.self_of_nhds
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : A (t, l) < s := by rw [← het]; exact hmt hl
    have hn : ∀ᶠ q in 𝓝 t, A (q, l) < s :=
      (hc l).tendsto.eventually (Iio_mem_nhds hlt)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]
  · intro u hu
    have htu : s < A (t, u) := by rw [← het]; exact hmt hu
    have hn : ∀ᶠ q in 𝓝 t, s < A (q, u) :=
      (hc u).tendsto.eventually (Ioi_mem_nhds htu)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]

/-- The implicit bias derivative follows from the derivative of the actual
mean-spin map and the local root equation. -/
lemma parametric_bias_hasDerivAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s a c : ℝ}
    (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) :
    HasDerivAt b (-a / c) t := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear a c)
  let M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear (-a / c) (1 / c))
  have hleft : Function.LeftInverse M L := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · rfl
    · change -a / c * x + (1 / c) * (a * x + c * y) = y
      field_simp [hc]
      ring
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (p.1, A p)) L (t, b t) :=
    hasFDerivAt_fst.prodMk hA
  have hg : ContinuousAt (fun q => (q, b q)) t := continuousAt_id.prodMk hb
  have hh : HasFDerivAt (fun q : ℝ => (q, s))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const s t)
  have hcomp : (fun p : ℝ × ℝ => (p.1, A p)) ∘ (fun q => (q, b q)) =ᶠ[𝓝 t]
      (fun q => (q, s)) := by
    filter_upwards [he] with q hq
    exact congrArg (Prod.mk q) hq
  have hd := HasFDerivAt.of_comp_of_leftInverse hg hf hh hcomp hleft
  have hsnd := hd.snd.hasDerivAt
  convert hsnd using 1
  all_goals try with_reducible_and_instances rfl
  simp [M, pairLinear]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBoundaryContinuity
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the prescribed-magnetization functional along the strict
height regularization, including coincident heights and zero root variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldRegularized_depth (h : FieldStep) (t : ℝ) :
    (fieldRegularized h t).depth = h.depth := rfl

lemma continuous_fieldRegularizedValue_bias (h : FieldStep) :
    Continuous (fun p : ℝ × ℝ => fieldValue (fieldRegularized h p.1) p.2) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hval := continuous_fieldVaryingValue L hL hc hV hv
  obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hL hV hv
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingValue L p.1 y)
    (hval.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    hcap zero_le_one (fun p y => by simpa only [one_mul] using hb p.1 y)
  have hlast : Continuous (fun p : ℝ × ℝ =>
      (fieldRegularized h p.1).height (Fin.last h.depth) / 2) := by
    change Continuous (fun p : ℝ × ℝ => (h.height (Fin.last h.depth) +
      fieldHeightEpsilon p.1 * ((Fin.last h.depth).val + 1 : ℕ)) / 2)
    have heps := continuous_fieldHeightEpsilon
    fun_prop
  convert hi.sub hlast using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [fieldValue_root, ← fieldRegularizedIncrements_eval,
    ← fieldVaryingValue_eq_scalar]
  simp only [gaussianOperator, ite_true, if_true, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one,
    fieldRegularizedRoot, NNReal.coe_mk, Pi.sub_apply, L]
  rfl

lemma continuous_fieldRegularizedMean_bias (h : FieldStep) :
    Continuous (fun p : ℝ × ℝ => fieldBiasMean (fieldRegularized h p.1) p.2) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hm := continuous_fieldVaryingMean L hL hc hV hv
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingMean L p.1 y)
    (hm.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    zero_le_one (le_refl (0 : ℝ)) (fun p y => by
      simpa only [zero_mul, add_zero] using (fieldVaryingMean_regular L hL p.1).2 y)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold fieldBiasMean
  rw [← fieldRegularizedIncrements_eval, ← fieldVaryingValue_eq_scalar,
    ← fieldVaryingMean_eq_scalar,
    fieldSpinTransition_eq_standard 0 _ (fieldVaryingValue_regular L hL p.1).1
      (fieldVaryingMean_regular L hL p.1).1, gaussianTiltAverage_zero]
  simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one, NNReal.coe_mk]
  rfl

lemma continuous_fieldRegularizedLevel_bias (h : FieldStep) (i : Fin (h.depth + 1)) :
    Continuous (fun p : ℝ × ℝ => magneticLevelAtBias (fieldRegularized h p.1) p.2 i) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  let j : Fin (L.length + 1) := ⟨i.val, by
    simpa only [L, fieldRegularizedIncrements, List.length_ofFn] using i.isLt⟩
  have hm := continuous_fieldVaryingSquares L hL hc hV hv j
  have hroot : Continuous (fun p : ℝ × ℝ => (fieldRegularizedRoot h p.1 : ℝ)) :=
    (NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)).comp continuous_fst
  have hi := continuous_field_gaussian_integral (E := ℝ × ℝ)
    (U := fun p y => fieldVaryingSquares L p.1 j y)
    (hm.comp (continuous_fst.fst.prodMk continuous_snd)) hroot continuous_snd
    zero_le_one (le_refl (0 : ℝ)) (fun p y => by
      have hb := (fieldVaryingSquares_regular L hL p.1 j).2 y
      simpa only [zero_mul, add_zero, abs_of_nonneg hb.1] using hb.2)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  change fieldSpinTransition 0 (NNReal.mk ((fieldRegularized h p.1).height 0)
    ((fieldRegularized h p.1).nonneg 0))
    (fieldScalarValue (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i.val, by rw [scalarFieldIncrements_length, fieldRegularized_depth]; exact i.isLt⟩) p.2 = _
  have he : fieldScalarSquares (scalarFieldIncrements (fieldRegularized h p.1))
      (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i.val, by rw [scalarFieldIncrements_length, fieldRegularized_depth]; exact i.isLt⟩ =
      fieldVaryingSquares L p.1 j := by
    rw [fieldVaryingSquares_eq_scalar]
    exact fieldScalarSquares_congr_list (fieldRegularizedIncrements_eval h p.1).symm
      (fun z => Real.log (Real.cosh z)) Real.tanh _ _ rfl
  rw [he, ← fieldRegularizedIncrements_eval, ← fieldVaryingValue_eq_scalar,
    fieldSpinTransition_eq_standard 0 _ (fieldVaryingValue_regular L hL p.1).1
      (fieldVaryingSquares_regular L hL p.1 j).1, gaussianTiltAverage_zero]
  simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one, NNReal.coe_mk]
  rfl

lemma continuous_fieldRegularizedMagneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    Continuous (fun t => magneticBias (fieldRegularized h t) s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply parametric_bias_continuousAt
    (A := fun p => fieldBiasMean (fieldRegularized h p.1) p.2)
    (s := s)
  · intro z
    exact ((continuous_fieldRegularizedMean_bias h).comp
      (continuous_id.prodMk continuous_const)).continuousAt
  · exact Eventually.of_forall (fun q => strictMono_fieldBiasMean (fieldRegularized h q))
  · exact Eventually.of_forall (fun q => fieldBiasMean_magneticBias (fieldRegularized h q) hs)

lemma continuous_fieldRegularizedConstrainedValue (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    Continuous (fun t => constrainedFieldValue (fieldRegularized h t) s) := by
  have hb := continuous_fieldRegularizedMagneticBias h hs
  have hv := (continuous_fieldRegularizedValue_bias h).comp (continuous_id.prodMk hb)
  convert hv.sub (hb.mul_const s) using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact constrainedFieldValue_magneticBias (fieldRegularized h t) hs

lemma continuous_fieldRegularizedMagneticLevel (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (i : Fin (h.depth + 1)) :
    Continuous (fun t => magneticFieldLevel (fieldRegularized h t) s i) := by
  have hb : Continuous (fun t => magneticBias (fieldRegularized h t) s) :=
    continuous_fieldRegularizedMagneticBias h hs
  have hp : Continuous (fun t : ℝ => (t, magneticBias (fieldRegularized h t) s)) :=
    continuous_id.prodMk hb
  have hc : Continuous (fun p : ℝ × ℝ =>
      magneticLevelAtBias (fieldRegularized h p.1) p.2 i) :=
    continuous_fieldRegularizedLevel_bias h i
  change Continuous (fun t : ℝ => magneticLevelAtBias (fieldRegularized h t)
    (magneticBias (fieldRegularized h t) s) i)
  simpa only [Function.comp_def] using hc.comp hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldFamily
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the joint finite-height derivatives with the actual
physical mean and curvature at every bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Classical
open scoped Topology

namespace InvariantIsing

lemma fieldFiniteFamily_mean_at_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) :
    F.X (r, b) = fieldBiasMean (fieldStepOfStrictHeights h r hs) b := by
  have hd := (F.spatial_derivative r hr b).sub_const (r (Fin.last h.depth) / 2)
  have he : (fun z => F.U (r, z) - r (Fin.last h.depth) / 2) =
      fieldValue (fieldStepOfStrictHeights h r hs) := by
    funext z
    rw [hU]
    exact fieldHeightJointValue_strict h r hs z
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldValue_bias (fieldStepOfStrictHeights h r hs) b)

lemma fieldFiniteFamily_curvature_at_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) :
    F.XX (r, b) = fieldBiasCurvature (fieldStepOfStrictHeights h r hs) b := by
  have hd := F.spatial_mean_derivative r hr b
  have he : (fun z => F.X (r, z)) = fieldBiasMean (fieldStepOfStrictHeights h r hs) := by
    funext z
    exact fieldFiniteFamily_mean_at_bias h F hU r hr hs z
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldBiasMean (fieldStepOfStrictHeights h r hs) b)

lemma fieldFiniteFamily_curvature_pos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (b : ℝ) : 0 < F.XX (r, b) := by
  rw [fieldFiniteFamily_curvature_at_bias h F hU r hr hs]
  exact fieldBiasCurvature_pos _ _

lemma magneticHeightBias_eq (h : FieldStep) (s : ℝ) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) :
    magneticHeightBias h s r = magneticBias (fieldStepOfStrictHeights h r hr) s := by
  simp only [magneticHeightBias, dite_eq_left hr]

lemma fieldFiniteFamily_magneticHeightBias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) {s : ℝ} (hs : |s| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    F.X (r, magneticHeightBias h s r) = s := by
  rw [fieldFiniteFamily_mean_at_bias h F hU r hr hrs, magneticHeightBias_eq h s r hrs]
  exact fieldBiasMean_magneticBias _ hs

lemma continuousAt_magneticHeightBias_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    ContinuousAt (fun t : ℝ => magneticHeightBias h s (r + t • d)) 0 := by
  let A := fun p : ℝ × ℝ => F.X (r + p.1 • d, p.2)
  have hpath : Continuous (fun t : ℝ => r + t • d) := by fun_prop
  have hN : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    exact hpath.continuousAt.eventually
      ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds (by simpa using And.intro hr hrs))
  apply parametric_bias_continuousAt (A := A)
  · intro z
    have hc : ContinuousAt F.X (r + (0 : ℝ) • d, z) := by
      simpa only [zero_smul, add_zero] using (F.derivativeX (r, z) hr).continuousAt
    have hp : ContinuousAt (fun t : ℝ => (r + t • d, z)) 0 := by fun_prop
    simpa only [A, zero_smul, add_zero, Function.comp_def] using
      (hc.comp (f := fun t : ℝ => (r + t • d, z)) hp)
  · filter_upwards [hN] with t ht
    have he : (fun z => A (t, z)) =
        fieldBiasMean (fieldStepOfStrictHeights h (r + t • d) ht.2) := by
      funext z
      exact fieldFiniteFamily_mean_at_bias h F hU _ ht.1 ht.2 z
    rw [he]
    exact strictMono_fieldBiasMean _
  · filter_upwards [hN] with t ht
    exact fieldFiniteFamily_magneticHeightBias h F hU hs _ ht.1 ht.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldHeightDerivative
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual height-direction envelope differentiation at fixed magnetization.
The bias response is obtained by implicit differentiation of the finite
physical mean, using its strictly positive curvature. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

lemma hasFDerivAt_field_line_restriction {n : ℕ} {U : FieldCovariate n → ℝ}
    {r d A : Fin n → ℝ} {b c : ℝ}
    (hU : HasFDerivAt U (fieldFiniteLinear A c) (r, b)) :
    HasFDerivAt (fun p : ℝ × ℝ => U (r + p.1 • d, p.2))
      (pairLinear (∑ i, A i * d i) c) (0, b) := by
  let L : (ℝ × ℝ) →L[ℝ] FieldCovariate n :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight d).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hm : HasFDerivAt (fun p : ℝ × ℝ => (r + p.1 • d, p.2)) L ((0 : ℝ), b) := by
    have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) ((0 : ℝ), b) := hasFDerivAt_fst
    have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) ((0 : ℝ), b) := hasFDerivAt_snd
    simpa only [zero_add, L, Pi.add_apply] using
      (((hasFDerivAt_const r ((0 : ℝ), b)).add (hf.smul_const d)).prodMk hs)
  have hu : HasFDerivAt U (fieldFiniteLinear A c)
      ((fun p : ℝ × ℝ => (r + p.1 • d, p.2)) (0, b)) := by
    simpa only [zero_smul, add_zero] using hU
  have hd := hu.comp ((0 : ℝ), b) hm
  refine hd.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro p
    simp only [ContinuousLinearMap.comp_apply, L, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smulRight_apply, fieldFiniteLinear_apply, Pi.smul_apply,
      smul_eq_mul, pairLinear_apply]
    change (∑ i, A i * d i) * p.1 + c * p.2 =
      (∑ i, A i * (p.1 * d i)) + c * p.2
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- An arbitrary strict height direction has the explicitly differentiated
physical optimizing bias. -/
lemma hasDerivAt_magneticHeightBias_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun t : ℝ => magneticHeightBias h s (r + t • d))
      (-(∑ i, F.PX i (r, magneticHeightBias h s r) * d i) /
        F.XX (r, magneticHeightBias h s r)) 0 := by
  let b := fun t : ℝ => magneticHeightBias h s (r + t • d)
  have hb := continuousAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hpos := fieldFiniteFamily_curvature_pos h F hU r hr hrs (b 0)
  have hmean := hasFDerivAt_field_line_restriction (d := d) (F.derivativeX (r, b 0) hr)
  have hN : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    exact hp.eventually ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds
      (by simpa only [zero_smul, add_zero, Set.mem_inter_iff] using And.intro hr hrs))
  have he : ∀ᶠ t : ℝ in 𝓝 0, F.X (r + t • d, b t) = s := by
    filter_upwards [hN] with t ht
    exact fieldFiniteFamily_magneticHeightBias h F hU hs _ ht.1 ht.2
  simpa only [b, zero_smul, add_zero] using
    parametric_bias_hasDerivAt hb hpos.ne' hmean he

lemma constrainedHeightFieldValue_eq (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hrs : r ∈ fieldStrictHeightCone h.depth) :
    constrainedHeightFieldValue h s r =
      fieldHeightJointValue h r (magneticHeightBias h s r) - magneticHeightBias h s r * s := by
  rw [constrainedHeightFieldValue, dite_eq_left hrs,
    constrainedFieldValue_magneticBias _ hs, magneticHeightBias_eq h s r hrs,
    fieldHeightJointValue_strict h r hrs]

lemma hasDerivAt_constrainedHeightFieldValue_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun t : ℝ => constrainedHeightFieldValue h s (r + t • d))
      ((∑ i, F.P i (r, magneticHeightBias h s r) * d i) - d (Fin.last h.depth) / 2) 0 := by
  let b := fun t : ℝ => magneticHeightBias h s (r + t • d)
  have hdb := hasDerivAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hp := ((hasDerivAt_const (0 : ℝ) r).add
    ((hasDerivAt_id (0 : ℝ)).smul_const d)).prodMk hdb
  have hF := F.derivative (r + (0 : ℝ) • d, b 0)
    (by simpa only [zero_smul, add_zero] using hr)
  have hd := hF.comp_hasDerivAt (0 : ℝ) hp
  have hemean : F.X (r, b 0) = s := by
    simpa only [b, zero_smul, add_zero] using
      fieldFiniteFamily_magneticHeightBias h F hU hs r hr hrs
  have hemean' : F.X (r, magneticHeightBias h s r) = s := by
    simpa only [b, zero_smul, add_zero] using hemean
  have hcenter : HasDerivAt (fun t : ℝ => (r + t • d) (Fin.last h.depth) / 2)
      (d (Fin.last h.depth) / 2) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (d (Fin.last h.depth))).const_add
        (r (Fin.last h.depth))).div_const 2
  have hdf := (hd.sub hcenter).sub (hdb.mul_const s)
  have hvalue : (fun t : ℝ => F.U (r + t • d, b t) -
      (r + t • d) (Fin.last h.depth) / 2 - b t * s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => constrainedHeightFieldValue h s (r + t • d)) := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    filter_upwards [hp.eventually ((isOpen_fieldStrictHeightCone _).mem_nhds
      (by simpa only [zero_smul, add_zero] using hrs))] with t ht
    rw [constrainedHeightFieldValue_eq h hs _ ht, fieldHeightJointValue, ← hU]
  convert hdf.congr_of_eventuallyEq hvalue.symm using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_smul, add_zero, zero_add, one_smul, fieldFiniteLinear_apply, b, hemean']
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldGradient
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact physical height gradient at an arbitrary bias, and hence
at the bias realizing a prescribed magnetization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma hasDerivAt_fieldInteriorChart_bias (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldInteriorChart h i t b)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        magneticLevelAtBias h b i.castSucc) 0 := by
  have hd := hasDerivAt_fieldInteriorChart h i hstrict b
  rw [magneticLevelAtBias_allSquares]
  exact hd

private lemma magnetic_terminal_list_zero (h : FieldStep) :
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 0 =
      fieldAllIncrements h := by
  have he := updated_increments_final h 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← he]
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h j)

lemma hasDerivAt_fieldFinalChart_bias (h : FieldStep)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldFinalChart h t b)
      (-(1 - h.cut (Fin.last h.depth).castSucc) / 2 *
        magneticLevelAtBias h b (Fin.last h.depth)) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take h.depth, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have ht : (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) := by
    change -(fieldIncrement h (Fin.last h.depth)).2 < 0
    linarith [hstrict (Fin.last h.depth)]
  have hd := hasDerivAt_fieldTerminalValue (L.take h.depth) hP
    (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1
    (h.height (Fin.last h.depth)) 0 b ht
  have hs := fieldScalarSquares_congr_list (magnetic_terminal_list_zero h)
    (fun y => Real.log (Real.cosh y)) Real.tanh
    (fieldTerminalLevel (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 0)
    ⟨(Fin.last h.depth).val + 1, by simp⟩ (by
      simp [fieldTerminalLevel, fieldAppendIndex, L])
  rw [congrFun hs b, ← magneticLevelAtBias_allSquares] at hd
  exact hd

lemma hasDerivAt_fieldHeightCoordinate_bias (h : FieldStep)
    (i : Fin (h.depth + 1)) (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i t b)
      (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticLevelAtBias h b i) 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : (fun t => fieldHeightCoordinateValue h (Fin.last h.depth) t b) =
        fun t => fieldFinalChart h t b := by
      funext t
      exact fieldHeightCoordinateValue_final h t b
    rw [he]
    simpa only [Fin.succ_last, h.last] using hasDerivAt_fieldFinalChart_bias h hstrict b
  · have he : (fun t => fieldHeightCoordinateValue h j.castSucc t b) =
        fun t => fieldInteriorChart h j t b := by
      funext t
      exact fieldHeightCoordinateValue_interior h j t b
    rw [he]
    exact hasDerivAt_fieldInteriorChart_bias h j hstrict b

lemma fieldFinite_centered_coordinate_derivative_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) (b : ℝ) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), b) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2)
      (F.P i (r, b) - if i = Fin.last h.depth then 1 / 2 else 0) 0 := by
  classical
  have hd := F.coordinate_derivative r b hr i
  by_cases hi : i = Fin.last h.depth
  · subst i
    have hc : HasDerivAt (fun t : ℝ => (r (Fin.last h.depth) + t) / 2) (1 / 2 : ℝ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (r (Fin.last h.depth))).div_const 2
    refine ((hd.sub hc).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      simp only [Pi.sub_apply, Function.update_self]
    · simp
  · have hn : Fin.last h.depth ≠ i := Ne.symm hi
    simpa [Function.update_of_ne hn, hi] using hd.sub_const (r (Fin.last h.depth) / 2)

theorem magneticHeight_gradient_identification (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) (b : ℝ) :
    F.P i (r, b) - (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticLevelAtBias (fieldStepOfStrictHeights h r hs) b i := by
  let k := fieldStepOfStrictHeights h r hs
  have hd := fieldFinite_centered_coordinate_derivative_bias h F r hr i b
  have he : (fun t : ℝ => F.U (Function.update r i (r i + t), b) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2) =
      fun t => fieldHeightCoordinateValue k i t b := by
    funext t
    rw [hU]
    change fieldHeightJointValue k (Function.update k.height i (k.height i + t)) b = _
    exact fieldHeightJointValue_update k i t b
  rw [he] at hd
  have hk := hasDerivAt_fieldHeightCoordinate_bias k i
    (fun j => fieldStepOfStrictHeights_strict h r hs j) b
  exact hd.unique hk

lemma magneticHeight_optimized_gradient (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (_hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    F.P i (r, magneticHeightBias h s r) -
        (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticFieldLevel (fieldStepOfStrictHeights h r hrs) s i := by
  rw [magneticHeight_gradient_identification h F hU r hr hrs i,
    magneticHeightBias_eq h s r hrs]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldHeightHessian
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual constrained finite-height Hessian.  Differentiating the
physical optimizing bias gives the scalar Schur-complement correction;
no twice-differentiable optimizer is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma hasDerivAt_constrainedHeightFieldValue_line_at (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (t : ℝ)
    (hr : r + t • d ∈ I) (hrs : r + t • d ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun q : ℝ => constrainedHeightFieldValue h s (r + q • d))
      ((∑ i, F.P i (r + t • d, magneticHeightBias h s (r + t • d)) * d i) -
        d (Fin.last h.depth) / 2) t := by
  have h0 := hasDerivAt_constrainedHeightFieldValue_line h F hI hU hs
    (r + t • d) d hr hrs
  have h0' : HasDerivAt (fun q : ℝ =>
      constrainedHeightFieldValue h s (r + t • d + q • d))
      ((∑ i, F.P i (r + t • d, magneticHeightBias h s (r + t • d)) * d i) -
        d (Fin.last h.depth) / 2) (id t - t) := by
    simpa only [id_eq, sub_self] using h0
  have hd := h0'.comp (h := fun q : ℝ => q - t) t ((hasDerivAt_id t).sub_const t)
  have he : (fun q : ℝ => constrainedHeightFieldValue h s
      (r + t • d + (q - t) • d)) =
      (fun q : ℝ => constrainedHeightFieldValue h s (r + q • d)) := by
    funext q
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [Function.comp_def, sub_self, mul_one, sub_zero, he] using hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticLevelDerivative
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiability of the physical conditional square levels at fixed
magnetization, including the change in the optimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

lemma magneticHeightSchur_symmetric (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (s : ℝ) (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (i j : Fin (h.depth + 1)) :
    magneticHeightSchur h F s r i j = magneticHeightSchur h F s r j i := by
  unfold magneticHeightSchur
  rw [F.symmetric i j (r, magneticHeightBias h s r) hr, mul_comm (F.PX i _)]

lemma hasDerivAt_magneticHeightP_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => F.P i (r + t • d, magneticHeightBias h s (r + t • d)))
      (∑ j, magneticHeightSchur h F s r i j * d j) 0 := by
  have hb := hasDerivAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hp := ((hasDerivAt_const (0 : ℝ) r).add
    ((hasDerivAt_id (0 : ℝ)).smul_const d)).prodMk hb
  have hF := F.derivativeP i (r + (0 : ℝ) • d, magneticHeightBias h s (r + (0 : ℝ) • d))
    (by simpa only [zero_smul, add_zero] using hr)
  have hd := hF.comp_hasDerivAt 0 hp
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [fieldFiniteLinear_apply, zero_add, one_smul,
      zero_smul, add_zero, magneticHeightSchur, sub_mul, Finset.sum_sub_distrib]
    rw [show (∑ j, F.PX i (r, magneticHeightBias h s r) *
        F.PX j (r, magneticHeightBias h s r) / F.XX (r, magneticHeightBias h s r) * d j) =
        F.PX i (r, magneticHeightBias h s r) *
          (∑ j, F.PX j (r, magneticHeightBias h s r) * d j) /
          F.XX (r, magneticHeightBias h s r) by
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    ring

lemma hasDerivAt_magneticHeightLevel_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => magneticHeightLevel h s (r + t • d) i)
      ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
        (∑ j, magneticHeightSchur h F s r i j * d j)) 0 := by
  let w := h.cut i.succ - h.cut i.castSucc
  have hw : w ≠ 0 := (sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)).ne'
  have hd := ((hasDerivAt_magneticHeightP_line h F hI hU hs r d hr hrs i).sub_const
    (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0)).const_mul (-2 / w)
  have hn : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    exact hp.eventually ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds
      (by simpa only [zero_smul, add_zero, Set.mem_inter_iff] using And.intro hr hrs))
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  rw [magneticHeightLevel, dite_eq_left ht.2]
  have he := magneticHeight_optimized_gradient h F hU hs (r + t • d) ht.1 ht.2 i
  rw [he]
  dsimp only [w] at hw ⊢
  field_simp [hw]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRadialHessian
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial row sign of the constrained height Hessian, obtained from
the actual fixed-magnetization radial comparison. -/

noncomputable section
open Set Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma magneticFieldLevel_congr {h k : FieldStep} (he : h = k) (s : ℝ)
    (i : Fin (h.depth + 1)) (j : Fin (k.depth + 1)) (hij : i.val = j.val) :
    magneticFieldLevel h s i = magneticFieldLevel k s j := by
  cases he
  have hi : i = j := Fin.ext hij
  subst j
  rfl

theorem magneticHeight_radial_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    ∑ j, magneticHeightSchur h F s r i j * r j ≤ 0 := by
  let k := fieldStepOfStrictHeights h r hrs
  let c : ℝ → ℝ≥0 := fun t => ⟨Real.sqrt (Real.exp t), Real.sqrt_nonneg _⟩
  let g := fun t : ℝ => magneticFieldLevel (fieldScaleCovariance k (c t)) s i
  have hcpos (t : ℝ) : 0 < c t := Real.sqrt_pos.2 (Real.exp_pos t)
  have hg : Monotone g := by
    intro a b hab
    have hc : c a ≤ c b := Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hab)
    exact magneticFieldLevel_radial k (hcpos a) hc i hs
  have he : g = fun t : ℝ => magneticHeightLevel h s (r + (Real.exp t - 1) • r) i := by
    funext t
    have hvec : r + (Real.exp t - 1) • r = Real.exp t • r := by module
    have htR : r + (Real.exp t - 1) • r ∈ fieldStrictHeightCone h.depth := by
      rw [hvec]
      exact fieldStrictHeightCone_smul hrs (Real.exp_pos t)
    have hsq : (c t : ℝ) ^ 2 = Real.exp t := Real.sq_sqrt (Real.exp_pos t).le
    have heq : r + (Real.exp t - 1) • r = fun j => (c t : ℝ) ^ 2 * r j := by
      rw [hvec]
      funext j
      change Real.exp t * r j = (c t : ℝ) ^ 2 * r j
      rw [hsq]
    have hk : fieldStepOfStrictHeights h (r + (Real.exp t - 1) • r) htR =
        fieldScaleCovariance k (c t) := by
      unfold fieldStepOfStrictHeights fieldWithHeights fieldScaleCovariance k
      congr 1
    rw [magneticHeightLevel, dite_eq_left htR]
    exact (magneticFieldLevel_congr hk s i i rfl).symm
  have hd := hasDerivAt_magneticHeightLevel_line h F hI hU hs r r hr hrs i
  have hq : HasDerivAt (fun t : ℝ => Real.exp t - 1) 1 0 := by
    simpa only [Real.exp_zero] using (Real.hasDerivAt_exp 0).sub_const 1
  have hd' : HasDerivAt (fun t : ℝ => magneticHeightLevel h s (r + t • r) i)
      ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
        (∑ j, magneticHeightSchur h F s r i j * r j)) (Real.exp 0 - 1) := by
    simpa only [Real.exp_zero, sub_self] using hd
  have ht := hd'.comp 0 hq
  have hp : 0 ≤ (-2 / (h.cut i.succ - h.cut i.castSucc)) *
      (∑ j, magneticHeightSchur h F s r i j * r j) := by
    have hder : HasDerivAt g
        ((-2 / (h.cut i.succ - h.cut i.castSucc)) *
          (∑ j, magneticHeightSchur h F s r i j * r j)) 0 := by
      simpa only [he, Function.comp_def, mul_one] using ht
    exact hder.nonneg_of_monotone hg
  have hw : 0 < h.cut i.succ - h.cut i.castSucc :=
    sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)
  have hn : -2 / (h.cut i.succ - h.cut i.castSucc) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hw
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticOffDiagonalHessian
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed sign of the constrained height Hessian follows from the
actual positive coordinate variation. Together with radial monotonicity,
it gives the negative quadratic-form sign. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

private lemma deriv_nonpos_of_right_order {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hf, self_mem_nhdsWithin] with t ht hpos
  simpa only [zero_add, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (sub_nonpos.mpr ht)

theorem magneticHeightSchur_mixed_nonneg (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (i j : Fin (h.depth + 1)) (hij : i < j) :
    0 ≤ magneticHeightSchur h F s r i j := by
  have hd := hasDerivAt_magneticHeightLevel_line h F hI hU hs r
    (Pi.single j 1) hr hrs i
  have hn := deriv_nonpos_of_right_order hd
    (by simpa only [zero_smul, add_zero] using
      magneticHeightLevel_coordinate_right_order h hs r hrs i j hij)
  have he : (∑ k, magneticHeightSchur h F s r i k * (Pi.single j (1 : ℝ) : Fin (h.depth + 1) → ℝ) k) =
      magneticHeightSchur h F s r i j := by
    classical
    simp [Pi.single_apply]
  rw [he] at hn
  have hw : 0 < h.cut i.succ - h.cut i.castSucc :=
    sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)
  have hc : -2 / (h.cut i.succ - h.cut i.castSucc) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hw
  nlinarith

theorem magneticHeightSchur_quadratic_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ I) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (x : Fin (h.depth + 1) → ℝ) :
    ∑ i, ∑ j, magneticHeightSchur h F s r i j * x i * x j ≤ 0 := by
  let M := fun i j => -magneticHeightSchur h F s r i j
  have hsym : ∀ i j, M i j = M j i := fun i j =>
    congrArg Neg.neg (magneticHeightSchur_symmetric h F s r hr i j)
  have hoff : ∀ i j, i ≠ j → M i j ≤ 0 := by
    intro i j hij
    apply neg_nonpos.mpr
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact magneticHeightSchur_mixed_nonneg h F hI hU hs r hr hrs i j hlt
    · rw [magneticHeightSchur_symmetric h F s r hr i j]
      exact magneticHeightSchur_mixed_nonneg h F hI hU hs r hr hrs j i hgt
  have hpos : ∀ i, 0 < r i := by
    intro i
    have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hrs 0
    exact h0.trans_le ((fieldStrictHeightCone_strictMono hrs).monotone (Fin.zero_le i))
  have hrow : ∀ i, 0 ≤ ∑ j, M i j * r j := by
    intro i
    have he := magneticHeight_radial_hessian_nonpos h F hI hU hs r hr hrs i
    simpa only [M, neg_mul, Finset.sum_neg_distrib, neg_nonneg] using he
  have hq := field_quadratic_nonneg_of_positive_scaling M r hsym hoff hpos hrow x
  simpa only [M, neg_mul, Finset.sum_neg_distrib, neg_nonneg] using hq

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeightSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supporting plane for the actual finite constrained field on the
strict height cone. The optimizing bias is varied along the segment. -/

noncomputable section
open Set Filter
open scoped BigOperators

namespace InvariantIsing

private lemma magnetic_gradient_line_at (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (t : ℝ)
    (hr : r + t • d ∈ I) (hrs : r + t • d ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun q : ℝ =>
      (∑ i, F.P i (r + q • d, magneticHeightBias h s (r + q • d)) * d i) -
        d (Fin.last h.depth) / 2)
      (∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j) t := by
  have hi (i : Fin (h.depth + 1)) :=
    (hasDerivAt_magneticHeightP_line h F hI hU hs (r + t • d) d hr hrs i).mul_const (d i)
  have hd := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hi i)).sub_const
    (d (Fin.last h.depth) / 2)
  have heq : (∑ i, (∑ j, magneticHeightSchur h F s (r + t • d) i j * d j) * d i) =
      ∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hd
  have hd' : HasDerivAt (fun q : ℝ =>
      (∑ i, F.P i (r + t • d + q • d,
        magneticHeightBias h s (r + t • d + q • d)) * d i) - d (Fin.last h.depth) / 2)
      (∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j) (t - t) := by
    simpa only [sub_self, Finset.sum_apply] using hd
  have hc := hd'.comp (h := fun q : ℝ => q - t) t ((hasDerivAt_id t).sub_const t)
  have hv (q : ℝ) : r + t • d + (q - t) • d = r + q • d := by module
  simpa only [Function.comp_def, hv, mul_one] using hc

theorem magneticHeight_support_strict (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r q : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (hq : q ∈ fieldStrictHeightCone h.depth) :
    constrainedFieldValue (fieldStepOfStrictHeights h q hq) m ≤
      constrainedFieldValue (fieldStepOfStrictHeights h r hr) m +
        ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i) * (q i - r i) := by
  classical
  obtain ⟨lo, V, hlo, hrI, hqI⟩ := fieldHeightBox_pair r q hr hq
  let I := fieldHeightBox h.depth lo V
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  obtain ⟨F, hF⟩ := fieldHeightBox_family h lo V hlo
  let d := q - r
  let f := fun t : ℝ => constrainedHeightFieldValue h m (r + t • d)
  let g := fun t : ℝ =>
    (∑ i, F.P i (r + t • d, magneticHeightBias h m (r + t • d)) * d i) -
      d (Fin.last h.depth) / 2
  let z := fun t : ℝ => ∑ i, ∑ j,
    magneticHeightSchur h F m (r + t • d) i j * d i * d j
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • d ∈ I := by
    have he : r + t • d = (1 - t) • r + t • q := by dsimp only [d]; module
    rw [he]
    exact convex_fieldHeightBox _ _ _ hrI hqI (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hstrict (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      r + t • d ∈ fieldStrictHeightCone h.depth :=
    fieldHeightBox_subset_strict hlo.le (hp t ht)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g t) t :=
    hasDerivAt_constrainedHeightFieldValue_line_at h F hI hF hm r d t (hp t ht) (hstrict t ht)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (z t) t :=
    magnetic_gradient_line_at h F hI hF hm r d t (hp t ht) (hstrict t ht)
  have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z t ≤ 0 :=
    magneticHeightSchur_quadratic_nonpos h F hI hF hm _ (hp t ht) (hstrict t ht) d
  have hanti : AntitoneOn g (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hz t (interior_subset ht))
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv f t ≤ g 0 := by
    intro t ht
    rw [(hf t (interior_subset ht)).deriv]
    exact hanti (by simp) (interior_subset ht) (interior_subset ht).1
  have hsup := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) 1 (by simp) zero_le_one
  let G : Fin (h.depth + 1) → ℝ := fun i =>
    -(h.cut i.succ - h.cut i.castSucc) / 2 *
      magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i
  have hgrad (i : Fin (h.depth + 1)) :
      F.P i (r, magneticHeightBias h m r) =
        G i + (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0) := by
    have he := magneticHeight_optimized_gradient h F hF hm r hrI hr i
    dsimp only [G]
    linarith
  have hsum : (∑ i, F.P i (r, magneticHeightBias h m r) * d i) =
      (∑ i, G i * d i) + d (Fin.last h.depth) / 2 := by
    simp_rw [hgrad, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hg0 : g 0 = ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
      magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i) * (q i - r i) := by
    simp only [g, zero_smul, add_zero]
    change (∑ i, F.P i (r, magneticHeightBias h m r) * d i) -
      d (Fin.last h.depth) / 2 = ∑ i, G i * (q i - r i)
    rw [hsum, add_sub_cancel_right]
    rfl
  have he0 : f 0 = constrainedFieldValue (fieldStepOfStrictHeights h r hr) m := by
    simp only [f, zero_smul, add_zero, constrainedHeightFieldValue, dite_eq_left hr]
  have he1 : f 1 = constrainedFieldValue (fieldStepOfStrictHeights h q hq) m := by
    have he : r + (1 : ℝ) • d = q := by dsimp only [d]; module
    simp only [f, he, constrainedHeightFieldValue, dite_eq_left hq]
  rw [he0, he1, hg0] at hsup
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticClosedSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained supporting inequality on the full nonnegative height
cone, including repeated levels and zero variances. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem magneticHeight_support (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    constrainedFieldValue (fieldWithHeights h r hr0 hrmono) m ≤ constrainedFieldValue h m +
      ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticFieldLevel h m i) *
        (r i - h.height i) := by
  let k := fieldWithHeights h r hr0 hrmono
  have hleft := continuous_fieldRegularizedConstrainedValue k hm
  have hright : Continuous (fun t => constrainedFieldValue (fieldRegularized h t) m +
      ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i)) := by
    have hval := continuous_fieldRegularizedConstrainedValue h hm
    have hB := continuous_fieldRegularizedMagneticLevel h hm
    fun_prop
  have hineq : ∀ t ∈ Ioc (0 : ℝ) 1,
      constrainedFieldValue (fieldRegularized k t) m ≤
        constrainedFieldValue (fieldRegularized h t) m +
          ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
            magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i) := by
    intro t ht
    have hh : (fieldRegularized h t).height ∈ fieldStrictHeightCone h.depth :=
      fieldRegularized_strict h ht
    have hk : (fieldRegularized k t).height ∈ fieldStrictHeightCone h.depth :=
      fieldRegularized_strict k ht
    have heh : fieldStepOfStrictHeights h (fieldRegularized h t).height hh =
        fieldRegularized h t := by
      unfold fieldStepOfStrictHeights fieldRegularized fieldWithHeights
      rfl
    have hek : fieldStepOfStrictHeights h (fieldRegularized k t).height hk =
        fieldRegularized k t := by
      unfold fieldStepOfStrictHeights fieldRegularized fieldWithHeights k
      rfl
    have hi := magneticHeight_support_strict h hm _ _ hh hk
    have hevh := congrArg (fun q : FieldStep => constrainedFieldValue q m) heh
    have hevk := congrArg (fun q : FieldStep => constrainedFieldValue q m) hek
    rw [hevh, hevk] at hi
    have hd (i : Fin (h.depth + 1)) : (fieldRegularized k t).height i -
        (fieldRegularized h t).height i = r i - h.height i := by
      change (r i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) -
        (h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) = _
      ring
    have heBsum :
        (∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldStepOfStrictHeights h (fieldRegularized h t).height hh) m i) *
            ((fieldRegularized k t).height i - (fieldRegularized h t).height i)) =
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldRegularized h t) m i) *
            (r i - h.height i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [magneticFieldLevel_congr heh m i i rfl, hd]
    exact hi.trans_eq (congrArg
      (fun a : ℝ => constrainedFieldValue (fieldRegularized h t) m + a) heBsum)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      constrainedFieldValue (fieldRegularized k t) m ≤
        constrainedFieldValue (fieldRegularized h t) m +
          ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
            magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hineq t ⟨ht, ht1.le⟩
  have hh := le_of_tendsto_of_tendsto
    (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent
  have hz (i : Fin (h.depth + 1)) :=
    magneticFieldLevel_congr (fieldRegularized_zero h) m i i rfl
  simp_rw [hz] at hh
  simpa only [fieldRegularized_zero, k] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRefinement
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prescribed-magnetization values and conditional spin products are
unchanged by subdivision of a tied covariance interval. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma FieldRefines.biasMean {h k : FieldStep} (hk : FieldRefines h k) :
    fieldBiasMean k = fieldBiasMean h := by
  funext b
  have hd := hasDerivAt_fieldValue_bias k b
  have he : fieldValue k = fieldValue h := funext hk.value
  rw [he] at hd
  exact hd.unique (hasDerivAt_fieldValue_bias h b)

lemma FieldRefines.magneticBias {h k : FieldStep} (hk : FieldRefines h k) :
    magneticBias k = magneticBias h :=
  congrArg Function.invFun hk.biasMean

lemma FieldRefines.constrainedValue {h k : FieldStep} (hk : FieldRefines h k) (s : ℝ) :
    constrainedFieldValue k s = constrainedFieldValue h s := by
  unfold constrainedFieldValue magneticBiasObjective
  simp only [hk.value]

lemma fieldScalarSquareAt_magneticLevel (h : FieldStep) (b : ℝ)
    (i : Fin (h.depth + 1)) :
    fieldScalarSquareAt (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
      Real.tanh (i.val + 1) b = magneticLevelAtBias h b i := by
  rw [fieldScalarSquareAt_eq (fieldAllIncrements h) _ _
    ⟨i.val + 1, by rw [fieldAllIncrements_length]; omega⟩]
  exact (magneticLevelAtBias_allSquares h b i).symm

lemma magneticLevelAtBias_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (b : ℝ)
    (j : Fin (h.depth + 2)) :
    magneticLevelAtBias (fieldInsertCut h i c hc₀ hc₁) b j =
      magneticLevelAtBias h b (fieldSplitIndex i j) := by
  apply (fieldScalarSquareAt_magneticLevel (fieldInsertCut h i c hc₀ hc₁) b j).symm.trans
  rw [fieldAllIncrements_insertCut, fieldScalarSquareAt_insert_zero]
  have hp : ((fieldAllIncrements h).take (i.val + 1)).length = i.val + 1 := by
    rw [List.length_take, fieldAllIncrements_length, Nat.min_eq_left (by omega)]
  rw [hp, List.take_append_drop]
  rw [← fieldScalarSquareAt_magneticLevel]
  by_cases hj : j.val ≤ i.val
  · rw [ite_eq_left (show j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_true]
  · rw [ite_eq_right (show ¬j.val + 1 ≤ i.val + 1 by omega)]
    simp only [fieldSplitIndex, hj, dite_false]
    have hj0 : 0 < j.val := by omega
    congr 2
    omega

lemma magneticFieldLevel_insertCut (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (s : ℝ)
    (j : Fin (h.depth + 2)) :
    magneticFieldLevel (fieldInsertCut h i c hc₀ hc₁) s j =
      magneticFieldLevel h s (fieldSplitIndex i j) := by
  have hr : FieldRefines h (fieldInsertCut h i c hc₀ hc₁) :=
    FieldRefines.insert (FieldRefines.refl h) i c hc₀ hc₁
  unfold magneticFieldLevel
  rw [hr.magneticBias, magneticLevelAtBias_insertCut]

lemma magneticFieldPath_on_cell (h : FieldStep) (s : ℝ) (i : Fin (h.depth + 1))
    {t : ℝ} (ht : t ∈ Set.Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    magneticFieldPath h s t = magneticFieldLevel h s i :=
  fieldLevelPath_on_cell h _ _ _ i ht

lemma magneticFieldPath_insertCut_ae (h : FieldStep) (i : Fin (h.depth + 1)) (c : ℝ)
    (hc₀ : h.cut i.castSucc < c) (hc₁ : c < h.cut i.succ) (s : ℝ) :
    (magneticFieldPath (fieldInsertCut h i c hc₀ hc₁) s).val =ᵐ[pathMeasure]
      (magneticFieldPath h s).val := by
  filter_upwards [ae_finite_overlap_cell (fieldInsertCut h i c hc₀ hc₁).cut
    (fieldInsertCut h i c hc₀ hc₁).first (fieldInsertCut h i c hc₀ hc₁).last] with t ht
  obtain ⟨j, hj⟩ := ht
  have hi := fieldInsertCut_cell_subset h i c hc₀ hc₁ j hj
  rw [magneticFieldPath_on_cell _ s j hj,
    magneticFieldPath_on_cell h s (fieldSplitIndex i j) hi]
  exact magneticFieldLevel_insertCut h i c hc₀ hc₁ s j

lemma FieldRefines.magneticPath_ae {h k : FieldStep} (hk : FieldRefines h k) (s : ℝ) :
    (magneticFieldPath k s).val =ᵐ[pathMeasure] (magneticFieldPath h s).val := by
  induction hk with
  | refl => exact Filter.EventuallyEq.rfl
  | insert hk i c hc₀ hc₁ ih =>
    exact (magneticFieldPath_insertCut_ae _ i c hc₀ hc₁ s).trans ih

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted overlap path for the same field groups as the magnetic
variational functional. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal
namespace InvariantIsing

lemma magneticGroupPath_eq_sum {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (h : FieldStep) (s : ℝ) :
    magneticGroupPath γ mag hγ hγsum h s = ∑ a, γ a * magneticFieldPath h (mag a) s := by
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPartitionSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constrained scalar-field supporting inequality on arbitrary
finite partitions, expressed through the physical magnetic overlap path. -/

noncomputable section
open MeasureTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma magneticFieldPath_step_ae (h : FieldStep) (m : ℝ) :
    (magneticFieldPath h m).val =ᵐ[pathMeasure]
      finiteStepFunction h.cut (magneticFieldLevel h m) := by
  filter_upwards [ae_finite_overlap_cell h.cut h.first h.last] with s hs
  obtain ⟨i, hi⟩ := hs
  rw [magneticFieldPath_on_cell h m i hi,
    finiteStepFunction_on_cell h.ordered_cut _ hi]

lemma fieldPairing_magnetic_same (h : FieldStep) (m : ℝ)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldPairing (magneticFieldPath h m) (fieldWithHeights h r hr0 hrmono) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * r i := by
  change (∫ s, magneticFieldPath h m s * fieldFunction (fieldWithHeights h r hr0 hrmono) s
    ∂pathMeasure) = _
  calc
    _ = ∫ s, finiteStepFunction h.cut (magneticFieldLevel h m) s *
        finiteStepFunction h.cut r s ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [magneticFieldPath_step_ae h m] with s hs
      rw [hs]
      rfl
    _ = _ := integral_finiteStepFunction_mul h.cut h.ordered_cut h.first h.last _ _

lemma fieldPairing_magnetic_self (h : FieldStep) (m : ℝ) :
    fieldPairing (magneticFieldPath h m) h =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * h.height i := by
  have he : fieldWithHeights h h.height h.nonneg h.ordered_height = h := by
    cases h
    rfl
  simpa only [he] using fieldPairing_magnetic_same h m h.height h.nonneg h.ordered_height

lemma magneticField_support_same_partition (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    constrainedFieldValue (fieldWithHeights h r hr0 hrmono) m ≤ constrainedFieldValue h m -
      (1 / 2 : ℝ) * ∫ s, magneticFieldPath h m s *
        (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure := by
  have hi := magneticHeight_support h hm r hr0 hrmono
  have he : (∫ s, magneticFieldPath h m s *
      (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure) =
      fieldPairing (magneticFieldPath h m) (fieldWithHeights h r hr0 hrmono) -
        fieldPairing (magneticFieldPath h m) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he, fieldPairing_magnetic_same, fieldPairing_magnetic_self]
  have hsum : (∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticFieldLevel h m i) *
      (r i - h.height i)) = -(1 / 2 : ℝ) *
        ((∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * r i) -
          ∑ i, (h.cut i.succ - h.cut i.castSucc) * magneticFieldLevel h m i * h.height i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hi
  linarith

lemma magneticField_support_equal_cutList {h k : FieldStep} {m : ℝ} (hm : |m| < 1)
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    constrainedFieldValue k m ≤ constrainedFieldValue h m - (1 / 2 : ℝ) *
      ∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨r, hr0, hrmono, rfl⟩ := field_eq_withHeights_of_cutList he
  exact magneticField_support_same_partition h hm r hr0 hrmono

theorem magneticField_support (h k : FieldStep) {m : ℝ} (hm : |m| < 1) :
    constrainedFieldValue k m ≤ constrainedFieldValue h m - (1 / 2 : ℝ) *
      ∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨h', k', hh', hk', hcuts⟩ := field_common_refinement h k
  have hi := magneticField_support_equal_cutList hm hcuts
  rw [hh'.constrainedValue m, hk'.constrainedValue m] at hi
  have he : (∫ s, magneticFieldPath h' m s * (fieldFunction k' s - fieldFunction h' s)
      ∂pathMeasure) = ∫ s, magneticFieldPath h m s *
        (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [hh'.magneticPath_ae m, hh'.field_ae, hk'.field_ae] with s hB hh hk
    rw [hB, hh, hk]
  rwa [he] at hi

theorem magneticField_support_pairing (h k : FieldStep) {m : ℝ} (hm : |m| < 1) :
    constrainedFieldValue k m + (1 / 2 : ℝ) * fieldPairing (magneticFieldPath h m) k ≤
      constrainedFieldValue h m + (1 / 2 : ℝ) * fieldPairing (magneticFieldPath h m) h := by
  have hs := magneticField_support h k hm
  have he : (∫ s, magneticFieldPath h m s * (fieldFunction k s - fieldFunction h s)
      ∂pathMeasure) = fieldPairing (magneticFieldPath h m) k -
        fieldPairing (magneticFieldPath h m) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he] at hs
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupSupport
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supporting inequality for the weighted magnetic functional,
with the same common height path for all field groups. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma fieldPairing_magneticGroup {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (h k : FieldStep) :
    fieldPairing (magneticGroupPath γ mag hγ hγsum h) k =
      ∑ a, γ a * fieldPairing (magneticFieldPath h (mag a)) k := by
  unfold fieldPairing
  simp_rw [magneticGroupPath_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun a _ => (integrable_path_mul_field (magneticFieldPath h (mag a)) k).const_mul (γ a))]
  simp only [integral_const_mul]

lemma magneticGroup_support_pairing {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (hmag : ∀ a, |mag a|<1)
    (h k : FieldStep) :
    magneticGroupValue γ mag k + fieldPairing (magneticGroupPath γ mag hγ hγsum h) k/2 ≤
      magneticGroupValue γ mag h + fieldPairing (magneticGroupPath γ mag hγ hγsum h) h/2 := by
  have he (v : FieldStep) : magneticGroupValue γ mag v +
      fieldPairing (magneticGroupPath γ mag hγ hγsum h) v/2 =
      ∑ a, γ a * (constrainedFieldValue v (mag a) +
        (1/2 : ℝ)*fieldPairing (magneticFieldPath h (mag a)) v) := by
    rw [fieldPairing_magneticGroup]
    simp only [magneticGroupValue, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he k,he h]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
    (magneticField_support_pairing h k (hmag a)) (hγ a)

theorem magneticGroup_support {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (hmag : ∀ a, |mag a|<1)
    (h k : FieldStep) :
    magneticGroupValue γ mag k ≤ magneticGroupValue γ mag h -
      (∫ s, magneticGroupPath γ mag hγ hγsum h s *
        (fieldFunction k s-fieldFunction h s) ∂pathMeasure)/2 := by
  have hs := magneticGroup_support_pairing γ mag hγ hγsum hmag h k
  have he : (∫ s, magneticGroupPath γ mag hγ hγsum h s *
      (fieldFunction k s-fieldFunction h s) ∂pathMeasure) =
      fieldPairing (magneticGroupPath γ mag hγ hγsum h) k -
        fieldPairing (magneticGroupPath γ mag hγ hγsum h) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
    all_goals try with_reducible_and_instances rfl
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, sub_zero]
  field_simp [hx'.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-spectrum interaction energy and its monotonicity. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_finiteSpectralSlope (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) : Continuous (finiteSpectralSlope ρ eig hρ hρsum) := by
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    (continuous_projectedResolventDerivative ρ eig hρ hρsum a)

theorem finiteSpectralSlope_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    finiteSpectralSlope ρ eig hρ hρsum 0 = ∑ a, ρ a * eig a := by
  simp only [finiteSpectralSlope, projectedResolventDerivative, lt_self_iff_false, ite_false, if_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finiteSpectralSlope_bounds (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {l u : ℝ}
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u) (x : ℝ) :
    l ≤ finiteSpectralSlope ρ eig hρ hρsum x ∧ finiteSpectralSlope ρ eig hρ hρsum x ≤ u := by
  have hw := sum_projectedResolventDerivative ρ eig hρ hρsum x
  constructor
  · calc
      l = ∑ a, l * projectedResolventDerivative ρ eig hρ hρsum a x := by
        rw [← Finset.mul_sum, hw, mul_one]
      _ ≤ finiteSpectralSlope ρ eig hρ hρsum x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hl a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
  · calc
      finiteSpectralSlope ρ eig hρ hρsum x ≤
          ∑ a, u * projectedResolventDerivative ρ eig hρ hρsum a x := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hu a)
          (projectedResolventDerivative_pos ρ eig hρ hρsum a x).le
      _ = u := by rw [← Finset.mul_sum, hw, mul_one]

theorem sum_eig_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    (∑ a, eig a * projectedResolvent ρ eig hρ hρsum a x) =
      x * finiteR ρ eig hρ hρsum x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero,
      Finset.sum_const_zero, zero_mul]
  · let B := finiteInverse ρ eig hρ hρsum x
    have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hterm : ∀ a, eig a * (ρ a / (B - eig a)) = B * (ρ a / (B - eig a)) - ρ a := by
      intro a
      have hgap : B - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
      field_simp [hgap]
      ring
    simp only [projectedResolvent, finiteR, ite_eq_left h]
    change (∑ a, eig a * (ρ a / (B - eig a))) = x * (B - 1 / x)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hρsum]
    change B * finiteResolvent ρ eig B - 1 = x * (B - 1 / x)
    rw [hs.2]
    field_simp

theorem hasDerivWithinAt_mul_finiteR_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun y => y * finiteR ρ eig hρ hρsum y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
  have hd : HasDerivWithinAt
      (fun y => ∑ a, eig a * projectedResolvent ρ eig hρ hρsum a y)
      (finiteSpectralSlope ρ eig hρ hρsum x) (Ici 0) x := by
    convert! HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx).const_mul (eig a)) using 1
    all_goals try with_reducible_and_instances rfl
  exact hd.congr (fun y hy => (sum_eig_projectedResolvent ρ eig hρ hρsum hy).symm)
    (sum_eig_projectedResolvent ρ eig hρ hρsum hx).symm

theorem hasDerivWithinAt_finiteThermalScalar (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum t)
      (finiteSpectralSlope ρ eig hρ hρsum (t * x)) (Ici 0) x := by
  rcases ht.eq_or_lt with h | h
  · subst t
    rw [zero_mul, finiteSpectralSlope_zero]
    have hd := (hasDerivAt_id x).mul_const (∑ a, ρ a * eig a)
    convert! hd.hasDerivWithinAt using 1
    · funext y
      simp [finiteThermalScalar, finiteR]
    · simp
  · have hdH := hasDerivWithinAt_mul_finiteR_nonneg ρ eig hρ hρsum (mul_nonneg h.le hx)
    have hdlin : HasDerivWithinAt (fun y : ℝ => t * y) t (Ici 0) x := by
      convert! ((hasDerivAt_id x).const_mul t).hasDerivWithinAt using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hd := (hdH.comp x hdlin (fun y hy => mul_nonneg h.le hy)).const_mul (1 / t)
    convert! hd using 1
    · funext y
      dsimp [finiteThermalScalar, Function.comp_def]
      field_simp [h.ne']
    · field_simp [h.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEnergyPrimitive
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The temperature primitive of the finite-spectrum interaction energy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem integral_finiteSpectralSlope_temperature (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (∫ u in 0..t, finiteSpectralSlope ρ eig hρ hρsum (u * x)) =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  have hc : Continuous (finiteThermalScalar ρ eig hρ hρsum x) :=
    continuous_id.mul ((continuous_finiteR ρ eig hρ hρsum).comp
      (continuous_const.mul continuous_id))
  have hd : ∀ u ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (finiteThermalScalar ρ eig hρ hρsum x)
        (finiteSpectralSlope ρ eig hρ hρsum (u * x)) (Ioi u) u := by
    intro u hu
    have h := hasDerivWithinAt_finiteThermalScalar ρ eig hρ hρsum hx hu.1.le
    rw [mul_comm x u] at h
    exact h.mono fun y hy => (lt_trans hu.1 (show u < y from hy)).le
  have hint : IntervalIntegrable (fun u => finiteSpectralSlope ρ eig hρ hρsum (u * x))
      volume 0 t :=
    ((continuous_finiteSpectralSlope ρ eig hρ hρsum).comp
      (continuous_id.mul continuous_const)).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc.continuousOn hd hint
  simpa only [finiteThermalScalar, zero_mul, sub_zero, mul_comm x t] using hFTC

/-- Equation `up:primitive`, for the actual finite atomic spectral transform. -/
theorem integral_finiteInteractionEnergy (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {t : ℝ} (ht : 0 ≤ t) (p : OverlapPath) :
    (∫ u in 0..t, finiteInteractionEnergy ρ eig hρ hρsum u p) =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p := by
  let K := ∑ a, |eig a|
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    exact Finset.single_le_sum (f := fun a => |eig a|)
      (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hS : ∀ x, |finiteSpectralSlope ρ eig hρ hρsum x| ≤ K := by
    intro x
    exact abs_le.mpr (finiteSpectralSlope_bounds ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  let f : ℝ → ℝ → ℝ := fun u r => finiteSpectralSlope ρ eig hρ hρsum (u * deficit p r)
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 t) (max 0 t)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (Function.uncurry f) :=
    (continuous_finiteSpectralSlope ρ eig hρ hρsum).measurable.comp
      (measurable_fst.mul ((continuous_deficit p).measurable.comp measurable_snd))
  have hi : Integrable (Function.uncurry f) ((volume.restrict (uIoc 0 t)).prod pathMeasure) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      change ‖finiteSpectralSlope ρ eig hρ hρsum (z.1 * deficit p z.2)‖ ≤ K
      simpa only [Real.norm_eq_abs] using hS (z.1 * deficit p z.2)
  have hswap := intervalIntegral_integral_swap hi
  unfold finiteInteractionEnergy spectralFunctional
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in 0..t, ∫ r, f u r ∂pathMeasure) =
    (1 / 2 : ℝ) * ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact integral_finiteSpectralSlope_temperature ρ eig hρ hρsum ht (deficit_nonneg p hr.2.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTemperatureFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-spectrum temperature functional is a differentiable primitive
of the interaction energy, including at temperature zero. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteTemperatureFunctional_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {t : ℝ} (ht : 0 ≤ t) :
    finiteTemperatureFunctional ρ eig hρ hρsum p t =
      spectralFunctional (fun x => t * finiteR ρ eig hρ hρsum (t * x)) p :=
  integral_finiteInteractionEnergy ρ eig hρ hρsum ht p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPathLimit
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L1 approximation of the trial path preserves the finite spectral
interaction functional, as required when removing a finite partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma finiteTemperatureFunctional_tendsto_of_L1 {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun k => ∫ s, |q k s - p s| ∂pathMeasure) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => finiteTemperatureFunctional ρ eig hρ hρsum (q k) t) atTop
      (𝓝 (finiteTemperatureFunctional ρ eig hρ hρsum p t)) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun b _ => abs_nonneg (eig b)) (Finset.mem_univ a)
  have hbound (x : ℝ) : |finiteR ρ eig hρ hρsum x| ≤ K :=
    abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hd (r : ℝ) : Tendsto (fun k => deficit (q k) r) atTop (𝓝 (deficit p r)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ hL
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [Real.norm_eq_abs] using abs_deficit_sub_path_le (q k) p r)
  have hi : Tendsto (fun k => ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit (q k) r)
      ∂pathMeasure) atTop
      (𝓝 (∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => t * K)
    · intro k
      exact (continuous_const.mul ((continuous_finiteR ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit (q k))))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left (hbound _) ht)
    · exact ae_of_all _ (fun r =>
        (((continuous_finiteR ρ eig hρ hρsum).tendsto _).comp ((hd r).const_mul t)).const_mul t)
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ ht,
    spectralFunctional] using hi.const_mul (1 / 2 : ℝ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTrialLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the magnetic cavity trial from weighted
self-consistency and its supporting inequality. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_entropy_trial_tendsto_of_support {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s *
        (fieldFunction k s-fieldFunction (h n) s) ∂pathMeasure)/2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
      spectralFunctional (finiteR ρ eig hρ hsum) (q n)) atTop
      (𝓝 ((magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p)) := by
  obtain ⟨htop,hent⟩ := magnetic_entropy_sequence_of_support γ mag hγ hγsum hmag p h hC hsupport hself
  have hpair := field_pairing_path_tendsto p q h hC hq
  have hspec := finiteTemperatureFunctional_tendsto_of_L1 ρ eig hρ hsum p q hq zero_le_one
  simp only [finiteTemperatureFunctional_eq ρ eig hρ hsum _ zero_le_one,one_mul] at hspec
  refine ⟨htop,?_⟩
  have ht := (hent.add (hpair.div_const 2)).add hspec
  have he : (fun n => (magneticGroupValue γ mag (h n) + fieldPairing p (h n)/2 +
      (fieldPairing (q n) (h n)-fieldPairing p (h n))/2) +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) =
      (fun n => magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
        spectralFunctional (finiteR ρ eig hρ hsum) (q n)) := by
    funext n
    ring
  rw [he] at ht
  simpa only [zero_div,add_zero] using ht

theorem magnetic_entropy_trial_eventually_lower_of_support {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s *
        (fieldFunction k s-fieldFunction (h n) s) ∂pathMeasure)/2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal - ε ≤
        magneticGroupValue γ mag (h n) + fieldPairing (q n) (h n)/2 +
          spectralFunctional (finiteR ρ eig hρ hsum) (q n) := by
  obtain ⟨htop,ht⟩ := magnetic_entropy_trial_tendsto_of_support
    ρ eig hρ hsum γ mag hγ hγsum hmag p q h hC hsupport hself hq
  have hbot : magneticEntropyFunctional γ mag p ≠ ⊥ := ne_bot_of_le_ne_bot
    (EReal.coe_ne_bot _) (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
  have hfinite := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum hmag
  have hi := iInf_le (fun v : OverlapPath => magneticEntropyFunctional γ mag v +
    (spectralFunctional (finiteR ρ eig hρ hsum) v : EReal)) p
  change magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag ≤ _ at hi
  rw [← EReal.coe_toReal hfinite.1 hfinite.2, ← EReal.coe_toReal htop hbot,
    ← EReal.coe_add] at hi
  have hi' : (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal ≤
      (magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p := by
    exact_mod_cast hi
  intro ε hε
  have he := ht.eventually (lt_mem_nhds (show
    (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal - ε <
      (magneticEntropyFunctional γ mag p).toReal + spectralFunctional (finiteR ρ eig hρ hsum) p by linarith))
  exact he.mono (fun _ h => h.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticEntropyMaximum
attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Magnetic entropy identification from the proved scalar supporting
inequality, with no additional concavity premise. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_entropy_trial_eventually_lower_oai {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1) (p : OverlapPath) (q : ℕ → OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s-p s|
      ∂pathMeasure) atTop (𝓝 0))
    (hq : Tendsto (fun n => ∫ s, |q n s-p s| ∂pathMeasure) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal-ε ≤
        magneticGroupValue γ mag (h n)+fieldPairing (q n) (h n)/2+
          spectralFunctional (finiteR ρ eig hρ hsum) (q n) :=
  magnetic_entropy_trial_eventually_lower_of_support ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).le) p q h hC
    (fun n k => magneticGroup_support γ mag hγ hγsum hmag (h n) k) hself hq

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower_oai.{u_1, u_2} := @OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower_oai.{u_1, u_2}
