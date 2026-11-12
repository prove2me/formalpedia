-- Prove2me | solution 1 for OAI.InvariantIsing.field_support_equal_cutList
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:57.273543+00:00
-- url     : https://prove2.me/submissions/d732d19b-484d-4299-b49e-5fa9caa45642

import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldLikelihoodRatio
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered likelihood-ratio comparison used by the folded Gaussian
transitions of the one-site Ising field recursion. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

/-- Ordered likelihood ratios increase every integrable increasing test.
The reference measure is supported on nonnegative absolute positions. -/
theorem field_likelihood_ratio_expectation_le
    (μ : Measure ℝ) [SFinite μ] (w₀ w₁ f : ℝ → ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hf : MonotoneOn f (Ici 0))
    (hcross : ∀ x ∈ Ici (0 : ℝ), ∀ y ∈ Ici (0 : ℝ), x ≤ y →
      w₁ x * w₀ y ≤ w₁ y * w₀ x)
    (hw₀ : Integrable w₀ μ) (hw₁ : Integrable w₁ μ)
    (hfw₀ : Integrable (fun x => f x * w₀ x) μ)
    (hfw₁ : Integrable (fun x => f x * w₁ x) μ)
    (hm₀ : 0 < ∫ x, w₀ x ∂μ) (hm₁ : 0 < ∫ x, w₁ x ∂μ) :
    (∫ x, f x * w₀ x ∂μ) / (∫ x, w₀ x ∂μ) ≤
      (∫ x, f x * w₁ x ∂μ) / (∫ x, w₁ x ∂μ) := by
  let K : ℝ × ℝ → ℝ := fun z =>
    (f z.1 * w₁ z.1) * w₀ z.2 + w₀ z.1 * (f z.2 * w₁ z.2) -
      (f z.1 * w₀ z.1) * w₁ z.2 - w₁ z.1 * (f z.2 * w₀ z.2)
  have hsupport : ∀ᵐ z ∂μ.prod μ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_Ici.preimage measurable_fst).inter
        (measurableSet_Ici.preimage measurable_snd))).mpr
    filter_upwards [hμ] with x hx
    filter_upwards [hμ] with y hy
    exact ⟨hx, hy⟩
  have hK : 0 ≤ ∫ z, K z ∂μ.prod μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hsupport] with z hz
    have he : K z = (f z.1 - f z.2) * (w₁ z.1 * w₀ z.2 - w₀ z.1 * w₁ z.2) := by
      dsimp only [K]
      ring
    rw [he]
    rcases le_total z.1 z.2 with hxy | hyx
    · apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (hf hz.1 hz.2 hxy)
      · have h := hcross z.1 hz.1 z.2 hz.2 hxy
        nlinarith
    · apply mul_nonneg
      · exact sub_nonneg.mpr (hf hz.2 hz.1 hyx)
      · have h := hcross z.2 hz.2 z.1 hz.1 hyx
        nlinarith
  have hI₁ := hfw₁.mul_prod hw₀
  have hI₂ := hw₀.mul_prod hfw₁
  have hI₃ := hfw₀.mul_prod hw₁
  have hI₄ := hw₁.mul_prod hfw₀
  have hI₁₂ : Integrable (fun z : ℝ × ℝ => (f z.1 * w₁ z.1) * w₀ z.2 +
      w₀ z.1 * (f z.2 * w₁ z.2)) (μ.prod μ) := hI₁.add hI₂
  have hI₁₂₃ : Integrable (fun z : ℝ × ℝ => (f z.1 * w₁ z.1) * w₀ z.2 +
      w₀ z.1 * (f z.2 * w₁ z.2) - (f z.1 * w₀ z.1) * w₁ z.2) (μ.prod μ) := hI₁₂.sub hI₃
  have he : (∫ z, K z ∂μ.prod μ) =
      2 * ((∫ x, f x * w₁ x ∂μ) * (∫ x, w₀ x ∂μ) -
        (∫ x, f x * w₀ x ∂μ) * (∫ x, w₁ x ∂μ)) := by
    dsimp only [K]
    rw [integral_sub hI₁₂₃ hI₄, integral_sub hI₁₂ hI₃, integral_add hI₁ hI₂]
    rw [integral_prod_mul (fun x => f x * w₁ x) w₀,
      integral_prod_mul w₀ (fun x => f x * w₁ x),
      integral_prod_mul (fun x => f x * w₀ x) w₁,
      integral_prod_mul w₁ (fun x => f x * w₀ x)]
    ring
  rw [he] at hK
  apply (div_le_div_iff₀ hm₀ hm₁).mpr
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFoldedKernel
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered folded Gaussian densities. These are the one-step comparisons
used in both the mixed and radial Ising-field derivatives. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma field_tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  have hs : 0 ≤ Real.sinh (y - x) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hxy)
  rw [Real.sinh_sub] at hs
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  exact (div_le_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)).mpr (by nlinarith)

lemma field_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using field_tanh_monotone hx

lemma field_scaled_tanh_mono {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) :
    a * Real.tanh (a * u) ≤ b * Real.tanh (b * u) := by
  exact mul_le_mul hab (field_tanh_monotone (mul_le_mul_of_nonneg_right hab hu))
    (field_tanh_nonneg (mul_nonneg ha hu)) (ha.trans hab)

lemma hasDerivAt_field_logcosh_mul (a x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.cosh (a * z))) (a * Real.tanh (a * x)) x := by
  have h := (((Real.hasDerivAt_cosh (a * x)).comp x
    ((hasDerivAt_id x).const_mul a)).log (Real.cosh_pos (a * x)).ne')
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_apply, mul_one, Real.tanh_eq_sinh_div_cosh]
  ring

/-- Increasing the scale makes the log-cosh payoff difference even and
nondecreasing on the positive half-line. -/
lemma field_logcosh_scaled_difference_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MonotoneOn (fun u => Real.log (Real.cosh (b * u)) - Real.log (Real.cosh (a * u))) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).log
      (fun _ => (Real.cosh_pos _).ne')).continuousOn.sub
        (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).log
          (fun _ => (Real.cosh_pos _).ne')).continuousOn)
  · intro x _
    exact ((hasDerivAt_field_logcosh_mul b x).sub
      (hasDerivAt_field_logcosh_mul a x)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt (fun u => Real.log (Real.cosh (b * u)) -
        Real.log (Real.cosh (a * u))) (b * Real.tanh (b * x) - a * Real.tanh (a * x)) x :=
      (hasDerivAt_field_logcosh_mul b x).sub (hasDerivAt_field_logcosh_mul a x)
    rw [hd.deriv]
    exact sub_nonneg.mpr (field_scaled_tanh_mono ha hab (le_of_lt hx))

lemma field_cosh_ratio_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MonotoneOn (fun u => Real.cosh (b * u) / Real.cosh (a * u)) (Ici 0) := by
  intro x hx y hy hxy
  have he := Real.exp_le_exp.mpr
    (field_logcosh_scaled_difference_monotone ha hab hx hy hxy)
  simpa only [Real.exp_sub, Real.exp_log (Real.cosh_pos _)] using he

lemma fieldFoldedWeight_pos (v ζ : ℝ) (F : ℝ → ℝ) (z u : ℝ) :
    0 < fieldFoldedWeight v ζ F z u :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _)) (Real.exp_pos _)

/-- The exact likelihood-ratio order in the absolute parent position. -/
lemma fieldFoldedWeight_parent_order {v : ℝ} (hv : 0 < v) (ζ : ℝ) (F : ℝ → ℝ)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁)
    {u₀ u₁ : ℝ} (hu₀ : 0 ≤ u₀) (huu : u₀ ≤ u₁) :
    fieldFoldedWeight v ζ F z₁ u₀ * fieldFoldedWeight v ζ F z₀ u₁ ≤
      fieldFoldedWeight v ζ F z₁ u₁ * fieldFoldedWeight v ζ F z₀ u₀ := by
  have hr := field_cosh_ratio_monotone (div_nonneg hz₀ hv.le)
    ((div_le_div_iff_of_pos_right hv).mpr hzz) hu₀ (hu₀.trans huu) huu
  have hc := (div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)).mp hr
  let C := Real.exp (-u₀ ^ 2 / (2 * v)) * Real.exp (ζ * F u₀) *
    (Real.exp (-u₁ ^ 2 / (2 * v)) * Real.exp (ζ * F u₁))
  have hC : 0 ≤ C := (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
    (mul_pos (Real.exp_pos _) (Real.exp_pos _))).le
  convert! mul_le_mul_of_nonneg_left hc hC using 1 <;>
    dsimp only [fieldFoldedWeight, C] <;> ring

/-- Increasing the even payoff by an increasing function raises the
folded transition in likelihood-ratio order. -/
lemma fieldFoldedWeight_payoff_order (v : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (z : ℝ) {u₀ u₁ : ℝ} (hu₀ : 0 ≤ u₀) (huu : u₀ ≤ u₁) :
    fieldFoldedWeight v ζ G z u₀ * fieldFoldedWeight v ζ F z u₁ ≤
      fieldFoldedWeight v ζ G z u₁ * fieldFoldedWeight v ζ F z u₀ := by
  have hdiff := mul_le_mul_of_nonneg_left (hFG hu₀ (hu₀.trans huu) huu) hζ
  have he : Real.exp (ζ * G u₀ + ζ * F u₁) ≤ Real.exp (ζ * G u₁ + ζ * F u₀) :=
    Real.exp_le_exp.mpr (by nlinarith)
  let C := Real.exp (-u₀ ^ 2 / (2 * v)) * Real.cosh ((z / v) * u₀) *
    (Real.exp (-u₁ ^ 2 / (2 * v)) * Real.cosh ((z / v) * u₁))
  have hC : 0 ≤ C := (mul_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
    (mul_pos (Real.exp_pos _) (Real.cosh_pos _))).le
  rw [Real.exp_add, Real.exp_add] at he
  convert! mul_le_mul_of_nonneg_left he hC using 1 <;>
    dsimp only [fieldFoldedWeight, C] <;> ring

/-- The parent comparison acts on every bounded increasing test under the
actual folded density, after its Gaussian integrability is supplied. -/
theorem fieldFolded_parent_expectation_le {v : ℝ} (hv : 0 < v)
    (ζ : ℝ) (F f : ℝ → ℝ) (hf : Measurable f)
    (hmono : MonotoneOn f (Ici 0)) {C : ℝ} (hbound : ∀ u, |f u| ≤ C)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁)
    (h₀ : Integrable (fieldFoldedWeight v ζ F z₀) (volume.restrict (Ici 0)))
    (h₁ : Integrable (fieldFoldedWeight v ζ F z₁) (volume.restrict (Ici 0)))
    (hm₀ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z₀ u)
    (hm₁ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z₁ u) :
    (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z₀ u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z₀ u) ≤
      (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z₁ u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z₁ u) := by
  have hb : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), ‖f u‖ ≤ C :=
    Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) _ _ f
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun x hx y _hxy hxy => fieldFoldedWeight_parent_order hv ζ F hz₀ hzz hx hxy)
    h₀ h₁ (h₀.bdd_mul hf.aestronglyMeasurable hb)
    (h₁.bdd_mul hf.aestronglyMeasurable hb) hm₀ hm₁

/-- The payoff comparison acts on the same bounded increasing tests. -/
theorem fieldFolded_payoff_expectation_le (v : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G f : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hf : Measurable f) (hmono : MonotoneOn f (Ici 0))
    {C : ℝ} (hbound : ∀ u, |f u| ≤ C) (z : ℝ)
    (h₀ : Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)))
    (h₁ : Integrable (fieldFoldedWeight v ζ G z) (volume.restrict (Ici 0)))
    (hm₀ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z u)
    (hm₁ : 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ G z u) :
    (∫ u in Ici 0, f u * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ F z u) ≤
      (∫ u in Ici 0, f u * fieldFoldedWeight v ζ G z u) /
        (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) := by
  have hb : ∀ᵐ u ∂volume.restrict (Ici (0 : ℝ)), ‖f u‖ ≤ C :=
    Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) _ _ f
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun x hx y _hy hxy => fieldFoldedWeight_payoff_order v hζ F G hFG z hx hxy)
    h₀ h₁ (h₀.bdd_mul hf.aestronglyMeasurable hb)
    (h₁.bdd_mul hf.aestronglyMeasurable hb) hm₀ hm₁

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFoldedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Gaussian folding and conditional sign factors. These identities
supply the folded transition and spin-mean kernel used in fld:radial. -/

noncomputable section
open scoped NNReal
open ProbabilityTheory

namespace InvariantIsing

lemma field_gaussian_pair_sum (v : ℝ≥0) (hv : v ≠ 0) (z u : ℝ) :
    gaussianPDFReal z v u + gaussianPDFReal z v (-u) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        (Real.exp (-u ^ 2 / (2 * v)) * Real.cosh ((z / v) * u)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have he₁ : -(u - z) ^ 2 / (2 * (v : ℝ)) =
      -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + (z / v) * u := by
    field_simp [hv']
    ring
  have he₂ : -(-u - z) ^ 2 / (2 * (v : ℝ)) =
      -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + -((z / v) * u) := by
    field_simp [hv']
    ring
  simp only [gaussianPDFReal, he₁, he₂, Real.exp_add, Real.cosh_eq]
  ring

lemma field_gaussian_pair_sign (v : ℝ≥0) (hv : v ≠ 0) (z u : ℝ) :
    gaussianPDFReal z v u - gaussianPDFReal z v (-u) =
      Real.tanh ((z / v) * u) * (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  let t := (z / (v : ℝ)) * u
  let C := (Real.sqrt (2 * Real.pi * v))⁻¹ *
    Real.exp (-z ^ 2 / (2 * (v : ℝ))) * Real.exp (-u ^ 2 / (2 * (v : ℝ)))
  have he₁ : gaussianPDFReal z v u = C * Real.exp t := by
    have he : -(u - z) ^ 2 / (2 * (v : ℝ)) =
        -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + t := by
      dsimp only [t]
      field_simp [hv']
      ring
    simp only [gaussianPDFReal, he, Real.exp_add, C]
    ring
  have he₂ : gaussianPDFReal z v (-u) = C * Real.exp (-t) := by
    have he : -(-u - z) ^ 2 / (2 * (v : ℝ)) =
        -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + -t := by
      dsimp only [t]
      field_simp [hv']
      ring
    simp only [gaussianPDFReal, he, Real.exp_add, C]
    ring
  rw [he₁, he₂]
  change C * Real.exp t - C * Real.exp (-t) =
    Real.tanh t * (C * Real.exp t + C * Real.exp (-t))
  rw [Real.tanh_eq]
  field_simp [(add_pos (Real.exp_pos t) (Real.exp_pos (-t))).ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianFolding
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian integral form of the folded one-site transition. -/

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma field_integral_fold (g : ℝ → ℝ) (hg : Integrable g volume) :
    (∫ x, g x) = ∫ u in Ici (0 : ℝ), g u + g (-u) := by
  have he : (fun u => (Iic (0 : ℝ)).indicator g (-u)) =
      (Ici (0 : ℝ)).indicator (fun u => g (-u)) := by
    funext u
    simp only [Set.indicator, mem_Iic, mem_Ici, neg_nonpos]
  have hn := integral_neg_eq_self ((Iic (0 : ℝ)).indicator g) volume
  rw [he, integral_indicator measurableSet_Ici, integral_indicator measurableSet_Iic] at hn
  rw [integral_add hg.integrableOn hg.comp_neg.integrableOn, hn, integral_Ici_eq_integral_Ioi]
  calc
    (∫ x, g x) = (∫ x in Iic 0, g x) + ∫ x in Ioi 0, g x := by
      simpa only [compl_Iic] using (integral_add_compl (s := Iic 0) measurableSet_Iic hg).symm
    _ = _ := add_comm _ _

lemma field_gaussian_density_integrable (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ)
    (f : ℝ → ℝ) (hf : Integrable f (gaussianReal z v)) :
    Integrable (fun u => gaussianPDFReal z v u * f u) volume := by
  rw [gaussianReal_of_var_ne_zero z hv] at hf
  have he := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF z v) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using he

/-- Folding a Gaussian with an even terminal tilt gives precisely the
positive-half-line density used in the likelihood-ratio comparison. -/
theorem field_gaussian_folded_integral (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * f |u| ∂gaussianReal z v) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        ∫ u in Ici (0 : ℝ), f u * fieldFoldedWeight v ζ F z u := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * f |u|)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hf
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ u, g u) = _
  rw [field_integral_fold g hg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u hu
  dsimp only [g]
  rw [abs_of_nonneg hu, abs_neg, abs_of_nonneg hu, hF u]
  have he := field_gaussian_pair_sum v hv z u
  change _ = C * (f u * fieldFoldedWeight v ζ F z u)
  calc
    _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) *
        (Real.exp (ζ * F u) * f u) := by ring
    _ = _ := by rw [he]; dsimp only [fieldFoldedWeight, C] <;> ring

lemma field_folded_constant_pos (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    0 < 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v)) := by
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  positivity

/-- Gaussian exponential integrability supplies the folded density's
integrability; no separate density-tail assumption is needed. -/
lemma fieldFoldedWeight_integrable (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F : ℝ → ℝ) (hF : Function.Even F)
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)) := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * Real.exp (ζ * F u)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hweight
  have hi : Integrable (fun u => g u + g (-u)) (volume.restrict (Ici 0)) :=
    hg.integrableOn.add hg.comp_neg.integrableOn
  have he : (fun u => g u + g (-u)) =ᵐ[volume.restrict (Ici 0)]
      (fun u => C * fieldFoldedWeight v ζ F z u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u _hu
    dsimp only [g]
    rw [hF u]
    have hp := field_gaussian_pair_sum v hv z u
    calc
      _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) * Real.exp (ζ * F u) := by ring
      _ = _ := by rw [hp]; dsimp only [C, fieldFoldedWeight] <;> ring
  have hc : C ≠ 0 := (field_folded_constant_pos v hv z).ne'
  have hi' := (hi.congr he).const_mul C⁻¹
  simpa only [Pi.mul_apply, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi'

lemma fieldFoldedWeight_mass_pos (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F : ℝ → ℝ) (hF : Function.Even F)
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    0 < ∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u := by
  have hi := fieldFoldedWeight_integrable v hv z ζ F hF hweight
  apply (integral_pos_iff_support_of_nonneg (fun u => (fieldFoldedWeight_pos v ζ F z u).le) hi).mpr
  have he : Function.support (fieldFoldedWeight v ζ F z) = univ := by
    ext u
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (fieldFoldedWeight_pos v ζ F z u).ne'
  rw [he, Measure.restrict_apply_univ]
  simp

lemma field_gaussian_folded_ratio (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v))
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * f |u| ∂gaussianReal z v) /
        (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) =
      (∫ u in Ici (0 : ℝ), f u * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u) := by
  have hn := field_gaussian_folded_integral v hv z ζ F f hF hf
  have hd := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hF
    (by simpa only [mul_one] using hweight)
  simp only [mul_one, one_mul] at hd
  rw [hn, hd, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The folded likelihood comparison for the actual Gaussian tilted
transition, with its integrability discharged by linear growth. -/

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

private lemma field_test_exp_integrable (v : ℝ≥0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ u, |f u| ≤ C) :
    Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v) := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ
  have hi := hw.bdd_mul (hf.comp measurable_abs).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hbound |u|))
  simpa only [Function.comp_apply, mul_comm] using hi

/-- Absolute child position is stochastically increasing in a nonnegative
parent position under an arbitrary even linearly growing payoff. -/
theorem field_gaussian_tilt_abs_parent_order (v : ℝ≥0) (hv : v ≠ 0) (ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (hf : Measurable f)
    (hmono : MonotoneOn f (Ici 0)) {C : ℝ} (hbound : ∀ u, |f u| ≤ C)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁) :
    (∫ u, f |u| ∂(gaussianReal z₀ v).tilted (fun u => ζ * F u)) ≤
      (∫ u, f |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * F u)) := by
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hw (z : ℝ) : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hgrowth ζ
  rw [integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_folded_ratio v hv z₀ ζ F f hFeven
      (field_test_exp_integrable v z₀ ζ F f hF hgrowth hf hbound) (hw z₀),
    field_gaussian_folded_ratio v hv z₁ ζ F f hFeven
      (field_test_exp_integrable v z₁ ζ F f hF hgrowth hf hbound) (hw z₁)]
  exact fieldFolded_parent_expectation_le hvp ζ F f hf hmono hbound hz₀ hzz
    (fieldFoldedWeight_integrable v hv z₀ ζ F hFeven (hw z₀))
    (fieldFoldedWeight_integrable v hv z₁ ζ F hFeven (hw z₁))
    (fieldFoldedWeight_mass_pos v hv z₀ ζ F hFeven (hw z₀))
    (fieldFoldedWeight_mass_pos v hv z₁ ζ F hFeven (hw z₁))

/-- Adding an even payoff which increases in absolute position raises the
actual absolute-position transition. -/
theorem field_gaussian_tilt_abs_payoff_order (v : ℝ≥0) (hv : v ≠ 0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G f : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hf : Measurable f) (hmono : MonotoneOn f (Ici 0))
    {C : ℝ} (hbound : ∀ u, |f u| ≤ C) (z : ℝ) :
    (∫ u, f |u| ∂(gaussianReal z v).tilted (fun u => ζ * F u)) ≤
      (∫ u, f |u| ∂(gaussianReal z v).tilted (fun u => ζ * G u)) := by
  have hwF : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hFgrowth ζ
  have hwG : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hG hGgrowth ζ
  rw [integral_tilted_eq_div, integral_tilted_eq_div,
    field_gaussian_folded_ratio v hv z ζ F f hFeven
      (field_test_exp_integrable v z ζ F f hF hFgrowth hf hbound) hwF,
    field_gaussian_folded_ratio v hv z ζ G f hGeven
      (field_test_exp_integrable v z ζ G f hG hGgrowth hf hbound) hwG]
  exact fieldFolded_payoff_expectation_le v hζ F G f hFG hf hmono hbound z
    (fieldFoldedWeight_integrable v hv z ζ F hFeven hwF)
    (fieldFoldedWeight_integrable v hv z ζ G hGeven hwG)
    (fieldFoldedWeight_mass_pos v hv z ζ F hFeven hwF)
    (fieldFoldedWeight_mass_pos v hv z ζ G hGeven hwG)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianTransformLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact one-step Gaussian operator laws used to propagate the radial
comparison through the finite Ising field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_even_abs {F : ℝ → ℝ} (hF : Function.Even F) (u : ℝ) : F |u| = F u := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, hF u]

lemma field_gaussian_integral_reflect (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    (∫ u, F u ∂gaussianReal (-z) v) = ∫ u, F u ∂gaussianReal z v := by
  have hm : (gaussianReal z v).map (fun u => -u) = gaussianReal (-z) v :=
    gaussianReal_map_neg

  rw [← hm, integral_map measurable_neg.aemeasurable hF.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall hEven)

lemma gaussianOperator_even (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    Function.Even (gaussianOperator ζ v F) := by
  intro z
  by_cases hζ : ζ = 0
  · subst ζ
    rw [gaussianOperator_eq_gaussian_integral v hF,
      gaussianOperator_eq_gaussian_integral v hF,
      field_gaussian_integral_reflect v z hF hEven]
  · rw [gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
        (fun u => by rw [hEven u])]

lemma field_linearGrowth_sub {F G : ℝ → ℝ} (hF : HasLinearGrowth F)
    (hG : HasLinearGrowth G) : HasLinearGrowth (fun u => G u - F u) := by
  obtain ⟨CF, LF, hCF, hLF, hF⟩ := hF
  obtain ⟨CG, LG, hCG, hLG, hG⟩ := hG
  refine ⟨CG + CF, LG + LF, add_nonneg hCG hCF, add_nonneg hLG hLF, ?_⟩
  intro u
  calc
    |G u - F u| ≤ |G u| + |F u| := abs_sub _ _
    _ ≤ (CG + LG * ‖u‖) + (CF + LF * ‖u‖) := add_le_add (hG u) (hF u)
    _ = _ := by ring

/-- Gaussian integrability of an even-test tilt supplies integrability of
its folded numerator, also for unbounded linearly growing tests. -/
lemma field_folded_test_integrable (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v)) :
    Integrable (fun u => f u * fieldFoldedWeight v ζ F z u) (volume.restrict (Ici 0)) := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * f |u|)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hf
  have hi : Integrable (fun u => g u + g (-u)) (volume.restrict (Ici 0)) :=
    hg.integrableOn.add hg.comp_neg.integrableOn
  have he : (fun u => g u + g (-u)) =ᵐ[volume.restrict (Ici 0)]
      (fun u => C * (f u * fieldFoldedWeight v ζ F z u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    dsimp only [g]
    rw [abs_of_nonneg hu, abs_neg, abs_of_nonneg hu, hF u]
    have hp := field_gaussian_pair_sum v hv z u
    calc
      _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) *
          (Real.exp (ζ * F u) * f u) := by ring
      _ = _ := by rw [hp]; dsimp only [C, fieldFoldedWeight] <;> ring
  have hc : C ≠ 0 := (field_folded_constant_pos v hv z).ne'
  have hi' := (hi.congr he).const_mul C⁻¹
  simpa only [Pi.mul_apply, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact odd-observable law for an even Gaussian tilt. This is the
conditional-spin kernel in the radial field comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussian_odd_folded_integral (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Function.Even F) (ha : Function.Odd a)
    (hi : Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal z v) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        ∫ u in Ici (0 : ℝ), (a u * Real.tanh ((z / v) * u)) * fieldFoldedWeight v ζ F z u := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * a u)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hi
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ u, g u) = _
  rw [field_integral_fold g hg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u _hu
  dsimp only [g]
  rw [hF u, ha u]
  have he := field_gaussian_pair_sign v hv z u
  have hp := field_gaussian_pair_sum v hv z u
  calc
    _ = (gaussianPDFReal z v u - gaussianPDFReal z v (-u)) *
        (Real.exp (ζ * F u) * a u) := by ring
    _ = _ := by rw [he, hp]; dsimp only [C, fieldFoldedWeight] <;> ring

/-- The physical odd conditional spin observable equals the folded
observable multiplied by the exact conditional sign. -/
theorem field_gaussian_tilt_odd_integral_eq_folded (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Function.Even F) (ha : Function.Odd a)
    (hi : Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v))
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    (∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)) =
      (∫ u in Ici (0 : ℝ), (a u * Real.tanh ((z / v) * u)) * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u) := by
  rw [integral_tilted_eq_div]
  have hn := field_gaussian_odd_folded_integral v hv z ζ F a hF ha hi
  have hd := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hF
    (by simpa only [mul_one] using hweight)
  simp only [mul_one, one_mul] at hd
  rw [hn, hd, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinKernelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity of the physical conditional-spin transition. This keeps
the spin observable, rather than the derivative in rescaled coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_spin_test_measurable {a : ℝ → ℝ} (ha : Measurable a) (v z : ℝ) :
    Measurable (fun u => a u * Real.tanh ((z / v) * u)) := by
  simp only [Real.tanh_eq]
  fun_prop

lemma field_spin_test_bound {a : ℝ → ℝ} {B : ℝ} (ha : ∀ u, |a u| ≤ B) (v z u : ℝ) :
    |a u * Real.tanh ((z / v) * u)| ≤ B := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (field_abs_tanh_le_one _) (abs_nonneg _)).trans
    (by simpa only [mul_one] using ha u)

lemma field_spin_test_monotone {a : ℝ → ℝ} (ha : MonotoneOn a (Ici 0))
    (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u) {v z : ℝ} (hv : 0 < v) (hz : 0 ≤ z) :
    MonotoneOn (fun u => a u * Real.tanh ((z / v) * u)) (Ici 0) := by
  intro x hx y hy hxy
  exact mul_le_mul (ha hx hy hxy)
    (field_tanh_monotone (mul_le_mul_of_nonneg_left hxy (div_nonneg hz hv.le)))
    (field_tanh_nonneg (mul_nonneg (div_nonneg hz hv.le) hx)) (hapos y hy)

private lemma field_spin_exp_integrable (v : ℝ≥0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Measurable F) (hgrowth : HasLinearGrowth F)
    (ha : Measurable a) {B : ℝ} (hbound : ∀ u, |a u| ≤ B) :
    Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v) := by
  have hi := (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ).bdd_mul ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hbound u))
  simpa only [mul_comm] using hi

lemma field_gaussian_tilt_odd_eq_abs (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (haodd : Function.Odd a)
    {B : ℝ} (hbound : ∀ u, |a u| ≤ B) :
    (∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)) =
      ∫ u, a |u| * Real.tanh ((z / v) * |u|)
        ∂(gaussianReal z v).tilted (fun u => ζ * F u) := by
  let f := fun u => a u * Real.tanh ((z / (v : ℝ)) * u)
  have hf : Measurable f := field_spin_test_measurable ha v z
  have hb : ∀ u, |f u| ≤ B := field_spin_test_bound hbound v z
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hgrowth ζ
  rw [field_gaussian_tilt_odd_integral_eq_folded v hv z ζ F a hFeven haodd
    (field_spin_exp_integrable v z ζ F a hF hgrowth ha hbound) hw]
  rw [integral_tilted_eq_div]
  exact (field_gaussian_folded_ratio v hv z ζ F f hFeven
    (field_spin_exp_integrable v z ζ F (fun u => f |u|) hF hgrowth
      (hf.comp measurable_abs) (fun u => hb |u|)) hw).symm

/-- Parent, payoff and physical spin-observable comparisons in one actual
Gaussian transition. This is the backward induction step in fld:radial. -/
theorem field_gaussian_spin_transition_order (v : ℝ≥0) (hv : v ≠ 0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G a b : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (ha : Measurable a) (hb : Measurable b) (haodd : Function.Odd a) (hbodd : Function.Odd b)
    (hamono : MonotoneOn a (Ici 0)) (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    (hab : ∀ u ∈ Ici (0 : ℝ), a u ≤ b u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) (hbB : ∀ u, |b u| ≤ B)
    {z₀ z₁ : ℝ} (hz₀ : 0 ≤ z₀) (hzz : z₀ ≤ z₁) :
    (∫ u, a u ∂(gaussianReal z₀ v).tilted (fun u => ζ * F u)) ≤
      ∫ u, b u ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u) := by
  let f := fun u => a u * Real.tanh ((z₀ / (v : ℝ)) * u)
  let g := fun u => b u * Real.tanh ((z₁ / (v : ℝ)) * u)
  have hf : Measurable f := field_spin_test_measurable ha v z₀
  have hg : Measurable g := field_spin_test_measurable hb v z₁
  have hfB : ∀ u, |f u| ≤ B := field_spin_test_bound haB v z₀
  have hgB : ∀ u, |g u| ≤ B := field_spin_test_bound hbB v z₁
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hfmono : MonotoneOn f (Ici 0) := field_spin_test_monotone hamono hapos hvp hz₀
  have hp := field_gaussian_tilt_abs_parent_order v hv ζ F f hF hFeven hFgrowth
    hf hfmono hfB hz₀ hzz
  have hq := field_gaussian_tilt_abs_payoff_order v hv hζ F G f hF hG hFeven hGeven
    hFgrowth hGgrowth hFG hf hfmono hfB z₁
  have htest : ∀ u, f |u| ≤ g |u| := by
    intro u
    have hu : |u| ∈ Ici (0 : ℝ) := abs_nonneg u
    exact mul_le_mul (hab |u| hu)
      (field_tanh_monotone (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hvp).mpr hzz) (abs_nonneg u)))
      (field_tanh_nonneg (mul_nonneg (div_nonneg hz₀ hvp.le) (abs_nonneg u)))
      ((hapos |u| hu).trans (hab |u| hu))
  have hfg : (∫ u, f |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u)) ≤
      ∫ u, g |u| ∂(gaussianReal z₁ v).tilted (fun u => ζ * G u) := by
    apply integral_mono
      (Integrable.of_bound (hf.comp measurable_abs).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hfB |u|)))
      (Integrable.of_bound (hg.comp measurable_abs).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun u => by simpa only [Function.comp_apply, Real.norm_eq_abs] using hgB |u|))) htest
  have he₀ := field_gaussian_tilt_odd_eq_abs v hv z₀ ζ F a hF hFeven hFgrowth ha haodd haB
  have he₁ := field_gaussian_tilt_odd_eq_abs v hv z₁ ζ G b hG hGeven hGgrowth hb hbodd hbB
  exact he₀.trans_le ((hp.trans hq).trans (hfg.trans_eq he₁.symm))

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

lemma fieldSpinTransition_odd (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F)
    (ha : Measurable a) (hOdd : Function.Odd a) :
    Function.Odd (fieldSpinTransition ζ v F a) := by
  intro z
  rw [fieldSpinTransition, fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have hnum : Measurable (fun u => Real.exp (ζ * F u) * a u) := (hF.const_mul ζ).exp.mul ha
  have hn : (∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal (-z) v) =
      -(∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal z v) := by
    rw [← gaussianReal_map_neg (μ := z) (v := v),
      integral_map measurable_neg.aemeasurable hnum.aestronglyMeasurable]
    calc
      _ = ∫ u, -(Real.exp (ζ * F u) * a u) ∂gaussianReal z v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by
          change Real.exp (ζ * F (-u)) * a (-u) = -(Real.exp (ζ * F u) * a u)
          rw [hEven u, hOdd u]
          ring)
      _ = _ := integral_neg _
  have hd := field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
    (fun u => by rw [hEven u])
  rw [hn, hd, neg_div]

lemma fieldSpinTransition_nonneg (ζ : ℝ) (v : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (hEven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (hOdd : Function.Odd a)
    (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ fieldSpinTransition ζ v F a z := by
  by_cases hv : v = 0
  · subst v
    rw [fieldSpinTransition_zero_variance]
    exact hapos z hz
  have he := field_gaussian_tilt_odd_eq_abs v hv z ζ F a hF hEven hgrowth ha hOdd haB
  rw [fieldSpinTransition, he]
  apply integral_nonneg
  intro u
  exact mul_nonneg (hapos |u| (abs_nonneg u))
    (field_tanh_nonneg (mul_nonneg (div_nonneg hz v.coe_nonneg) (abs_nonneg u)))

lemma fieldSpinTransition_monotone {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (hEven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (ha : Measurable a) (hOdd : Function.Odd a)
    (hamono : MonotoneOn a (Ici 0)) (hapos : ∀ u ∈ Ici (0 : ℝ), 0 ≤ a u)
    {B : ℝ} (haB : ∀ u, |a u| ≤ B) :
    MonotoneOn (fieldSpinTransition ζ v F a) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    intro x hx y hy hxy
    rw [fieldSpinTransition_zero_variance, fieldSpinTransition_zero_variance]
    exact hamono hx hy hxy
  intro x hx y _hy hxy
  exact field_gaussian_spin_transition_order v hv hζ F F a a hF hF hEven hEven hgrowth hgrowth
    (by intro u _ w _ _; simp only [sub_self, le_refl])
    ha ha hOdd hOdd hamono hapos (fun _ _ => le_rfl) haB haB hx hxy

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianOrdinaryOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary Gaussian integration preserves radial monotonicity. This is
the exponent-zero endpoint of the backward field comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussian_integral_monotone (v : ℝ≥0) (hv : v ≠ 0)
    (F : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (hmono : MonotoneOn F (Ici 0)) :
    MonotoneOn (fun z => ∫ u, F u ∂gaussianReal z v) (Ici 0) := by
  let W : ℝ → ℝ → ℝ := fieldFoldedWeight v 0 (fun _ => 0)
  have hw (z : ℝ) : Integrable (fun u : ℝ => Real.exp (0 * (0 : ℝ))) (gaussianReal z v) := by
    simpa only [zero_mul, Real.exp_zero] using (integrable_const (1 : ℝ))
  have hi (z : ℝ) : Integrable (fun u => Real.exp (0 * (0 : ℝ)) * F |u|)
      (gaussianReal z v) := by
    simpa only [zero_mul, Real.exp_zero, one_mul, field_even_abs hFeven] using
      field_gaussian_linear_integrable v z hF hgrowth
  have hW (z : ℝ) : Integrable (W z) (volume.restrict (Ici 0)) :=
    fieldFoldedWeight_integrable v hv z 0 (fun _ => 0) (fun _ => rfl) (hw z)
  have hFW (z : ℝ) : Integrable (fun u => F u * W z u) (volume.restrict (Ici 0)) :=
    field_folded_test_integrable v hv z 0 (fun _ => 0) F (fun _ => rfl) (hi z)
  have hWpos (z : ℝ) : 0 < ∫ u in Ici 0, W z u :=
    fieldFoldedWeight_mass_pos v hv z 0 (fun _ => 0) (fun _ => rfl) (hw z)
  have he (z : ℝ) : (∫ u, F u ∂gaussianReal z v) =
      (∫ u in Ici 0, F u * W z u) / (∫ u in Ici 0, W z u) := by
    simpa [W, field_even_abs hFeven] using
      field_gaussian_folded_ratio v hv z 0 (fun _ => 0) F (fun _ => rfl) (hi z) (hw z)
  intro x hx y _hy hxy
  change (∫ u, F u ∂gaussianReal x v) ≤ ∫ u, F u ∂gaussianReal y v
  rw [he x, he y]
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) (W x) (W y) F
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun u hu w _hw huw => fieldFoldedWeight_parent_order hvp 0 (fun _ => 0) hx hxy hu huw)
    (hW x) (hW y) (hFW x) (hFW y) (hWpos x) (hWpos y)

lemma gaussianOperator_difference_monotone_zero (v : ℝ≥0) (hv : v ≠ 0)
    (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator 0 v G z - gaussianOperator 0 v F z) (Ici 0) := by
  have hm := field_gaussian_integral_monotone v hv (fun u => G u - F u)
    (hG.sub hF) (fun u => by change G (-u) - F (-u) = G u - F u; rw [hGeven u, hFeven u])
    (field_linearGrowth_sub hFgrowth hGgrowth) hFG
  have he (z : ℝ) : gaussianOperator 0 v G z - gaussianOperator 0 v F z =
      ∫ u, (G u - F u) ∂gaussianReal z v := by
    rw [gaussianOperator_eq_gaussian_integral v hG,
      gaussianOperator_eq_gaussian_integral v hF,
      integral_sub (field_gaussian_linear_integrable v z hG hGgrowth)
        (field_gaussian_linear_integrable v z hF hFgrowth)]
  simpa only [he] using hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianRecursionOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial payoff comparison propagates through each actual nonzero
Gaussian backward operator. The zero-exponent case is handled separately. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldFolded_exp_difference_mul (v ζ : ℝ) (F G : ℝ → ℝ) (z u : ℝ) :
    Real.exp (ζ * (G u - F u)) * fieldFoldedWeight v ζ F z u =
      fieldFoldedWeight v ζ G z u := by
  dsimp only [fieldFoldedWeight]
  calc
    _ = (Real.exp (-u ^ 2 / (2 * v)) * Real.cosh (z / v * u)) *
        (Real.exp (ζ * (G u - F u)) * Real.exp (ζ * F u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma fieldFolded_mass_ratio_monotone (v : ℝ) (hv : 0 < v) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hF : ∀ z, Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)))
    (hG : ∀ z, Integrable (fieldFoldedWeight v ζ G z) (volume.restrict (Ici 0)))
    (hFpos : ∀ z, 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z u) :
    MonotoneOn (fun z => (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) /
      (∫ u in Ici 0, fieldFoldedWeight v ζ F z u)) (Ici 0) := by
  intro x hx y _hy hxy
  have htest : MonotoneOn (fun u => Real.exp (ζ * (G u - F u))) (Ici 0) := by
    intro u hu v hv huv
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG hu hv huv) hζ)
  have hi (z : ℝ) : Integrable (fun u => Real.exp (ζ * (G u - F u)) *
      fieldFoldedWeight v ζ F z u) (volume.restrict (Ici 0)) := by
    simpa only [fieldFolded_exp_difference_mul] using hG z
  have h := field_likelihood_ratio_expectation_le (volume.restrict (Ici 0))
    (fieldFoldedWeight v ζ F x) (fieldFoldedWeight v ζ F y)
    (fun u => Real.exp (ζ * (G u - F u))) (ae_restrict_mem measurableSet_Ici) htest
    (fun u hu w _hw huw => fieldFoldedWeight_parent_order hv ζ F hx hxy hu huw)
    (hF x) (hF y) (hi x) (hi y) (hFpos x) (hFpos y)
  simpa only [fieldFolded_exp_difference_mul] using h

lemma field_gaussian_exp_ratio_folded (v : ℝ≥0) (hv : v ≠ 0) (ζ : ℝ)
    (F G : ℝ → ℝ) (hFeven : Function.Even F) (hGeven : Function.Even G)
    (z : ℝ)
    (hzF : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v))
    (hzG : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * G u) ∂gaussianReal z v) /
      (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) =
    (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) /
      (∫ u in Ici 0, fieldFoldedWeight v ζ F z u) := by
  have hnum := field_gaussian_folded_integral v hv z ζ G (fun _ => 1) hGeven
    (by simpa only [mul_one] using hzG)
  have hden := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hFeven
    (by simpa only [mul_one] using hzF)
  simp only [mul_one, one_mul] at hnum hden
  rw [hnum, hden, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

/-- Increasing an even payoff by a radially increasing difference has a
radially increasing effect on the nonzero-exponent backward value. -/
theorem gaussianOperator_difference_monotone_pos (v : ℝ≥0) (hv : v ≠ 0)
    {ζ : ℝ} (hζ : 0 < ζ) (F G : ℝ → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator ζ v G z - gaussianOperator ζ v F z) (Ici 0) := by
  have hwF (z : ℝ) : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hFgrowth ζ
  have hwG (z : ℝ) : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hG hGgrowth ζ
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hratio := fieldFolded_mass_ratio_monotone v hvp hζ.le F G hFG
    (fun z => fieldFoldedWeight_integrable v hv z ζ F hFeven (hwF z))
    (fun z => fieldFoldedWeight_integrable v hv z ζ G hGeven (hwG z))
    (fun z => fieldFoldedWeight_mass_pos v hv z ζ F hFeven (hwF z))
  intro x hx y hy hxy
  have hr := hratio hx hy hxy
  dsimp only at hr ⊢
  rw [← field_gaussian_exp_ratio_folded v hv ζ F G hFeven hGeven x (hwF x) (hwG x),
    ← field_gaussian_exp_ratio_folded v hv ζ F G hFeven hGeven y (hwF y) (hwG y)] at hr
  have hpF (z : ℝ) := MeasureTheory.integral_exp_pos (hwF z)
  have hpG (z : ℝ) := MeasureTheory.integral_exp_pos (hwG z)
  have hlog := Real.log_le_log (div_pos (hpG x) (hpF x)) hr
  rw [Real.log_div (hpG x).ne' (hpF x).ne', Real.log_div (hpG y).ne' (hpF y).ne'] at hlog
  simpa only [gaussianOperator_eq_gaussian_exp_integral hζ.ne' v hG,
    gaussianOperator_eq_gaussian_exp_integral hζ.ne' v hF, ← mul_sub] using
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hζ.le)

/-- Full one-step radial difference preservation, including zero Gaussian
variance and the ordinary root exponent. -/
theorem gaussianOperator_difference_monotone (v : ℝ≥0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator ζ v G z - gaussianOperator ζ v F z) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    simpa only [NNReal.coe_zero, gaussianOperator_zero_variance] using hFG
  by_cases hz : ζ = 0
  · subst ζ
    exact gaussianOperator_difference_monotone_zero v hv F G hF hG
      hFeven hGeven hFgrowth hGgrowth hFG
  · exact gaussianOperator_difference_monotone_pos v hv (lt_of_le_of_ne hζ (Ne.symm hz))
      F G hF hG hFeven hGeven hFgrowth hGgrowth hFG

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldEvenTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even bounded tests of the tilted scalar position chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_even (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F)
    (ha : Measurable a) (hae : Function.Even a) :
    Function.Even (fieldSpinTransition ζ v F a) := by
  intro z
  rw [fieldSpinTransition, fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have he : Function.Even (fun u => Real.exp (ζ * F u) * a u) := by
    intro u
    dsimp only
    rw [hFe u, hae u]
  have hm : Measurable (fun u => Real.exp (ζ * F u) * a u) :=
    (hF.const_mul ζ).exp.mul ha
  rw [field_gaussian_integral_reflect v z hm he,
    field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
      (fun u => by rw [hFe u])]

lemma fieldSpinTransition_even_monotone (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F) (hFg : HasLinearGrowth F)
    (ha : Measurable a) (hae : Function.Even a) (ham : MonotoneOn a (Ici 0))
    {K : ℝ} (haB : ∀ u, |a u| ≤ K) :
    MonotoneOn (fieldSpinTransition ζ v F a) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    intro x hx y hy hxy
    rw [fieldSpinTransition_zero_variance, fieldSpinTransition_zero_variance]
    exact ham hx hy hxy
  intro x hx y _hy hxy
  have h := field_gaussian_tilt_abs_parent_order v hv ζ F a hF hFe hFg
    ha ham haB hx hxy
  simpa only [fieldSpinTransition, field_even_abs hae] using h

lemma fieldSpinTransition_even_order (v : ℝ≥0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    {F G a b : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hae : Function.Even a) (hbe : Function.Even b)
    (ham : MonotoneOn a (Ici 0)) {K : ℝ}
    (haB : ∀ u, |a u| ≤ K) (hbB : ∀ u, |b u| ≤ K)
    (hab : ∀ u ∈ Ici (0 : ℝ), a u ≤ b u) (z : ℝ) :
    fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v G b z := by
  have hab' (u : ℝ) : a u ≤ b u := by
    rw [← field_even_abs hae u, ← field_even_abs hbe u]
    exact hab |u| (abs_nonneg u)
  by_cases hv : v = 0
  · subst v
    simpa only [fieldSpinTransition_zero_variance] using hab' z
  have h := field_gaussian_tilt_abs_payoff_order v hv hζ F G a hF hG hFe hGe
    hFg hGg hFG ha ham haB z
  have h' : fieldSpinTransition ζ v F a z ≤ fieldSpinTransition ζ v G a z := by
    simpa only [fieldSpinTransition, field_even_abs hae] using h
  exact h'.trans (fieldSpinTransition_mono_test ζ v G ha hb haB hbB hab' z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial order of the actual scalar backward values and physical spin
means, with covariance increments fixed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_even (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (he : Function.Even F) :
    Function.Even (fieldScalarValue L F) := by
  induction L with
  | nil => exact he
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldScalarValue_regular L ht hF hG
    exact gaussianOperator_even av.1 av.2 hr.1 (ih ht)

lemma fieldScalarValue_difference_monotone (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0)) :
    MonotoneOn (fun z => fieldScalarValue L G z - fieldScalarValue L F z) (Ici 0) := by
  induction L with
  | nil => exact hFG
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    exact gaussianOperator_difference_monotone av.2 (hL av List.mem_cons_self).le
      _ _ hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
      (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2 (ih ht)

lemma fieldScalarMean_shape (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hFe : Function.Even F)
    (ha : Measurable a) (hao : Function.Odd a)
    (ham : MonotoneOn a (Ici 0)) (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z)
    {K : ℝ} (haB : ∀ z, |a z| ≤ K) :
    Function.Odd (fieldScalarMean L F a) ∧
      MonotoneOn (fieldScalarMean L F a) (Ici 0) ∧
      ∀ z ∈ Ici (0 : ℝ), 0 ≤ fieldScalarMean L F a z := by
  induction L with
  | nil => exact ⟨hao, ham, hap⟩
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha haB
    have hs := ih ht
    have he := fieldScalarValue_even L ht hF hG hFe
    refine ⟨fieldSpinTransition_odd av.1 av.2 hr.1 he hm.1 hs.1, ?_, ?_⟩
    · exact fieldSpinTransition_monotone (hL av List.mem_cons_self).le av.2
        hr.1 he hr.2 hm.1 hs.1 hs.2.1 hs.2.2 hm.2
    · intro z hz
      exact fieldSpinTransition_nonneg av.1 av.2 hr.1 he hr.2 hm.1 hs.1 hs.2.2 hm.2 hz

lemma fieldScalarMean_order (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hao : Function.Odd a) (hbo : Function.Odd b)
    (ham : MonotoneOn a (Ici 0)) (hbm : MonotoneOn b (Ici 0))
    (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z) (hbp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ b z)
    {K : ℝ} (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ K)
    (hab : ∀ z ∈ Ici (0 : ℝ), a z ≤ b z) :
    ∀ z ∈ Ici (0 : ℝ), fieldScalarMean L F a z ≤ fieldScalarMean L G b z := by
  induction L with
  | nil => exact hab
  | cons av L ih =>
    have ht (bv) (hc : bv ∈ L) := hL bv (List.mem_cons_of_mem av hc)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    have hmr := fieldScalarMean_regular L ht hF hFg ha haB
    have hnr := fieldScalarMean_regular L ht hG hGg hb hbB
    have hms := fieldScalarMean_shape L ht hF hFg hFe ha hao ham hap haB
    have hns := fieldScalarMean_shape L ht hG hGg hGe hb hbo hbm hbp hbB
    intro z hz
    by_cases hv : av.2 = 0
    · simpa only [fieldScalarMean, hv, fieldSpinTransition_zero_variance] using ih ht z hz
    · exact field_gaussian_spin_transition_order av.2 hv (hL av List.mem_cons_self).le
        _ _ _ _ hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
        (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2
        (fieldScalarValue_difference_monotone L ht hF hG hFg hGg hFe hGe hFG)
        hmr.1 hnr.1 hms.1 hns.1 hms.2.1 hms.2.2 (ih ht) hmr.2 hnr.2 hz le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarSquareOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered even second-moment tests propagated through the actual
finite tilted position chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_shape (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hFe : Function.Even F)
    (ha : Measurable a) (hao : Function.Odd a)
    (ham : MonotoneOn a (Ici 0)) (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z)
    (haB : ∀ z, |a z| ≤ 1) :
    ∀ i, Function.Even (fieldScalarSquares L F a i) ∧
      MonotoneOn (fieldScalarSquares L F a i) (Ici 0) := by
  have hsq (f : ℝ → ℝ) (ho : Function.Odd f)
      (hm : MonotoneOn f (Ici 0)) (hp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ f z) :
      Function.Even (fun z => (f z) ^ 2) ∧ MonotoneOn (fun z => (f z) ^ 2) (Ici 0) := by
    refine ⟨fun z => by dsimp only; rw [ho z, neg_sq], ?_⟩
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (hp x hx) (hm hx hy hxy) 2
  induction L with
  | nil => intro i; exact hsq a hao ham hap
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have he := fieldScalarValue_even L ht hF hG hFe
    have hs := fieldScalarMean_shape (av :: L) hL hF hG hFe ha hao ham hap haB
    have hr := fieldScalarSquares_regular L ht hF hG ha haB
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsq _ hs.1 hs.2.1 hs.2.2
    · have hj := ih ht j
      have hb (z : ℝ) : |fieldScalarSquares L F a j z| ≤ 1 := by
        rw [abs_of_nonneg ((hr j).2 z).1]
        exact ((hr j).2 z).2
      exact ⟨fieldSpinTransition_even av.1 av.2 hv.1 he (hr j).1 hj.1,
        fieldSpinTransition_even_monotone av.1 av.2 hv.1 he hv.2
          (hr j).1 hj.1 hj.2 hb⟩

lemma fieldScalarSquares_order (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hao : Function.Odd a) (hbo : Function.Odd b)
    (ham : MonotoneOn a (Ici 0)) (hbm : MonotoneOn b (Ici 0))
    (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z) (hbp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ b z)
    (haB : ∀ z, |a z| ≤ 1) (hbB : ∀ z, |b z| ≤ 1)
    (hab : ∀ z ∈ Ici (0 : ℝ), a z ≤ b z) :
    ∀ i z, fieldScalarSquares L F a i z ≤ fieldScalarSquares L G b i z := by
  induction L with
  | nil =>
    intro i z
    have heF : (a z) ^ 2 = (a |z|) ^ 2 := by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz, hao z, neg_sq]
    have heG : (b z) ^ 2 = (b |z|) ^ 2 := by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz, hbo z, neg_sq]
    change (a z) ^ 2 ≤ (b z) ^ 2
    rw [heF, heG]
    exact pow_le_pow_left₀ (hap _ (abs_nonneg z)) (hab _ (abs_nonneg z)) 2
  | cons av L ih =>
    have ht (bv) (hc : bv ∈ L) := hL bv (List.mem_cons_of_mem av hc)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    have hFs := fieldScalarSquares_shape (av :: L) hL hF hFg hFe ha hao ham hap haB
    have hGs := fieldScalarSquares_shape (av :: L) hL hG hGg hGe hb hbo hbm hbp hbB
    have hms := fieldScalarMean_shape (av :: L) hL hF hFg hFe ha hao ham hap haB
    have hmorder := fieldScalarMean_order (av :: L) hL hF hG hFg hGg hFe hGe hFG
      ha hb hao hbo ham hbm hap hbp haB hbB hab
    have hFreg := fieldScalarSquares_regular L ht hF hFg ha haB
    have hGreg := fieldScalarSquares_regular L ht hG hGg hb hbB
    intro i z
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← field_even_abs (hFs 0).1 z, ← field_even_abs (hGs 0).1 z]
      simp only [fieldScalarSquares_zero]
      exact pow_le_pow_left₀ (hms.2.2 _ (abs_nonneg z)) (hmorder _ (abs_nonneg z)) 2
    · have hshape := fieldScalarSquares_shape L ht hF hFg hFe ha hao ham hap haB j
      have hgshape := fieldScalarSquares_shape L ht hG hGg hGe hb hbo hbm hbp hbB j
      have hFb (u : ℝ) : |fieldScalarSquares L F a j u| ≤ 1 := by
        rw [abs_of_nonneg ((hFreg j).2 u).1]
        exact ((hFreg j).2 u).2
      have hGb (u : ℝ) : |fieldScalarSquares L G b j u| ≤ 1 := by
        rw [abs_of_nonneg ((hGreg j).2 u).1]
        exact ((hGreg j).2 u).2
      exact fieldSpinTransition_even_order av.2 (hL av List.mem_cons_self).le
        hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
        (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2
        (fieldScalarValue_difference_monotone L ht hF hG hFg hGg hFe hGe hFG)
        (hFreg j).1 (hGreg j).1 hshape.1 hgshape.1 hshape.2 hFb hGb
        (fun u _ => ih ht j u) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evenness, monotonicity and the unit spin bound for the actual affine
log-cosh recursion. These hypotheses of the mixed-order argument are
discharged from the explicit terminal function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

theorem fieldAffineFamily_shape (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t)
    (hζ : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    Function.Even (fun z => (fieldAffineFamily I hI L hL).U (t, z)) ∧
    Function.Odd (fun z => (fieldAffineFamily I hI L hL).X (t, z)) ∧
    MonotoneOn (fun z => (fieldAffineFamily I hI L hL).X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ (fieldAffineFamily I hI L hL).X (t, z)) ∧
    (∀ z, |(fieldAffineFamily I hI L hL).X (t, z)| ≤ 1) := by
  have hi : ∀ av ∈ fieldAffineIncrements L t, 0 < av.1 := by
    intro av hav
    obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
    exact hζ bv hb
  have hF : Measurable (fun z : ℝ => Real.log (Real.cosh z)) := by fun_prop
  have hFg : HasLinearGrowth (fun z : ℝ => Real.log (Real.cosh z)) :=
    (fieldLogCoshFamily I).growth 0
  have hFe : Function.Even (fun z : ℝ => Real.log (Real.cosh z)) := by
    intro z
    simp only [Real.cosh_neg]
  have ha : Measurable (fun z : ℝ => Real.tanh z) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hao : Function.Odd Real.tanh := Real.tanh_neg
  have ham : MonotoneOn Real.tanh (Ici 0) := field_tanh_monotone.monotoneOn _
  have hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ Real.tanh z := fun _ hz => field_tanh_nonneg hz
  have hv := fieldScalarValue_even (fieldAffineIncrements L t) hi hF hFg hFe
  have hm := fieldScalarMean_shape (fieldAffineIncrements L t) hi hF hFg hFe
    ha hao ham hap field_abs_tanh_le_one
  have hb := (fieldScalarMean_regular (fieldAffineIncrements L t) hi hF hFg
    ha field_abs_tanh_le_one).2
  have hU : (fun z => (fieldAffineFamily I hI L hL).U (t, z)) =
      fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
    rw [fieldAffineFamily_value I hI L hL]
    exact fieldAffineValue_scalar L t
  have hX := fieldAffineFamily_mean I hI L hL t
  have hXp (z : ℝ) := congrFun hX z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    exact hv
  · rw [hX]
    exact hm.1
  · rw [hX]
    exact hm.2.1
  · intro z hz
    rw [hXp]
    exact hm.2.2 z hz
  · intro z
    rw [hXp]
    exact hb z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldParameterOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial order of the parameter derivative integrates to radial
order of payoff differences, without interchanging mixed derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem field_parameter_difference_order {I : Set ℝ} (hI : Convex ℝ I)
    {F D : ℝ → ℝ → ℝ}
    (hd : ∀ t ∈ I, ∀ z, HasDerivAt (fun s => F s z) (D t z) t)
    (hD : ∀ t ∈ I, AntitoneOn (D t) (Ici 0))
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    MonotoneOn (fun z => F t z - F s z) (Ici 0) := by
  intro x hx y hy hxy
  have hder (q : ℝ) (hq : q ∈ I) :
      HasDerivAt (fun r => F r y - F r x) (D q y - D q x) q :=
    (hd q hq y).sub (hd q hq x)
  have hanti : AntitoneOn (fun r => F r y - F r x) I :=
    antitoneOn_of_hasDerivWithinAt_nonpos hI
      (fun q hq => (hder q hq).continuousAt.continuousWithinAt)
      (fun q hq => (hder q (interior_subset hq)).hasDerivWithinAt)
      (fun q hq => sub_nonpos.mpr (hD q (interior_subset hq) hx hy hxy))
  have h := hanti ht hs hts
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpatialParameterOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spatial consequence of the backward covariance derivative.
Radial antitonicity of that derivative gives ordering of the physical
conditional means, and hence ordering of all earlier squared means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

theorem field_spatial_derivative_order {F : ℝ → ℝ} {f g : ℝ}
    (hF : HasDerivAt F f g) {H : ℝ → ℝ} {h : ℝ}
    (hH : HasDerivAt H h g) (hg : 0 ≤ g)
    (hmono : MonotoneOn (fun y => F y - H y) (Ici 0)) : h ≤ f := by
  have hd : HasDerivAt (fun y => F y - H y) (f - h) g := hF.sub hH
  have hn := hmono.derivWithin_nonneg (x := g)
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 g hg)] at hn
  exact sub_nonneg.mp hn

namespace FieldSmoothFamily

theorem physical_mean_antitone_parameter {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : Convex ℝ I) (hD : ∀ t ∈ I, AntitoneOn (fun z => F.T (t, z)) (Ici 0))
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    ∀ z ∈ Ici (0 : ℝ), F.X (s, z) ≤ F.X (t, z) := by
  have hp := field_parameter_difference_order hI
    (fun q hq z => F.parameter_derivative q z hq) hD ht hs hts
  intro z hz
  exact field_spatial_derivative_order (F.spatial t z) (F.spatial s z) hz hp

theorem earlier_squares_antitone_parameter {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : Convex ℝ I) (hD : ∀ t ∈ I, AntitoneOn (fun z => F.T (t, z)) (Ici 0))
    (hUe : ∀ t ∈ I, Function.Even (fun z => F.U (t, z)))
    (hXo : ∀ t ∈ I, Function.Odd (fun z => F.X (t, z)))
    (hXm : ∀ t ∈ I, MonotoneOn (fun z => F.X (t, z)) (Ici 0))
    (hXp : ∀ t ∈ I, ∀ z ∈ Ici (0 : ℝ), 0 ≤ F.X (t, z))
    (hXb : ∀ p, |F.X p| ≤ 1)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    ∀ i z, fieldScalarSquares L (fun y => F.U (s, y)) (fun y => F.X (s, y)) i z ≤
      fieldScalarSquares L (fun y => F.U (t, y)) (fun y => F.X (t, y)) i z := by
  have hp := field_parameter_difference_order hI
    (fun q hq z => F.parameter_derivative q z hq) hD ht hs hts
  exact fieldScalarSquares_order L hL
    (F := fun y => F.U (s, y)) (G := fun y => F.U (t, y))
    (a := fun y => F.X (s, y)) (b := fun y => F.X (t, y))
    (F.mU.comp (by fun_prop)) (F.mU.comp (by fun_prop)) (F.growth s) (F.growth t)
    (hUe s hs) (hUe t ht) hp
    (F.mX.comp (by fun_prop)) (F.mX.comp (by fun_prop))
    (hXo s hs) (hXo t ht) (hXm s hs) (hXm t ht) (hXp s hs) (hXp t ht)
    (fun z => hXb (s, z)) (fun z => hXb (t, z))
    (F.physical_mean_antitone_parameter hI hD ht hs hts)

end FieldSmoothFamily
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTangentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evenness and radial antitonicity of a backward covariance derivative
are preserved by each unchanged earlier Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussianTiltAverage_even (s ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F)
    (hA : Measurable A) (hAe : Function.Even A) :
    Function.Even (gaussianTiltAverage s ζ F A) := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hA]
  exact fieldSpinTransition_even ζ (Real.toNNReal s) hF hFe hA hAe

lemma field_gaussianTiltAverage_even_monotone (s ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hFe : Function.Even F) (hFg : HasLinearGrowth F)
    (hA : Measurable A) (hAe : Function.Even A) (hAm : MonotoneOn A (Ici 0))
    {K : ℝ} (hAb : ∀ y, |A y| ≤ K) :
    MonotoneOn (gaussianTiltAverage s ζ F A) (Ici 0) := by
  rw [field_gaussianTiltAverage_eq_transition s ζ hF hA]
  exact fieldSpinTransition_even_monotone ζ (Real.toNNReal s) hF hFe hFg hA hAe hAm hAb

lemma field_negative_square_average_shape (s ζ k : ℝ) (hk : 0 ≤ k)
    {F X : ℝ → ℝ} (hF : Measurable F) (hFe : Function.Even F)
    (hFg : HasLinearGrowth F) (hX : Measurable X) (hXo : Function.Odd X)
    (hXm : MonotoneOn X (Ici 0)) (hXp : ∀ y ∈ Ici (0 : ℝ), 0 ≤ X y)
    {K : ℝ} (hXb : ∀ y, |X y| ≤ K) :
    Function.Even (fun z => -k * gaussianTiltAverage s ζ F (fun y => (X y) ^ 2) z) ∧
      AntitoneOn (fun z => -k * gaussianTiltAverage s ζ F (fun y => (X y) ^ 2) z) (Ici 0) := by
  have he : Function.Even (fun y => (X y) ^ 2) := by
    intro y
    dsimp only
    rw [hXo y, neg_sq]
  have hm : MonotoneOn (fun y => (X y) ^ 2) (Ici 0) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (hXp x hx) (hXm hx hy hxy) 2
  have hb : ∀ y, |(X y) ^ 2| ≤ K ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hXb y) 2
  have hJ := field_gaussianTiltAverage_even s ζ hF hFe (hX.pow_const 2) he
  have hJm := field_gaussianTiltAverage_even_monotone s ζ hF hFe hFg
    (hX.pow_const 2) he hm hb
  refine ⟨fun z => by dsimp only; rw [hJ z], ?_⟩
  intro x hx y hy hxy
  exact mul_le_mul_of_nonpos_left (hJm hx hy hxy) (neg_nonpos.mpr hk)

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

lemma fieldAdjacentInner_shape (a b η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hη : 0 < η) (hζ : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    let G := fieldAdjacentInner a b η L hb hs
    Function.Even (fun z => G.U (t, z)) ∧
    Function.Odd (fun z => G.X (t, z)) ∧
    MonotoneOn (fun z => G.X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ G.X (t, z)) ∧ (∀ z, |G.X (t, z)| ≤ 1) := by
  let av : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: L, ∀ q ∈ Ioo (-a) b, 0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.2]
    · rw [hs v hv, zero_mul, add_zero]
      exact hb v hv
  have he : ∀ v ∈ av :: L, 0 < v.exponent := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hη
    · exact hζ v hv
  change Function.Even (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo (av :: L) hv).U (t, z)) ∧ _
  exact fieldAffineFamily_shape (Ioo (-a) b) isOpen_Ioo (av :: L) hv he t

lemma fieldAdjacentFamily_shape (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hη : 0 < η) (htail : ∀ av ∈ L, 0 < av.exponent) (t : ℝ) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    Function.Even (fun z => G.U (t, z)) ∧
    Function.Odd (fun z => G.X (t, z)) ∧
    MonotoneOn (fun z => G.X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ G.X (t, z)) ∧ (∀ z, |G.X (t, z)| ≤ 1) := by
  let av : FieldAffineStep := ⟨a, 1, ζ⟩
  let bv : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: bv :: L, ∀ q ∈ Ioo (-a) b, 0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.1]
    · rcases List.mem_cons.mp hv with rfl | hv
      · dsimp only [bv]
        linarith [hq.2]
      · rw [hs v hv, zero_mul, add_zero]
        exact hb v hv
  have he : ∀ v ∈ av :: bv :: L, 0 < v.exponent := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hζ
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hη
      · exact htail v hv
  change Function.Even (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo (av :: bv :: L) hv).U (t, z)) ∧ _
  exact fieldAffineFamily_shape (Ioo (-a) b) isOpen_Ioo (av :: bv :: L) hv he t

theorem fieldAdjacentFamily_tangent_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hη : 0 < η) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    {t : ℝ} (ht : t ∈ Ioo (-a) b) :
    AntitoneOn (fun z => (fieldAdjacentFamily a b ζ η L hb hs).T (t, z)) (Ici 0) := by
  let F := fieldAdjacentTail a b L hb hs
  let G := fieldAdjacentInner a b η L hb hs
  have hg := fieldAdjacentInner_shape a b η L hb hs hη htail t
  have hU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
  have hX : Measurable (fun z => G.X (t, z)) := G.mX.comp (by fun_prop)
  have hshape := field_negative_square_average_shape (a + t) ζ ((η - ζ) / 2)
    (by linarith) hU hg.1 (G.growth t) hX hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have heq : (fun z => (fieldAdjacentFamily a b ζ η L hb hs).T (t, z)) =
      (fun z => -((η - ζ) / 2) * gaussianTiltAverage (a + t) ζ
        (fun y => G.U (t, y)) (fun y => (G.X (t, y)) ^ 2) z) := by
    funext z
    have h := F.adjacent_tangent isOpen_Ioo a b ζ η
      (fun q hq => by linarith [hq.1]) (fun q hq => by linarith [hq.2])
      (p := (t, z)) ht (fun y => fieldAdjacentTail_stationary a b L hb hs (t, y))
    simpa only [F, G, fieldAdjacentFamily, fieldAdjacentInner, neg_div] using h
  rw [heq]
  exact hshape.2

theorem fieldAdjacent_earlier_squares_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1)
    {t s : ℝ} (ht : t ∈ Ioo (-a) b) (hss : s ∈ Ioo (-a) b) (hts : t ≤ s) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    ∀ i z, fieldScalarSquares P (fun y => G.U (s, y)) (fun y => G.X (s, y)) i z ≤
      fieldScalarSquares P (fun y => G.U (t, y)) (fun y => G.X (t, y)) i z := by
  have hη : 0 < η := lt_of_lt_of_le hζ hζη
  let G := fieldAdjacentFamily a b ζ η L hb hs
  have hshape (q : ℝ) := fieldAdjacentFamily_shape a b ζ η L hb hs hζ hη htail q
  exact G.earlier_squares_antitone_parameter (convex_Ioo (-a) b)
    (fun q hq => fieldAdjacentFamily_tangent_antitone a b ζ η L hb hs hη hζη htail hq)
    (fun q _ => (hshape q).1) (fun q _ => (hshape q).2.1)
    (fun q _ => (hshape q).2.2.1) (fun q _ => (hshape q).2.2.2.1)
    (fun p => (hshape p.1).2.2.2.2 p.2) P hP ht hss hts

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSquarePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of an earlier conditional spin square with an unchanged
later scalar recursion. This keeps the ordinary Gaussian root separate. -/

noncomputable section
open IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_append_prefix (P S : List (ℝ × ℝ≥0)) (F a : ℝ → ℝ)
    (i : Fin (P.length + 1)) :
    fieldScalarSquares (P ++ S) F a (fieldPrefixIndex P S i) =
      fieldScalarSquares P (fieldScalarValue S F) (fieldScalarMean S F a) i := by
  induction P with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hi := i.isLt
      simp only [List.length_nil, zero_add] at hi
      omega
    subst i
    have he : fieldPrefixIndex [] S 0 = 0 := by apply Fin.ext; rfl
    rw [he]
    funext z
    simp only [List.nil_append, fieldScalarSquares_zero, fieldScalarSquares]
  | cons av P ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have he : fieldPrefixIndex (av :: P) S 0 = 0 := by apply Fin.ext; rfl
      rw [he]
      funext z
      rw [fieldScalarSquares_zero, fieldScalarSquares_zero, fieldScalarMean_append]
    · have he : fieldPrefixIndex (av :: P) S j.succ = (fieldPrefixIndex P S j).succ := by
        apply Fin.ext
        rfl
      rw [he]
      change fieldSpinTransition av.1 av.2 (fieldScalarValue (P ++ S) F)
        (fieldScalarSquares (P ++ S) F a (fieldPrefixIndex P S j)) = _
      rw [fieldScalarValue_append, ih]
      rfl

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

lemma fieldTerminalFamily_mean_eq_transition (a ζ t : ℝ) :
    (fun z => (fieldTerminalFamily a ζ).X (t, z)) =
      fieldSpinTransition ζ (Real.toNNReal (a + t))
        (fun y => Real.log (Real.cosh y)) Real.tanh := by
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  funext z
  change gaussianTiltAverage (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) Real.tanh z = _
  rw [one_mul, field_gaussianTiltAverage_eq_transition _ _ measurable_logCosh hm]

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

theorem fieldTerminalFamily_tangent_antitone (a ζ : ℝ) (hζ : ζ ≤ 1) (t : ℝ) :
    AntitoneOn (fun z => (fieldTerminalFamily a ζ).T (t, z)) (Ici 0) := by
  have he : Function.Even (fun y : ℝ => Real.log (Real.cosh y)) := by
    intro y
    simp only [Real.cosh_neg]
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  have h := field_negative_square_average_shape (a + t) ζ ((1 - ζ) / 2) (by linarith)
    measurable_logCosh he logCosh_linearGrowth hm Real.tanh_neg
    (field_tanh_monotone.monotoneOn _) (fun _ hy => field_tanh_nonneg hy)
    field_abs_tanh_le_one
  intro x hx y hy hxy
  dsimp only
  rw [fieldTerminalFamily_tangent, fieldTerminalFamily_tangent]
  have hh := h.2 hx hy hxy
  dsimp only at hh
  linarith

theorem fieldTerminalFamily_shape (a ζ : ℝ) (hζ : 0 ≤ ζ) (t : ℝ) :
    Function.Even (fun z => (fieldTerminalFamily a ζ).U (t, z)) ∧
    Function.Odd (fun z => (fieldTerminalFamily a ζ).X (t, z)) ∧
    MonotoneOn (fun z => (fieldTerminalFamily a ζ).X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ (fieldTerminalFamily a ζ).X (t, z)) ∧
    (∀ z, |(fieldTerminalFamily a ζ).X (t, z)| ≤ 1) := by
  have he : Function.Even (fun y : ℝ => Real.log (Real.cosh y)) := by
    intro y
    simp only [Real.cosh_neg]
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hval := fieldTerminalFamily_value_eq_operator a ζ t
  have hmean := fieldTerminalFamily_mean_eq_transition a ζ t
  have hmeanPoint (z : ℝ) := congrFun hmean z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]
    exact gaussianOperator_even ζ _ measurable_logCosh he
  · rw [hmean]
    exact fieldSpinTransition_odd ζ _ measurable_logCosh he hm Real.tanh_neg
  · rw [hmean]
    exact fieldSpinTransition_monotone hζ _ measurable_logCosh he logCosh_linearGrowth
      hm Real.tanh_neg (field_tanh_monotone.monotoneOn _)
      (fun _ hz => field_tanh_nonneg hz) field_abs_tanh_le_one
  · intro z hz
    rw [hmeanPoint]
    exact fieldSpinTransition_nonneg ζ _ measurable_logCosh he logCosh_linearGrowth
      hm Real.tanh_neg (fun _ hy => field_tanh_nonneg hy) field_abs_tanh_le_one hz
  · intro z
    rw [hmeanPoint]
    exact fieldSpinTransition_bound ζ _ measurable_logCosh logCosh_linearGrowth
      field_abs_tanh_le_one z

theorem fieldTerminal_earlier_squares_antitone (a ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1)
    {t s : ℝ} (ht : t ∈ Ioi (-a)) (hs : s ∈ Ioi (-a)) (hts : t ≤ s) :
    let G := fieldTerminalFamily a ζ
    ∀ i z, fieldScalarSquares P (fun y => G.U (s, y)) (fun y => G.X (s, y)) i z ≤
      fieldScalarSquares P (fun y => G.U (t, y)) (fun y => G.X (t, y)) i z := by
  have hshape (q : ℝ) := fieldTerminalFamily_shape a ζ hζ0 q
  exact (fieldTerminalFamily a ζ).earlier_squares_antitone_parameter (convex_Ioi (-a))
    (fun q _ => fieldTerminalFamily_tangent_antitone a ζ hζ1 q)
    (fun q _ => (hshape q).1) (fun q _ => (hshape q).2.1)
    (fun q _ => (hshape q).2.2.1) (fun q _ => (hshape q).2.2.2.1)
    (fun p => (hshape p.1).2.2.2.2 p.2) P hP ht hs hts

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRootOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed-coordinate order after the final ordinary Gaussian root
average. Positive cascade exponents are required only for the interior
prefix; the root exponent remains zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarOverlaps_antitone_of_squares (P : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hP : ∀ av ∈ P, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hFG : HasLinearGrowth F)
    (hG : Measurable G) (hGG : HasLinearGrowth G)
    (ha : Measurable a) (haB : ∀ z, |a z| ≤ 1)
    (hb : Measurable b) (hbB : ∀ z, |b z| ≤ 1)
    (hle : ∀ i z, fieldScalarSquares P G b i z ≤ fieldScalarSquares P F a i z)
    (i : Fin (P.length + 1)) :
    fieldScalarOverlaps P root G b i ≤ fieldScalarOverlaps P root F a i := by
  have hrF := fieldScalarSquares_regular P hP hF hFG ha haB i
  have hrG := fieldScalarSquares_regular P hP hG hGG hb hbB i
  have hiF : Integrable (fieldScalarSquares P F a i) (gaussianReal 0 root) :=
    Integrable.of_bound hrF.1.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrF.2 z).1]
      exact (hrF.2 z).2)
  have hiG : Integrable (fieldScalarSquares P G b i) (gaussianReal 0 root) :=
    Integrable.of_bound hrG.1.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrG.2 z).1]
      exact (hrG.2 z).2)
  exact integral_mono hiG hiF (hle i)

theorem fieldAdjacent_earlier_overlaps_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1) (root : ℝ≥0)
    {t s : ℝ} (ht : t ∈ Ioo (-a) b) (hss : s ∈ Ioo (-a) b) (hts : t ≤ s)
    (i : Fin (P.length + 1)) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    fieldScalarOverlaps P root (fun y => G.U (s, y)) (fun y => G.X (s, y)) i ≤
      fieldScalarOverlaps P root (fun y => G.U (t, y)) (fun y => G.X (t, y)) i := by
  let G := fieldAdjacentFamily a b ζ η L hb hs
  have hshape q := fieldAdjacentFamily_shape a b ζ η L hb hs hζ
    (lt_of_lt_of_le hζ hζη) htail q
  exact fieldScalarOverlaps_antitone_of_squares P root hP
    (G.mU.comp (by fun_prop)) (G.growth t)
    (G.mU.comp (by fun_prop)) (G.growth s)
    (G.mX.comp (by fun_prop)) (fun z => (hshape t).2.2.2.2 z)
    (G.mX.comp (by fun_prop)) (fun z => (hshape s).2.2.2.2 z)
    (fieldAdjacent_earlier_squares_antitone a b ζ η L hb hs hζ hζη htail P hP ht hss hts) i

theorem fieldTerminal_earlier_overlaps_antitone (a ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1) (root : ℝ≥0)
    {t s : ℝ} (ht : t ∈ Ioi (-a)) (hs : s ∈ Ioi (-a)) (hts : t ≤ s)
    (i : Fin (P.length + 1)) :
    let G := fieldTerminalFamily a ζ
    fieldScalarOverlaps P root (fun y => G.U (s, y)) (fun y => G.X (s, y)) i ≤
      fieldScalarOverlaps P root (fun y => G.U (t, y)) (fun y => G.X (t, y)) i := by
  let G := fieldTerminalFamily a ζ
  have hshape q := fieldTerminalFamily_shape a ζ hζ0 q
  exact fieldScalarOverlaps_antitone_of_squares P root hP
    (G.mU.comp (by fun_prop)) (G.growth t)
    (G.mU.comp (by fun_prop)) (G.growth s)
    (G.mX.comp (by fun_prop)) (fun z => (hshape t).2.2.2.2 z)
    (G.mX.comp (by fun_prop)) (fun z => (hshape s).2.2.2.2 z)
    (fieldTerminal_earlier_squares_antitone a ζ hζ0 hζ1 P hP ht hs hts) i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAdjacentScalarLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjacent and final height-variation families have the same
literal scalar transition lists used in the original finite field model. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAdjacentAffineList_positive (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) :
    ∀ av ∈ fieldAdjacentAffineList a b ζ η L, ∀ t ∈ Ioo (-a) b,
      0 < av.base + av.slope * t := by
  intro av hav t ht
  rcases List.mem_cons.mp hav with rfl | hav
  · change 0 < a + 1 * t
    linarith [ht.1]
  · rcases List.mem_cons.mp hav with rfl | hav
    · change 0 < b + (-1) * t
      linarith [ht.2]
    · rw [hs av hav, zero_mul, add_zero]
      exact hb av hav

lemma fieldAdjacentFamily_scalar (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η L hb hs).U (t, z)) =
      fieldScalarValue (fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t)
        (fun z => Real.log (Real.cosh z)) := by
  let M := fieldAdjacentAffineList a b ζ η L
  let hM := fieldAdjacentAffineList_positive a b ζ η L hb hs
  have he : fieldAdjacentFamily a b ζ η L hb hs =
      fieldAffineFamily (Ioo (-a) b) isOpen_Ioo M hM := rfl
  rw [he, fieldAffineFamily_value]
  exact fieldAffineValue_scalar M t

lemma fieldAdjacentFamily_scalar_mean (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η L hb hs).X (t, z)) =
      fieldScalarMean (fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t)
        (fun z => Real.log (Real.cosh z)) Real.tanh := by
  let M := fieldAdjacentAffineList a b ζ η L
  let hM := fieldAdjacentAffineList_positive a b ζ η L hb hs
  have he : fieldAdjacentFamily a b ζ η L hb hs =
      fieldAffineFamily (Ioo (-a) b) isOpen_Ioo M hM := rfl
  rw [he]
  exact fieldAffineFamily_mean (Ioo (-a) b) isOpen_Ioo M hM t

lemma fieldAdjacentAffineList_increments (a b ζ η : ℝ) (L : List FieldAffineStep) (t : ℝ) :
    fieldAffineIncrements (fieldAdjacentAffineList a b ζ η L) t =
      (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: fieldAffineIncrements L t := by
  simp only [fieldAffineIncrements, fieldAdjacentAffineList, List.map_cons, one_mul,
    neg_one_mul, sub_eq_add_neg]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldCovarianceScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact change of position units between scaled covariance and scaled
terminal log-cosh in the finite one-site field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma gaussianOperator_scale_position (a v c : ℝ) (hc : 0 ≤ c)
    (F : ℝ → ℝ) (z : ℝ) :
    gaussianOperator a v (fun u => F (c * u)) z =
      gaussianOperator a (c ^ 2 * v) F (c * z) := by
  have hs : Real.sqrt (c ^ 2 * v) = c * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have he (g : ℝ) : c * (z + Real.sqrt v * g) = c * z + (c * Real.sqrt v) * g := by ring
  simp only [gaussianOperator, hs, he]

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

lemma coordinate_gradient_derivative (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => F.P i (Function.update r j (r j + t), z))
      (F.PP i j (r, z)) 0 := by
  classical
  have hv : HasDerivAt (fun t : ℝ => Function.update r j (r j + t)) (Pi.single j 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hkj : k = j
    · subst k
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (r j)
    · simpa [Function.update_of_ne hkj, Pi.single_eq_of_ne hkj] using
        hasDerivAt_const (0 : ℝ) (r k)
  have hp := hv.prodMk (hasDerivAt_const (0 : ℝ) z)
  have hF : HasFDerivAt (F.P i) (fieldFiniteLinear (fun k => F.PP i k (r, z)) (F.PX i (r, z)))
      (Function.update r j (r j + 0), z) := by simpa using F.derivativeP i (r, z) hr
  have hd := hF.comp_hasDerivAt 0 hp
  simpa [fieldFiniteLinear_apply, Function.comp_def, Pi.single_apply] using hd

lemma line_derivative (r c : Fin n → ℝ) (z t : ℝ) (hr : r + t • c ∈ I) :
    HasDerivAt (fun s : ℝ => F.U (r + s • c, z))
      (∑ i, F.P i (r + t • c, z) * c i) t := by
  have hv := (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const c)
  have hp := hv.prodMk (hasDerivAt_const t z)
  have hd := (F.derivative (r + t • c, z) hr).comp_hasDerivAt t hp
  simpa [fieldFiniteLinear_apply, Function.comp_def] using hd

lemma line_gradient_derivative (r c : Fin n → ℝ) (z t : ℝ) (hr : r + t • c ∈ I) :
    HasDerivAt (fun s : ℝ => ∑ i, F.P i (r + s • c, z) * c i)
      (∑ i, ∑ j, F.PP i j (r + t • c, z) * c i * c j) t := by
  have hv := (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const c)
  have hp := hv.prodMk (hasDerivAt_const t z)
  have hd (i : Fin n) : HasDerivAt (fun s => F.P i (r + s • c, z) * c i)
      ((∑ j, F.PP i j (r + t • c, z) * c j) * c i) t := by
    simpa [fieldFiniteLinear_apply, Function.comp_def] using
      ((F.derivativeP i (r + t • c, z) hr).comp_hasDerivAt t hp).mul_const (c i)
  refine ((HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hd i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [Finset.sum_apply]
  · simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end FieldFiniteFamily
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldFiniteSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite height Hessian criterion and its supporting-plane
consequence. The conclusion assumes the mixed and radial derivative signs of the
scalar Ising recursion. -/

noncomputable section
open Set IsingPerceptron
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma hessian_nonpos (r : Fin n → ℝ) (z : ℝ) (hr : r ∈ I)
    (hpos : ∀ i, 0 < r i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ F.PP i j (r, z))
    (hrow : ∀ i, ∑ j, F.PP i j (r, z) * r j ≤ 0) (x : Fin n → ℝ) :
    ∑ i, ∑ j, F.PP i j (r, z) * x i * x j ≤ 0 := by
  have hq := field_quadratic_nonneg_of_positive_scaling
    (fun i j => -F.PP i j (r, z)) r
    (fun i j => congrArg Neg.neg (F.symmetric i j (r, z) hr))
    (fun i j hij => neg_nonpos.mpr (hoff i j hij)) hpos
    (fun i => by simpa only [neg_mul, Finset.sum_neg_distrib] using neg_nonneg.mpr (hrow i)) x
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonneg] using hq

/-- A supporting plane follows from the Hessian sign criterion along a
segment. Existence of the second derivatives suffices; continuity of the
second derivatives is not assumed. -/
theorem support_of_hessian (hI : Convex ℝ I) (r s : Fin n → ℝ) (z : ℝ)
    (hr : r ∈ I) (hs : s ∈ I)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ i, ∑ j, F.PP i j (r + t • (s - r), z) * (s i - r i) * (s j - r j) ≤ 0) :
    F.U (s, z) ≤ F.U (r, z) + ∑ i, F.P i (r, z) * (s i - r i) := by
  let c := s - r
  let f := fun t : ℝ => F.U (r + t • c, z)
  let g := fun t : ℝ => ∑ i, F.P i (r + t • c, z) * c i
  let q := fun t : ℝ => ∑ i, ∑ j, F.PP i j (r + t • c, z) * c i * c j
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • c ∈ I := by
    have he : r + t • c = (1 - t) • r + t • s := by
      dsimp only [c]
      module
    rw [he]
    exact hI hr hs (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g t) t :=
    F.line_derivative r c z t (hp t ht)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (q t) t :=
    F.line_gradient_derivative r c z t (hp t ht)
  have hanti : AntitoneOn g (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hq t (interior_subset ht))
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv f t ≤ g 0 := by
    intro t ht
    have ht' := interior_subset ht
    rw [(hf t ht').deriv]
    exact hanti (by simp) ht' ht'.1
  have hslope := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) 1 (by simp) zero_le_one
  have he0 : r + (0 : ℝ) • c = r := by simp
  have he1 : r + (1 : ℝ) • c = s := by dsimp only [c]; module
  dsimp only [f, g] at hslope
  rw [he0, he1] at hslope
  simpa only [sub_zero, mul_one, c, Pi.sub_apply, add_comm] using (sub_le_iff_le_add.mp hslope)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.fieldAllIncrements_length _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual magnetization-overlap path for a finite scalar Ising field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma scalarFieldIncrements_value (h : FieldStep) :
    fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) =
      (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
        (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) := by
  unfold fieldScalarValue scalarFieldIncrements
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldValue_scalar_chain (h : FieldStep) :
    fieldValue h 0 = gaussianOperator 0 (h.height 0)
      (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) 0 -
      h.height (Fin.last h.depth) / 2 := by
  rw [scalarFieldIncrements_value, fieldValue, List.ofFn_succ, List.foldr_cons]
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    simp [fieldIncrement, h.first]
  rw [hroot]

lemma fieldMagnetizationPath_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldMagnetizationPath h s = fieldMagnetizationLevel h i :=
  fieldLevelPath_on_cell h _ _ _ i hs

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

lemma fieldAllSquares_magnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldScalarSquares (fieldAllIncrements h) (fun y => Real.log (Real.cosh y))
      Real.tanh ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ 0 = fieldMagnetizationLevel h i := by
  have hroot := fieldAllIncrements_root h
  let j : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have hs := fieldScalarSquares_congr_list hroot
    (fun y => Real.log (Real.cosh y)) Real.tanh
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ j.succ (by rfl)
  rw [congrFun hs 0]
  change fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)))
    (fieldScalarSquares (scalarFieldIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh j) 0 = _
  simp only [fieldSpinTransition, integral_tilted_eq_div, zero_mul, Real.exp_zero,
    one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, div_one]
  rfl

private lemma terminal_list_zero (h : FieldStep) :
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 0 =
      fieldAllIncrements h := by
  let L := fieldAllIncrements h
  have hlen : L.length = h.depth + 1 := fieldAllIncrements_length h
  have hget : L[h.depth] = ((fieldIncrement h (Fin.last h.depth)).1,
      NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth))) := by
    exact List.getElem_ofFn _
  unfold fieldTerminalIncrements
  simp only [add_zero]
  rw [show Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2 =
      NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth)) by
      change Real.toNNReal (↑(NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth)))) = _
      exact Real.toNNReal_coe, ← hget]
  rw [List.take_concat_get' L h.depth (by rw [hlen]; omega)]
  exact List.take_of_length_le (by rw [hlen])

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

/-- The exact interior coordinate gradient in `fld:gradient`, expressed
with the already constructed physical magnetization-overlap levels. -/
lemma hasDerivAt_fieldInteriorChart_magnetization (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldInteriorChart h i t 0)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        fieldMagnetizationLevel h i.castSucc) 0 := by
  have hd := hasDerivAt_fieldInteriorChart h i hstrict 0
  have hs : fieldScalarSquares (fieldAllIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh
      ⟨i.val + 1, by simp⟩ 0 =
      fieldMagnetizationLevel h i.castSucc := by
    simpa only [Fin.val_castSucc] using fieldAllSquares_magnetization h i.castSucc
  rw [hs] at hd
  exact hd

lemma hasDerivAt_fieldFinalChart (h : FieldStep)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldFinalChart h t 0)
      (-(1 - h.cut (Fin.last h.depth).castSucc) / 2 *
        fieldMagnetizationLevel h (Fin.last h.depth)) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take h.depth, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have ht : (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) := by
    change -(fieldIncrement h (Fin.last h.depth)).2 < 0
    linarith [hstrict (Fin.last h.depth)]
  have hd := hasDerivAt_fieldTerminalValue (L.take h.depth) hP
    (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1
    (h.height (Fin.last h.depth)) 0 0 ht
  have hs := fieldScalarSquares_congr_list (terminal_list_zero h)
    (fun y => Real.log (Real.cosh y)) Real.tanh
    (fieldTerminalLevel (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 0)
    ⟨(Fin.last h.depth).val + 1, by simp⟩ (by
      simp [fieldTerminalLevel, fieldAppendIndex, L])
  rw [congrFun hs 0, fieldAllSquares_magnetization] at hd
  exact hd

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

lemma hasDerivAt_fieldHeightCoordinate_interior (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i.castSucc t 0)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        fieldMagnetizationLevel h i.castSucc) 0 := by
  have he : (fun t => fieldHeightCoordinateValue h i.castSucc t 0) =
      fun t => fieldInteriorChart h i t 0 := by
    funext t
    exact fieldHeightCoordinateValue_interior h i t 0
  rw [he]
  exact hasDerivAt_fieldInteriorChart_magnetization h i hstrict

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

/-- Exact finite-coordinate gradient of the actual field functional,
including the zero root exponent and the final diagonal subtraction. -/
lemma hasDerivAt_fieldHeightCoordinate (h : FieldStep) (i : Fin (h.depth + 1))
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i t 0)
      (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : (fun t => fieldHeightCoordinateValue h (Fin.last h.depth) t 0) =
        fun t => fieldFinalChart h t 0 := by
      funext t
      exact fieldHeightCoordinateValue_final h t 0
    rw [he]
    simpa only [Fin.succ_last, h.last] using hasDerivAt_fieldFinalChart h hstrict
  · exact hasDerivAt_fieldHeightCoordinate_interior h j hstrict

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightGradient
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the jointly constructed height gradient with the
actual scalar magnetization. The terminal centering is retained explicitly. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFinite_centered_coordinate_derivative (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), 0) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2)
      (F.P i (r, 0) - if i = Fin.last h.depth then 1 / 2 else 0) 0 := by
  classical
  have hd := F.coordinate_derivative r 0 hr i
  by_cases hi : i = Fin.last h.depth
  · subst i
    have hc : HasDerivAt (fun t : ℝ => (r (Fin.last h.depth) + t) / 2) (1 / 2 : ℝ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (r (Fin.last h.depth))).div_const 2
    refine ((hd.sub hc).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      simp only [Pi.sub_apply, Function.update_self]
    · simp
  · have hn : Fin.last h.depth ≠ i := Ne.symm hi
    simpa [Function.update_of_ne hn, hi] using
      hd.sub_const (r (Fin.last h.depth) / 2)

/-- The exact literal-height gradient. `F` is derivative data constructed
from the finite Gaussian recursion; the equality of its value is the only
identification required here. -/
theorem fieldHeight_gradient_identification (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    F.P i (r, 0) - (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        fieldMagnetizationLevel (fieldStepOfStrictHeights h r hs) i := by
  let k := fieldStepOfStrictHeights h r hs
  have hd := fieldFinite_centered_coordinate_derivative h F r hr i
  have he : (fun t : ℝ => F.U (Function.update r i (r i + t), 0) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2) =
      fun t => fieldHeightCoordinateValue k i t 0 := by
    funext t
    rw [hU]
    change fieldHeightJointValue k (Function.update k.height i (k.height i + t)) 0 = _
    exact fieldHeightJointValue_update k i t 0
  rw [he] at hd
  have hk := hasDerivAt_fieldHeightCoordinate k i
    (fun j => fieldStepOfStrictHeights_strict h r hs j)
  exact hd.unique hk

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightLists
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transition-list laws for a literal height update. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_withHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldAllIncrements (fieldWithHeights h r hr0 hrmono) =
      List.ofFn (fun j : Fin (h.depth + 1) =>
        (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j))) := by
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact (Real.toNNReal_of_nonneg (fieldIncrement_nonneg (fieldWithHeights h r hr0 hrmono) j)).symm

lemma fieldAllIncrements_update_interior (h : FieldStep) (j : Fin h.depth) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      fieldAdjacentIncrements ((fieldAllIncrements h).take j.val)
        ((fieldAllIncrements h).drop (j.val + 2))
        (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
        (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_interior h j t

lemma fieldAllIncrements_update_final (h : FieldStep) (t : ℝ)
    (ht : Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) ht) =
      fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
        (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_final h t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRootPrefixLaw
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the original magnetization levels after
splitting off the root and an unchanged prefix of scalar transitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldMagnetizationLevel_root_prefix (h : FieldStep)
    (P S : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : fieldAllIncrements h = (0, root) :: (P ++ S))
    (i : Fin (h.depth + 1)) (j : Fin (P.length + 1)) (hij : i.val = j.val) :
    fieldMagnetizationLevel h i =
      fieldScalarOverlaps P root
        (fieldScalarValue S (fun z => Real.log (Real.cosh z)))
        (fieldScalarMean S (fun z => Real.log (Real.cosh z)) Real.tanh) j := by
  let i' : Fin ((fieldAllIncrements h).length + 1) :=
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩
  have he := fieldScalarSquares_congr_list hL (fun z => Real.log (Real.cosh z))
    Real.tanh i' (fieldPrefixIndex P S j).succ (by
      simp only [i', fieldPrefixIndex, Fin.val_succ]
      omega)
  rw [← fieldAllSquares_magnetization h i]
  change fieldScalarSquares (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
    Real.tanh i' 0 = _
  rw [congrFun he 0]
  change fieldSpinTransition 0 root (fieldScalarValue (P ++ S) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (P ++ S) (fun z => Real.log (Real.cosh z))
      Real.tanh (fieldPrefixIndex P S j)) 0 = _
  rw [fieldScalarSquares_append_prefix]
  simp only [fieldSpinTransition, integral_tilted_eq_div, zero_mul, Real.exp_zero,
    one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, div_one]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightInteriorLaw
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual interior-height magnetization as the root average of the
adjacent Gaussian variation family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_update_interior_root (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (fieldInteriorPrefix h j ++
          ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
          ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
          fieldInteriorTail h j) := by
  rw [fieldAllIncrements_update_interior, fieldAdjacentIncrements, fieldAllIncrements_root]
  obtain ⟨l, hl⟩ : ∃ l, j.val = l + 1 := ⟨j.val - 1, by omega⟩
  simp only [fieldInteriorPrefix, fieldInteriorTail, hl, Nat.add_sub_cancel,
    List.take_succ_cons, List.drop_succ_cons, List.cons_append]

theorem fieldMagnetizationLevel_interior_family (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (j : Fin h.depth) (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth)
    (i : Fin (h.depth + 1)) (hij : i.val < j.val) :
    let S := fieldInteriorTail h j
    let G := fieldAdjacentFamily (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
      (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 (fieldFixedAffine S)
      (fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)) (fieldFixedAffine_slope S)
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) i =
      fieldScalarOverlaps (fieldInteriorPrefix h j) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun y => G.U (t, y)) (fun y => G.X (t, y))
        ⟨i.val, by rw [fieldInteriorPrefix_length]; omega⟩ := by
  dsimp only
  let P := fieldInteriorPrefix h j
  let S := fieldInteriorTail h j
  let a := (fieldIncrement h j.castSucc).2
  let b := (fieldIncrement h j.succ).2
  let ζ := (fieldIncrement h j.castSucc).1
  let η := (fieldIncrement h j.succ).1
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)
  let hs := fieldFixedAffine_slope S
  have hvalue := fieldAdjacentFamily_scalar a b ζ η L hb hs t
  have hmean := fieldAdjacentFamily_scalar_mean a b ζ η L hb hs t
  rw [fieldAdjacentAffineList_increments, fieldFixedAffine_increments] at hvalue hmean
  rw [hvalue, hmean]
  exact fieldMagnetizationLevel_root_prefix _ P
    ((ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S)
    (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldAllIncrements_update_interior_root h j hj t ht) i
    ⟨i.val, by dsimp only [P]; rw [fieldInteriorPrefix_length]; omega⟩ rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightInteriorOrder
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mixed-height order for nonterminal coordinates. The unchanged
root has exponent zero and is integrated only after the positive prefix. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

theorem fieldHeight_interior_earlier_antitone (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (j : Fin h.depth) (hj : 0 < j.val) (i : Fin (h.depth + 1)) (hij : i.val < j.val)
    {t s : ℝ}
    (ht : t ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2)
    (hs : s ∈ Ioo (-(fieldIncrement h j.castSucc).2) (fieldIncrement h j.succ).2)
    (hts : t ≤ s) :
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + s))
      (fieldHeight_update_interior_mem h hstrict j s hs)) i ≤
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t))
      (fieldHeight_update_interior_mem h hstrict j t ht)) i := by
  let P := fieldInteriorPrefix h j
  let S := fieldInteriorTail h j
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S (fieldInteriorTail_strict h j hstrict)
  let hz := fieldFixedAffine_slope S
  have hP : ∀ av ∈ P, 0 < av.1 := by
    intro av hav
    exact scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hL : ∀ av ∈ L, 0 < av.exponent := by
    intro av hav
    obtain ⟨bv, hv, rfl⟩ := List.mem_map.mp hav
    exact scalarFieldIncrements_positive h bv (List.mem_of_mem_drop hv)
  have hζ : 0 < (fieldIncrement h j.castSucc).1 := by
    change 0 < h.cut j.castSucc.castSucc
    rw [← h.first]
    exact h.ordered_cut (by change 0 < j.val; exact hj)
  have hζη : (fieldIncrement h j.castSucc).1 ≤ (fieldIncrement h j.succ).1 := by
    apply h.ordered_cut.monotone
    change j.val ≤ j.val + 1
    omega
  rw [fieldMagnetizationLevel_interior_family h hstrict j hj s _ i hij,
    fieldMagnetizationLevel_interior_family h hstrict j hj t _ i hij]
  exact fieldAdjacent_earlier_overlaps_antitone
    (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
    (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 L hb hz hζ hζη hL P hP
    (NNReal.mk (h.height 0) (h.nonneg 0)) ht hs hts _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightFinalOrder
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final-height version of the actual mixed-coordinate order. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_update_final_root (h : FieldStep) (hn : 0 < h.depth) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (fieldFinalPrefix h ++ [((fieldIncrement h (Fin.last h.depth)).1,
          Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))]) := by
  rw [fieldAllIncrements_update_final, fieldTerminalIncrements, fieldAllIncrements_root]
  obtain ⟨l, hl⟩ : ∃ l, h.depth = l + 1 := ⟨h.depth - 1, by omega⟩
  simp only [fieldFinalPrefix, hl, Nat.add_sub_cancel, List.take_succ_cons, List.cons_append]

lemma fieldMagnetizationLevel_final_family (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) (hn : 0 < h.depth) (t : ℝ)
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) :
    let G := fieldTerminalFamily (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) i =
      fieldScalarOverlaps (fieldFinalPrefix h) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun y => G.U (t, y)) (fun y => G.X (t, y))
        ⟨i.val, by rw [fieldFinalPrefix_length]; omega⟩ := by
  dsimp only
  let a := (fieldIncrement h (Fin.last h.depth)).2
  let ζ := (fieldIncrement h (Fin.last h.depth)).1
  have hvalue := fieldTerminalFamily_value_eq_operator a ζ t
  have hmean := fieldTerminalFamily_mean_eq_transition a ζ t
  rw [hvalue, hmean]
  exact fieldMagnetizationLevel_root_prefix _ (fieldFinalPrefix h)
    [(ζ, Real.toNNReal (a + t))] (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldAllIncrements_update_final_root h hn t ht hstrict) i
    ⟨i.val, by rw [fieldFinalPrefix_length]; omega⟩ rfl

theorem fieldHeight_final_earlier_antitone (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2)
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) {t s : ℝ}
    (ht : t ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2))
    (hs : s ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2)) (hts : t ≤ s) :
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + s))
      (fieldHeight_update_final_mem h hstrict s hs)) i ≤
    fieldMagnetizationLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t))
      (fieldHeight_update_final_mem h hstrict t ht)) i := by
  have hn : 0 < h.depth := by omega
  have hP : ∀ av ∈ fieldFinalPrefix h, 0 < av.1 := by
    intro av hav
    exact scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hζ0 : 0 ≤ (fieldIncrement h (Fin.last h.depth)).1 := by
    change 0 ≤ h.cut (Fin.last h.depth).castSucc
    rw [← h.first]
    exact h.ordered_cut.monotone (Fin.zero_le _)
  have hζ1 : (fieldIncrement h (Fin.last h.depth)).1 ≤ 1 := by
    change h.cut (Fin.last h.depth).castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  rw [fieldMagnetizationLevel_final_family h hstrict hn s hs i hi,
    fieldMagnetizationLevel_final_family h hstrict hn t ht i hi]
  exact fieldTerminal_earlier_overlaps_antitone _ _ hζ0 hζ1 (fieldFinalPrefix h) hP
    (NNReal.mk (h.height 0) (h.nonneg 0)) ht hs hts _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRadialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial increase of the actual conditional spin products, expressed
in the original Gaussian position units. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarOverlaps_radial (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root (fun z => Real.log (Real.cosh (c * z)))
        (fun z => Real.tanh (c * z)) i ≤
      fieldScalarOverlaps L root (fun z => Real.log (Real.cosh (d * z)))
        (fun z => Real.tanh (d * z)) i := by
  have hd : 0 ≤ d := hc.trans hcd
  have hFm (r : ℝ) : Measurable (fun z => Real.log (Real.cosh (r * z))) :=
    measurable_logCosh.comp (measurable_id.const_mul r)
  have hFg (r : ℝ) : HasLinearGrowth (fun z => Real.log (Real.cosh (r * z))) :=
    logCosh_linearGrowth.scale_argument r
  have hFe (r : ℝ) : Function.Even (fun z => Real.log (Real.cosh (r * z))) := by
    intro z
    simp only [mul_neg, Real.cosh_neg]
  have ham (r : ℝ) : Measurable (fun z => Real.tanh (r * z)) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hao (r : ℝ) : Function.Odd (fun z => Real.tanh (r * z)) := by
    intro z
    simp only [mul_neg, Real.tanh_neg]
  have hamo (r : ℝ) (hr : 0 ≤ r) : MonotoneOn (fun z => Real.tanh (r * z)) (Ici 0) := by
    intro x _hx y _hy hxy
    exact field_tanh_monotone (mul_le_mul_of_nonneg_left hxy hr)
  have hap (r : ℝ) (hr : 0 ≤ r) : ∀ z ∈ Ici (0 : ℝ), 0 ≤ Real.tanh (r * z) :=
    fun z hz => field_tanh_nonneg (mul_nonneg hr hz)
  have haB (r : ℝ) : ∀ z : ℝ, |Real.tanh (r * z)| ≤ 1 :=
    fun z => field_abs_tanh_le_one (r * z)
  have hab : ∀ z ∈ Ici (0 : ℝ), Real.tanh (c * z) ≤ Real.tanh (d * z) :=
    fun z hz => field_tanh_monotone (mul_le_mul_of_nonneg_right hcd hz)
  have horder := fieldScalarSquares_order L hL (hFm c) (hFm d) (hFg c) (hFg d)
    (hFe c) (hFe d) (field_logcosh_scaled_difference_monotone hc hcd)
    (ham c) (ham d) (hao c) (hao d) (hamo c hc) (hamo d hd)
    (hap c hc) (hap d hd) (haB c) (haB d) hab
  have hi (r : ℝ) : Integrable
      (fieldScalarSquares L (fun z => Real.log (Real.cosh (r * z)))
        (fun z => Real.tanh (r * z)) i) (gaussianReal 0 root) := by
    have hr := fieldScalarSquares_regular L hL (hFm r) (hFg r) (ham r) (haB r) i
    exact Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]
        exact (hr.2 z).2))
  exact integral_mono (hi c) (hi d) (horder i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of position units for the actual finite conditional spin
chain. The spin observable acquires no multiplicative derivative factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

private lemma scalar_value_measurable (L : List (ℝ × ℝ≥0))
    {F : ℝ → ℝ} (hF : Measurable F) : Measurable (fieldScalarValue L F) := by
  induction L with
  | nil => exact hF
  | cons av L ih =>
    change Measurable (gaussianOperator av.1 av.2 (fieldScalarValue L F))
    rw [gaussianOperator_eq_transform]
    exact measurable_gaussianTransform ih _ _

private lemma scalar_mean_measurable (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) :
    Measurable (fieldScalarMean L F a) := by
  induction L with
  | nil => exact ha
  | cons av L ih =>
    exact measurable_fieldSpinTransition av.1 av.2 (scalar_value_measurable L hF) ih

private lemma scalar_squares_measurable (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) :
    ∀ i, Measurable (fieldScalarSquares L F a i) := by
  induction L with
  | nil => intro i; exact ha.pow_const 2
  | cons av L ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (scalar_mean_measurable (av :: L) hF ha).pow_const 2
    · exact measurable_fieldSpinTransition av.1 av.2 (scalar_value_measurable L hF) (ih j)

lemma fieldSpinTransition_scale_position (ζ : ℝ) (v c : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v (fun u => F (c * u)) (fun u => a (c * u)) z =
      fieldSpinTransition ζ (c ^ 2 * v) F a (c * z) := by
  have hFc : Measurable (fun u => F ((c : ℝ) * u)) := hF.comp (measurable_id.const_mul _)
  have hac : Measurable (fun u => a ((c : ℝ) * u)) := ha.comp (measurable_id.const_mul _)
  rw [fieldSpinTransition_eq_standard ζ v hFc hac,
    fieldSpinTransition_eq_standard ζ (c ^ 2 * v) hF ha,
    gaussianTiltAverage_eq_div, gaussianTiltAverage_eq_div]
  have hs : Real.sqrt ((c ^ 2 * v : ℝ≥0) : ℝ) = c * Real.sqrt (v : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq c.coe_nonneg]
  have he (u : ℝ) : (c : ℝ) * (z + Real.sqrt (v : ℝ) * u) =
      c * z + (c * Real.sqrt (v : ℝ)) * u := by ring
  simp only [hs, he]

lemma fieldScalarValue_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (F : ℝ → ℝ) (z : ℝ) :
    fieldScalarValue L (fun u => F (c * u)) z =
      fieldScalarValue (fieldScaleIncrements c L) F (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    have he : fieldScalarValue L (fun u => F (c * u)) =
        fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) := funext ih
    change gaussianOperator av.1 av.2 (fieldScalarValue L (fun u => F (c * u))) z =
      gaussianOperator av.1 (c ^ 2 * av.2 : ℝ≥0) (fieldScalarValue (fieldScaleIncrements c L) F) (c * z)
    rw [he]
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      gaussianOperator_scale_position av.1 av.2 c c.coe_nonneg _ z

lemma fieldScalarMean_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u)) z =
      fieldScalarMean (fieldScaleIncrements c L) F a (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    have hv : fieldScalarValue L (fun u => F (c * u)) =
        fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) :=
      funext (fieldScalarValue_scale_position c L F)
    have hm : fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u)) =
        fun u => fieldScalarMean (fieldScaleIncrements c L) F a (c * u) := funext ih
    change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun u => F (c * u)))
        (fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u))) z =
      fieldSpinTransition av.1 (c ^ 2 * av.2) (fieldScalarValue (fieldScaleIncrements c L) F)
        (fieldScalarMean (fieldScaleIncrements c L) F a) (c * z)
    rw [hv, hm]
    exact fieldSpinTransition_scale_position av.1 av.2 c
      (scalar_value_measurable _ hF) (scalar_mean_measurable _ hF ha) z

lemma fieldScalarSquares_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a)
    (i : Fin (L.length + 1)) (z : ℝ) :
    fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) i z =
      fieldScalarSquares (fieldScaleIncrements c L) F a
        (Fin.cast (by rw [fieldScaleIncrements_length]) i) (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cast_zero, fieldScalarSquares_zero] using
        congrArg (fun x : ℝ => x ^ 2) (fieldScalarMean_scale_position c (av :: L) hF ha z)
    · have hv : fieldScalarValue L (fun u => F (c * u)) =
          fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) :=
        funext (fieldScalarValue_scale_position c L F)
      have hq : fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) j =
          fun u => fieldScalarSquares (fieldScaleIncrements c L) F a
            (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) j) (c * u) := funext (ih j)
      change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun u => F (c * u)))
          (fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) j) z =
        fieldSpinTransition av.1 (c ^ 2 * av.2) (fieldScalarValue (fieldScaleIncrements c L) F)
          (fieldScalarSquares (fieldScaleIncrements c L) F a
            (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) j)) (c * z)
      rw [hv, hq]
      exact fieldSpinTransition_scale_position av.1 av.2 c
        (scalar_value_measurable _ hF) (scalar_squares_measurable _ hF ha _) z

lemma fieldScalarOverlaps_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (root : ℝ≥0) {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a)
    (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root (fun u => F (c * u)) (fun u => a (c * u)) i =
      fieldScalarOverlaps (fieldScaleIncrements c L) (c ^ 2 * root) F a
        (Fin.cast (by rw [fieldScaleIncrements_length]) i) := by
  have hs : NNReal.mk ((c : ℝ) ^ 2) (sq_nonneg _) = c ^ 2 := by
    apply Subtype.ext
    rfl
  have hm : (gaussianReal 0 root).map (fun u : ℝ => (c : ℝ) * u) =
      gaussianReal 0 (c ^ 2 * root) := by
    simpa only [mul_zero, hs] using
      gaussianReal_map_const_mul (μ := 0) (v := root) (c : ℝ)
  unfold fieldScalarOverlaps
  simp_rw [fieldScalarSquares_scale_position c L hF ha i]
  rw [← hm]
  have hc : Measurable (fun u : ℝ => (c : ℝ) * u) := measurable_const.mul measurable_id
  exact (integral_map hc.aemeasurable
    (scalar_squares_measurable _ hF ha _).aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRadialCovariance
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial monotonicity of the actual finite-field overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma scalarFieldIncrements_scale (h : FieldStep) (c : ℝ≥0) :
    scalarFieldIncrements (fieldScaleCovariance h c) =
      fieldScaleIncrements c (scalarFieldIncrements h) := by
  unfold scalarFieldIncrements fieldScaleIncrements
  rw [List.map_ofFn]
  congr 1
  funext i
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (fieldIncrement (fieldScaleCovariance h c) i.succ).2 =
      (c : ℝ) ^ 2 * (fieldIncrement h i.succ).2
    simp only [fieldIncrement, fieldScaleCovariance]
    split_ifs <;> ring

private lemma overlaps_congr_list (L M : List (ℝ × ℝ≥0)) (he : L = M)
    (root : ℝ≥0) (F a : ℝ → ℝ) (i : Fin (L.length + 1)) (j : Fin (M.length + 1))
    (hij : i.val = j.val) :
    fieldScalarOverlaps L root F a i = fieldScalarOverlaps M root F a j := by
  subst M
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

lemma fieldMagnetizationLevel_scale (h : FieldStep) (c : ℝ≥0)
    (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel (fieldScaleCovariance h c) i =
      fieldScalarOverlaps (scalarFieldIncrements h) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun z => Real.log (Real.cosh ((c : ℝ) * z)))
        (fun z => Real.tanh ((c : ℝ) * z))
        (Fin.cast (by rw [scalarFieldIncrements_length]) i) := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have he := fieldScalarOverlaps_scale_position c (scalarFieldIncrements h)
    (NNReal.mk (h.height 0) (h.nonneg 0)) measurable_logCosh hm
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  rw [he]
  unfold fieldMagnetizationLevel
  have hroot : NNReal.mk ((fieldScaleCovariance h c).height 0)
      ((fieldScaleCovariance h c).nonneg 0) = c ^ 2 * NNReal.mk (h.height 0) (h.nonneg 0) := by
    apply Subtype.ext
    rfl
  rw [hroot]
  exact overlaps_congr_list _ _ (scalarFieldIncrements_scale h c) _ _ _ _ _ rfl

theorem fieldMagnetizationLevel_radial (h : FieldStep) {c d : ℝ≥0}
    (hcd : c ≤ d) (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel (fieldScaleCovariance h c) i ≤
      fieldMagnetizationLevel (fieldScaleCovariance h d) i := by
  rw [fieldMagnetizationLevel_scale, fieldMagnetizationLevel_scale]
  exact fieldScalarOverlaps_radial _ _ (scalarFieldIncrements_positive h) c.coe_nonneg
    (by exact_mod_cast hcd) _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRadialHessian
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
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

lemma fieldMagnetizationLevel_congr {h k : FieldStep} (he : h = k)
    (i : Fin (h.depth + 1)) (j : Fin (k.depth + 1)) (hij : i.val = j.val) :
    fieldMagnetizationLevel h i = fieldMagnetizationLevel k j := by
  cases he
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma fieldStrictHeightCone_smul {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) {a : ℝ} (ha : 0 < a) :
    a • r ∈ fieldStrictHeightCone n := by
  intro j
  have he : fieldHeightIncrement (a • r) j = a * fieldHeightIncrement r j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  exact mul_pos ha (hr j)

theorem fieldHeight_radial_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    ∑ j, F.PP i j (r, 0) * r j ≤ 0 := by
  classical
  let k := fieldStepOfStrictHeights h r hs
  let c : ℝ → ℝ≥0 := fun t => ⟨Real.sqrt (1 + t), Real.sqrt_nonneg _⟩
  let w := h.cut i.succ - h.cut i.castSucc
  let d := if i = Fin.last h.depth then (1 / 2 : ℝ) else 0
  let g := fun t : ℝ => -w / 2 * fieldMagnetizationLevel (fieldScaleCovariance k (c t)) i + d
  have hw : 0 ≤ w := sub_nonneg.mpr (h.ordered_cut.monotone i.castSucc_le_succ)
  have hg : Antitone g := by
    intro a b hab
    have hc : c a ≤ c b := by
      change Real.sqrt (1 + a) ≤ Real.sqrt (1 + b)
      exact Real.sqrt_le_sqrt (by linarith)
    have hb := fieldMagnetizationLevel_radial k hc i
    dsimp only [g]
    have hneg : -w / 2 ≤ 0 := by linarith
    have hh := mul_le_mul_of_nonpos_left hb hneg
    linarith
  have hm : Tendsto (fun t : ℝ => r + t • r) (𝓝 0) (𝓝 r) := by
    simpa using (show ContinuousAt (fun t : ℝ => r + t • r) 0 by fun_prop).tendsto
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), r + t • r ∈ I := hm.eventually (hI.mem_nhds hr)
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t :=
    (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds (by norm_num)
  have he : g =ᶠ[𝓝 0] fun t : ℝ => F.P i (r + t • r, 0) := by
    filter_upwards [hmem, hpos] with t htI ht
    have htR : r + t • r ∈ fieldStrictHeightCone h.depth := by
      have heq : r + t • r = (1 + t) • r := by module
      rw [heq]
      exact fieldStrictHeightCone_smul hs ht
    have hsq : (c t : ℝ) ^ 2 = 1 + t := Real.sq_sqrt ht.le
    have heq : r + t • r = fun j => (c t : ℝ) ^ 2 * r j := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsq]
      ring
    have hk : fieldStepOfStrictHeights h (r + t • r) htR =
        fieldScaleCovariance k (c t) := by
      unfold fieldStepOfStrictHeights fieldWithHeights fieldScaleCovariance k
      congr 1
    have hh := fieldHeight_gradient_identification h F hU (r + t • r) htI htR i
    rw [fieldMagnetizationLevel_congr hk i i rfl] at hh
    dsimp only [g, w, d]
    linarith
  have hd : HasDerivAt (fun t : ℝ => F.P i (r + t • r, 0))
      (∑ j, F.PP i j (r, 0) * r j) 0 := by
    have hv := (hasDerivAt_const (0 : ℝ) r).add ((hasDerivAt_id (0 : ℝ)).smul_const r)
    have hp : HasDerivAt (fun t : ℝ => (r + t • r, (0 : ℝ))) (r, 0) 0 := by
      simpa using hv.prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hF : HasFDerivAt (F.P i)
        (fieldFiniteLinear (fun j => F.PP i j (r, 0)) (F.PX i (r, 0)))
        (r + (0 : ℝ) • r, 0) := by simpa using F.derivativeP i (r, 0) hr
    simpa [fieldFiniteLinear_apply, Function.comp_def] using
      hF.comp_hasDerivAt (f := fun t : ℝ => (r + t • r, (0 : ℝ))) 0 hp
  exact (hd.congr_of_eventuallyEq he).nonpos_of_antitone hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightHessianSign
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mixed-coordinate and quadratic-form signs of the finite
scalar Ising height Hessian. The mixed and radial derivative estimates imply the Hessian sign. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma fieldHeight_hessian_nonneg_of_coordinate_order (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) (hr : h.height ∈ I)
    (i j : Fin (h.depth + 1)) {J : Set ℝ} (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J)
    (hadm : ∀ t ∈ J, Function.update h.height j (h.height j + t) ∈ fieldStrictHeightCone h.depth)
    (horder : ∀ t (ht : t ∈ J) s (hs : s ∈ J), t ≤ s →
      fieldMagnetizationLevel (fieldStepOfStrictHeights h
        (Function.update h.height j (h.height j + s)) (hadm s hs)) i ≤
      fieldMagnetizationLevel (fieldStepOfStrictHeights h
        (Function.update h.height j (h.height j + t)) (hadm t ht)) i) :
    0 ≤ F.PP i j (h.height, 0) := by
  let q := fun t : ℝ => Function.update h.height j (h.height j + t)
  let K := J ∩ q ⁻¹' I
  have hq : Continuous q := by
    apply continuous_pi
    intro k
    by_cases hkj : k = j
    · subst k
      simp only [q, Function.update_self]
      fun_prop
    · simpa only [q, Function.update_of_ne hkj] using continuous_const
  have hK : IsOpen K := hJ.inter (hI.preimage hq)
  have h0K : (0 : ℝ) ∈ K := by simpa [K, q] using And.intro h0 hr
  have hm : MonotoneOn (fun t => F.P i (q t, 0)) K := by
    intro a ha b hb hab
    have hga := fieldHeight_gradient_identification h F hU (q a) ha.2 (hadm a ha.1) i
    have hgb := fieldHeight_gradient_identification h F hU (q b) hb.2 (hadm b hb.1) i
    have hord := horder a ha.1 b hb.1 hab
    have hw : 0 ≤ h.cut i.succ - h.cut i.castSucc :=
      sub_nonneg.mpr (h.ordered_cut.monotone i.castSucc_le_succ)
    have hm := mul_le_mul_of_nonpos_left hord (show -(h.cut i.succ - h.cut i.castSucc) / 2 ≤ 0 by linarith)
    linarith
  have hd := F.coordinate_gradient_derivative h.height 0 hr i j
  have hn := hm.derivWithin_nonneg (x := 0)
  rw [hd.hasDerivWithinAt.derivWithin (hK.uniqueDiffWithinAt h0K)] at hn
  exact hn

theorem fieldHeight_hessian_mixed_nonneg (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) (hr : h.height ∈ I)
    (hstrict : ∀ k, 0 < (fieldIncrement h k).2)
    (i j : Fin (h.depth + 1)) (hij : i < j) : 0 ≤ F.PP i j (h.height, 0) := by
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij
    apply fieldHeight_hessian_nonneg_of_coordinate_order h hI F hU hr i (Fin.last h.depth)
      isOpen_Ioi (show (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) by
        have hh := hstrict (Fin.last h.depth)
        change -(fieldIncrement h (Fin.last h.depth)).2 < 0
        linarith)
      (fun t ht => fieldHeight_update_final_mem h hstrict t ht)
    intro t ht s hs hts
    exact fieldHeight_final_earlier_antitone h hstrict i hij ht hs hts
  · intro hij
    have hj : 0 < j.val := by change i.val < j.val at hij; omega
    apply fieldHeight_hessian_nonneg_of_coordinate_order h hI F hU hr i j.castSucc
      isOpen_Ioo (show (0 : ℝ) ∈ Ioo (-(fieldIncrement h j.castSucc).2)
        (fieldIncrement h j.succ).2 by
          have ha := hstrict j.castSucc
          have hb := hstrict j.succ
          constructor <;> linarith)
      (fun t ht => fieldHeight_update_interior_mem h hstrict j t ht)
    intro t ht s hs hts
    exact fieldHeight_interior_earlier_antitone h hstrict j hj i hij ht hs hts

theorem fieldHeight_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (x : Fin (h.depth + 1) → ℝ) :
    ∑ i, ∑ j, F.PP i j (r, 0) * x i * x j ≤ 0 := by
  let k := fieldStepOfStrictHeights h r hs
  have hk : ∀ j, 0 < (fieldIncrement k j).2 := fun j => hs j
  have hpos : ∀ i, 0 < r i := by
    intro i
    have h0 : 0 < r 0 := by simpa [fieldHeightIncrement] using hs 0
    exact h0.trans_le ((fieldStrictHeightCone_strictMono hs).monotone (Fin.zero_le i))
  apply F.hessian_nonpos r 0 hr hpos
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact fieldHeight_hessian_mixed_nonneg k hI F hU hr hk i j hlt
    · rw [F.symmetric i j (r, 0) hr]
      exact fieldHeight_hessian_mixed_nonneg k hI F hU hr hk j i hgt
  · exact fun i => fieldHeight_radial_hessian_nonpos h hI F hU r hr hs i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar-field supporting inequality on strict finite
height vectors. The Hessian criterion follows from the mixed and radial derivative signs. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem fieldHeight_support_strict (h : FieldStep) (r s : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (hs : s ∈ fieldStrictHeightCone h.depth) :
    fieldValue (fieldStepOfStrictHeights h s hs) 0 ≤
      fieldValue (fieldStepOfStrictHeights h r hr) 0 +
        ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldStepOfStrictHeights h r hr) i) * (s i - r i) := by
  classical
  obtain ⟨m, V, hm, hrI, hsI⟩ := fieldHeightBox_pair r s hr hs
  let I := fieldHeightBox h.depth m V
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  have hconv : Convex ℝ I := convex_fieldHeightBox _ _ _
  obtain ⟨F, hF⟩ := fieldHeightBox_family h m V hm
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • (s - r) ∈ I := by
    have he : r + t • (s - r) = (1 - t) • r + t • s := by module
    rw [he]
    exact hconv hrI hsI (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∑ i, ∑ j, F.PP i j (r + t • (s - r), 0) * (s i - r i) * (s j - r j) ≤ 0 :=
    fieldHeight_hessian_nonpos h hI F hF _ (hpath t ht)
      (fieldHeightBox_subset_strict hm.le (hpath t ht)) (s - r)
  have hsup := F.support_of_hessian hconv r s 0 hrI hsI hq
  let G : Fin (h.depth + 1) → ℝ := fun i => -(h.cut i.succ - h.cut i.castSucc) / 2 *
    fieldMagnetizationLevel (fieldStepOfStrictHeights h r hr) i
  have hgrad (i : Fin (h.depth + 1)) :
      F.P i (r, 0) = G i + (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0) := by
    have hi := fieldHeight_gradient_identification h F hF r hrI hr i
    dsimp only [G]
    linarith
  have hsum : (∑ i, F.P i (r, 0) * (s i - r i)) =
      (∑ i, G i * (s i - r i)) + (s (Fin.last h.depth) - r (Fin.last h.depth)) / 2 := by
    simp_rw [hgrad, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hrvalue : F.U (r, 0) - r (Fin.last h.depth) / 2 =
      fieldValue (fieldStepOfStrictHeights h r hr) 0 := by
    rw [hF]
    exact fieldHeightJointValue_strict h r hr 0
  have hsvalue : F.U (s, 0) - s (Fin.last h.depth) / 2 =
      fieldValue (fieldStepOfStrictHeights h s hs) 0 := by
    rw [hF]
    exact fieldHeightJointValue_strict h s hs 0
  rw [hsum] at hsup
  change fieldValue (fieldStepOfStrictHeights h s hs) 0 ≤
    fieldValue (fieldStepOfStrictHeights h r hr) 0 + ∑ i, G i * (s i - r i)
  linarith

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

theorem continuous_fieldVaryingOverlaps {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (hc : ∀ av ∈ L, Continuous av.2)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V)
    (root : E → ℝ≥0) (hr : Continuous root) (i : Fin (L.length + 1)) :
    Continuous (fun t => ∫ u, fieldVaryingSquares L t i
      (Real.sqrt (root t : ℝ) * u) ∂gaussianReal 0 1) := by
  have hsq := continuous_fieldVaryingSquares L hL hc hV hv i
  have hshift : Continuous (fun p : E × ℝ => fieldVaryingSquares L p.1 i
      (Real.sqrt (root p.1 : ℝ) * p.2)) :=
    hsq.comp (continuous_fst.prodMk
      (((Real.continuous_sqrt.comp (NNReal.continuous_coe.comp hr)).comp continuous_fst).mul continuous_snd))
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
  · exact Eventually.of_forall (fun s =>
      (hshift.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · exact Eventually.of_forall (fun s => ae_of_all _ (fun u => by
      have h := (fieldVaryingSquares_regular L hL s i).2 (Real.sqrt (root s : ℝ) * u)
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2))
  · exact integrable_const _
  · exact ae_of_all _ (fun u =>
      (hshift.comp (continuous_id.prodMk continuous_const)).continuousAt)

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

lemma fieldVaryingOverlaps_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (root : ℝ≥0) (i : Fin (L.length + 1)) :
    (∫ u, fieldVaryingSquares L t i (Real.sqrt (root : ℝ) * u) ∂gaussianReal 0 1) =
      fieldScalarOverlaps (L.map (fun av => (av.1, av.2 t))) root
        (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) i) := by
  have hm := (fieldVaryingSquares_regular L hL t i).1
  rw [fieldScalarOverlaps, ← fieldVaryingSquares_eq_scalar L t i,
    integral_gaussianReal_zero_eq_standard root hm]

lemma continuous_fieldRegularizedRoot (h : FieldStep) : Continuous (fieldRegularizedRoot h) :=
  (continuous_const.add continuous_fieldHeightEpsilon).subtype_mk _

lemma continuous_fieldRegularizedValue (h : FieldStep) :
    Continuous (fun t => fieldValue (fieldRegularized h t) 0) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  have hval := continuous_fieldVaryingValue L hL hc hV hv
  obtain ⟨hcap, hb⟩ := fieldVaryingValue_bound L hL hV hv
  have hroot : Continuous (fun t : ℝ => (fieldRegularizedRoot h t : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_fieldRegularizedRoot h)
  have hi := continuous_field_gaussian_integral hval hroot
    (show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const)
    hcap zero_le_one (fun t y => by simpa only [one_mul] using hb t y)
  have hlast : Continuous (fun t => (fieldRegularized h t).height (Fin.last h.depth) / 2) := by
    change Continuous (fun t => (h.height (Fin.last h.depth) +
      fieldHeightEpsilon t * ((Fin.last h.depth).val + 1 : ℕ)) / 2)
    have heps := continuous_fieldHeightEpsilon
    fun_prop
  convert hi.sub hlast using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [fieldValue_scalar_chain, ← fieldRegularizedIncrements_eval,
    ← fieldVaryingValue_eq_scalar]
  simp only [gaussianOperator, ite_true, if_true, zero_add, fieldRegularized, fieldWithHeights,
    fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one,
    fieldRegularizedRoot, NNReal.coe_mk, Pi.sub_apply, L]
  rfl

lemma continuous_fieldRegularizedMagnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    Continuous (fun t => fieldMagnetizationLevel (fieldRegularized h t) i) := by
  let L := fieldRegularizedIncrements h
  let V := h.height (Fin.last h.depth) + 1
  have hV : 0 ≤ V := add_nonneg (h.nonneg _) zero_le_one
  have hL := fieldRegularizedIncrements_positive h
  have hc := fieldRegularizedIncrements_continuous h
  have hv := fieldRegularizedIncrements_bound h
  let j : Fin (L.length + 1) := ⟨i.val, by
    simpa only [L, fieldRegularizedIncrements, List.length_ofFn] using i.isLt⟩
  have hcont := continuous_fieldVaryingOverlaps L hL hc hV hv
    (fieldRegularizedRoot h) (continuous_fieldRegularizedRoot h) j
  convert hcont using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [fieldVaryingOverlaps_eq_scalar L hL]
  unfold fieldMagnetizationLevel
  have hroot : (NNReal.mk ((fieldRegularized h t).height 0)
      ((fieldRegularized h t).nonneg 0)) = fieldRegularizedRoot h t := by
    apply Subtype.ext
    simp only [fieldRegularizedRoot, fieldRegularized, fieldWithHeights,
      fieldRegularizedHeight, Fin.val_zero, zero_add, Nat.cast_one, mul_one]
    rfl
  rw [hroot]
  unfold fieldScalarOverlaps
  apply integral_congr_ae
  apply ae_of_all
  intro z
  exact congrFun (fieldScalarSquares_congr_list
    (fieldRegularizedIncrements_eval h t).symm (fun y => Real.log (Real.cosh y))
    Real.tanh _ _ rfl) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightClosedSupport
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite scalar-field supporting inequality on the closed
nonnegative height cone. The proof removes the strict approximation by
continuity of both the value and its physical magnetization coefficients. -/

noncomputable section
open IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem fieldHeight_support (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldValue (fieldWithHeights h r hr0 hrmono) 0 ≤ fieldValue h 0 +
      ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) *
        (r i - h.height i) := by
  let k := fieldWithHeights h r hr0 hrmono
  have hleft := continuous_fieldRegularizedValue k
  have hright : Continuous (fun t => fieldValue (fieldRegularized h t) 0 +
      ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
        fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i)) := by
    have hval := continuous_fieldRegularizedValue h
    have hB := continuous_fieldRegularizedMagnetization h
    fun_prop
  have hineq : ∀ t ∈ Ioc (0 : ℝ) 1,
      fieldValue (fieldRegularized k t) 0 ≤ fieldValue (fieldRegularized h t) 0 +
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i) := by
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
    have hi := fieldHeight_support_strict h _ _ hh hk
    have hevh := congrArg (fun q : FieldStep => fieldValue q 0) heh
    have hevk := congrArg (fun q : FieldStep => fieldValue q 0) hek
    rw [hevh, hevk] at hi
    have hd (i : Fin (h.depth + 1)) : (fieldRegularized k t).height i -
        (fieldRegularized h t).height i = r i - h.height i := by
      change (r i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) -
        (h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) = _
      ring
    have heBsum :
        (∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldStepOfStrictHeights h (fieldRegularized h t).height hh) i) *
            ((fieldRegularized k t).height i - (fieldRegularized h t).height i)) =
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) *
            (r i - h.height i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldMagnetizationLevel_congr heh i i rfl, hd]
    exact hi.trans_eq (congrArg (fun a : ℝ => fieldValue (fieldRegularized h t) 0 + a) heBsum)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      fieldValue (fieldRegularized k t) 0 ≤ fieldValue (fieldRegularized h t) 0 +
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hineq t ⟨ht, ht1.le⟩
  have hh := le_of_tendsto_of_tendsto
    (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent
  have hz (i : Fin (h.depth + 1)) :=
    fieldMagnetizationLevel_congr (fieldRegularized_zero h) i i rfl
  simp_rw [hz] at hh
  simpa only [fieldRegularized_zero, k] using hh

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

lemma fieldMagnetizationPath_step_ae (h : FieldStep) :
    (fieldMagnetizationPath h).val =ᵐ[pathMeasure]
      finiteStepFunction h.cut (fieldMagnetizationLevel h) := by
  filter_upwards [ae_finite_overlap_cell h.cut h.first h.last] with s hs
  obtain ⟨i, hi⟩ := hs
  rw [fieldMagnetizationPath_on_cell h i hi,
    finiteStepFunction_on_cell h.ordered_cut _ hi]

lemma fieldPairing_magnetization_same (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldPairing (fieldMagnetizationPath h) (fieldWithHeights h r hr0 hrmono) =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * r i := by
  change (∫ s, fieldMagnetizationPath h s * fieldFunction (fieldWithHeights h r hr0 hrmono) s
    ∂pathMeasure) = _
  calc
    _ = ∫ s, finiteStepFunction h.cut (fieldMagnetizationLevel h) s *
        finiteStepFunction h.cut r s ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [fieldMagnetizationPath_step_ae h] with s hs
      rw [hs]
      rfl
    _ = _ := integral_finiteStepFunction_mul h.cut h.ordered_cut h.first h.last _ _

lemma fieldPairing_magnetization_self (h : FieldStep) :
    fieldPairing (fieldMagnetizationPath h) h =
      ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * h.height i := by
  have he : fieldWithHeights h h.height h.nonneg h.ordered_height = h := by
    cases h
    rfl
  simpa only [he] using fieldPairing_magnetization_same h h.height h.nonneg h.ordered_height

lemma field_support_same_partition (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldValue (fieldWithHeights h r hr0 hrmono) 0 ≤ fieldValue h 0 -
      (1 / 2 : ℝ) * ∫ s, fieldMagnetizationPath h s *
        (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure := by
  have hi := fieldHeight_support h r hr0 hrmono
  have he : (∫ s, fieldMagnetizationPath h s *
      (fieldFunction (fieldWithHeights h r hr0 hrmono) s - fieldFunction h s) ∂pathMeasure) =
      fieldPairing (fieldMagnetizationPath h) (fieldWithHeights h r hr0 hrmono) -
        fieldPairing (fieldMagnetizationPath h) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he, fieldPairing_magnetization_same, fieldPairing_magnetization_self]
  have hs : (∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) *
      (r i - h.height i)) = -(1 / 2 : ℝ) *
        ((∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * r i) -
          ∑ i, (h.cut i.succ - h.cut i.castSucc) * fieldMagnetizationLevel h i * h.height i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hi
  linarith

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

lemma field_support_equal_cutList_oai {h k : FieldStep}
    (he : List.ofFn h.cut = List.ofFn k.cut) :
    fieldValue k 0 ≤ fieldValue h 0 - (1 / 2 : ℝ) *
      ∫ s, fieldMagnetizationPath h s * (fieldFunction k s - fieldFunction h s) ∂pathMeasure := by
  obtain ⟨r, hr0, hrmono, rfl⟩ := field_eq_withHeights_of_cutList he
  exact field_support_same_partition h r hr0 hrmono

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.field_support_equal_cutList_oai := @OAI.InvariantIsing.field_support_equal_cutList_oai
