-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_original_scalar_self_consistency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:40.487587+00:00
-- url     : https://prove2.me/submissions/92a1bf31-2ed8-4821-a5f3-ce2f57372479

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_cavity_original_overlap_limit
import Theorems.Thm_OAI_InvariantIsing_cavity_original_spin_limit

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Measure.isProbabilityMeasure_of_map`, which takes the map's measurability; ours takes
the function `f`, and `_` there leaves the instance argument stuck (HardSphere, oaiq-054). -/
theorem isProbabilityMeasure_of_map_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {f : α → β} [MeasureTheory.IsProbabilityMeasure (μ.map f)]
    (_hf : AEMeasurable f μ) : MeasureTheory.IsProbabilityMeasure μ :=
  MeasureTheory.Measure.isProbabilityMeasure_of_map f
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_GaussianIntegration
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hm' : Measurable f')
    {K K' : ℝ} (hb : ∀ x, |f x| ≤ K) (hb' : ∀ x, |f' x| ≤ K') :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hm : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)).measurable
  have hif : Integrable f (gaussianReal 0 1) :=
    (MemLp.of_bound hm.aestronglyMeasurable K
      (ae_of_all _ (fun x => by simpa using hb x)) (p := 1)).integrable le_rfl
  have hif' : Integrable f' (gaussianReal 0 1) :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun x => by simpa using hb' x)) (p := 1)).integrable le_rfl
  apply gaussian_integration_by_parts hd hif hif'
  exact ((memLp_id_gaussianReal 1).integrable le_rfl).mul_bdd
    hm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hb x))

lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {F F' : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F) (hm' : Measurable F')
    (hd : ∀ (g : Fin n → ℝ) (x : ℝ),
      HasDerivAt (fun y => F (i.insertNth y g)) (F' (i.insertNth x g)) x)
    {K K' : ℝ} (hb : ∀ g, |F g| ≤ K) (hb' : ∀ g, |F' g| ≤ K') :
    (∫ g, g i * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, F' g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm ((gaussianReal 0 1).prod ν) μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hF' : Integrable F' μ :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun g => by simpa using hb' g)) (p := 1)).integrable le_rfl
  have hFi : Integrable (fun g => g i * F g) μ := by
    have hc : Integrable (fun g : Fin (n + 1) → ℝ => g i) μ :=
      (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)
    exact hc.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa using hb g))
  change (∫ g, g i * F g ∂μ) = ∫ g, F' g ∂μ
  rw [← he.integral_comp' (fun g => g i * F g), ← he.integral_comp' F']
  have hi1 : Integrable (fun v => e.symm v i * F (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hFi
  have hi2 : Integrable (fun v => F' (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hF'
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  apply gaussian_integration_by_parts_bounded (hd g)
  · exact hm'.comp (measurable_pi_iff.mpr (i.forall_iff_succAbove.mpr
      ⟨by simp only [Fin.insertNth_apply_same]; exact measurable_id,
        fun j => by simp⟩))
  · exact fun x => hb _
  · exact fun x => hb' _

section FiniteGibbs
variable {S : Type*} [Fintype S]

lemma finiteGibbs_nonneg {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    0 ≤ finiteGibbs w H x :=
  div_nonneg (mul_nonneg (hw.1 x) (Real.exp_pos _).le) (finitePartition_pos hw H).le

lemma finiteGibbs_sum {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    ∑ x, finiteGibbs w H x = 1 := by
  simp only [finiteGibbs, ← Finset.sum_div]
  exact div_self (finitePartition_pos hw H).ne'

lemma finiteGibbs_le_one {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    finiteGibbs w H x ≤ 1 := by
  rw [← finiteGibbs_sum hw H]
  exact Finset.single_le_sum (fun y _ => finiteGibbs_nonneg hw H y) (Finset.mem_univ x)

lemma finiteGibbs_average_bound {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ x, |A x| ≤ K) :
    |∑ x, finiteGibbs w H x * A x| ≤ K := by
  calc
    _ ≤ ∑ x, |finiteGibbs w H x * A x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, finiteGibbs w H x * |A x| := by
      congr 1; ext x; rw [abs_mul, abs_of_nonneg (finiteGibbs_nonneg hw H x)]
    _ ≤ ∑ x, finiteGibbs w H x * K := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hA x) (finiteGibbs_nonneg hw H x))
    _ = K := by rw [← Finset.sum_mul, finiteGibbs_sum hw H, one_mul]

lemma hasDerivAt_finitePartition {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (w : S → ℝ) :
    HasDerivAt (fun s => finitePartition w (H s))
      (∑ x, w x * Real.exp (H t x) * dH x) t := by
  simpa only [finitePartition, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hH x).exp.const_mul (w x)))

lemma hasDerivAt_finiteGibbs {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (x : S) :
    HasDerivAt (fun s => finiteGibbs w (H s) x)
      (finiteGibbs w (H t) x *
        (dH x - ∑ y, finiteGibbs w (H t) y * dH y)) t := by
  have hd := ((hH x).exp.const_mul (w x)).div
    (hasDerivAt_finitePartition hH w) (finitePartition_pos hw (H t)).ne'
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [finiteGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(finitePartition_pos hw (H t)).ne']

lemma hasDerivAt_log_finitePartition {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) :
    HasDerivAt (fun s => Real.log (finitePartition w (H s)))
      (∑ x, finiteGibbs w (H t) x * dH x) t := by
  convert (hasDerivAt_finitePartition hH w).log (finitePartition_pos hw (H t)).ne' using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteGibbs, div_mul_eq_mul_div, Finset.sum_div]

end FiniteGibbs

section GaussianGibbs
variable {S : Type*} [Fintype S]

lemma continuous_gaussianGibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (x : S) :
    Continuous (fun g => gaussianGibbs w B C g x) := by
  unfold gaussianGibbs finiteGibbs
  apply Continuous.div
  · unfold linearGaussian; fun_prop
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

omit [Fintype S] in
lemma hasDerivAt_linearGaussian_insert {n : ℕ} (C : S → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => linearGaussian C (i.insertNth y g) x) (C x i) t := by
  have he : (fun y => linearGaussian C (i.insertNth y g) x) =
      fun y => C x i * y + ∑ j : Fin n, C x (i.succAbove j) * g j := by
    funext y
    simp only [linearGaussian, i.sum_univ_succAbove, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  rw [he]
  simpa using ((hasDerivAt_id t).const_mul (C x i)).add_const
    (∑ j : Fin n, C x (i.succAbove j) * g j)

lemma hasDerivAt_gaussianGibbs_insert {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => gaussianGibbs w B C (i.insertNth y g) x)
      (gaussianGibbs w B C (i.insertNth t g) x *
        (C x i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i)) t := by
  apply hasDerivAt_finiteGibbs hw
  intro z
  exact (hasDerivAt_linearGaussian_insert C i g z t).const_add (B z)

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

lemma replicaGibbs_nonneg {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    0 ≤ replicaGibbs w B C g σ :=
  Finset.prod_nonneg (fun l _ => finiteGibbs_nonneg hw _ (σ l))

lemma replicaGibbs_le_one {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    replicaGibbs w B C g σ ≤ 1 := by
  exact Finset.prod_le_one (fun replica _ => finiteGibbs_nonneg hw _ (σ replica))
    (fun l _ => finiteGibbs_le_one hw _ (σ l))

lemma continuous_replicaGibbs {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (σ : Fin r → S) :
    Continuous (fun g => replicaGibbs w B C g σ) := by
  exact continuous_finsetProd _ (fun l _ => continuous_gaussianGibbs hw B C (σ l))

lemma hasDerivAt_replicaGibbs_insert {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (σ : Fin r → S) (t : ℝ) :
    HasDerivAt (fun y => replicaGibbs w B C (i.insertNth y g) σ)
      (replicaGibbs w B C (i.insertNth t g) σ *
        (∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i))) t := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun l _ => hasDerivAt_gaussianGibbs_insert hw B C i g (σ l) t)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← mul_assoc, Finset.prod_erase_mul _ _ hl]
  rfl

lemma integrable_gaussian_coordinate_mul {n : ℕ} (i : Fin n)
    {F : (Fin n → ℝ) → ℝ} (hm : Measurable F) {K : ℝ} (hK : ∀ g, |F g| ≤ K) :
    Integrable (fun g => g i * F g) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hc : Integrable (fun g : Fin n → ℝ => g i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal 1).integrable le_rfl)
  exact hc.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun g => by simpa using hK g))

omit [Fintype S] in
lemma gaussian_pi_linear_insertion {n : ℕ} (a : Fin (n + 1) → ℝ)
    {F : (Fin (n + 1) → ℝ) → ℝ} {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
    (hm : Measurable F) (hm' : ∀ i, Measurable (F' i))
    (hd : ∀ i g x, HasDerivAt (fun y => F (i.insertNth y g)) (F' i (i.insertNth x g)) x)
    {K : ℝ} {K' : Fin (n + 1) → ℝ}
    (hb : ∀ g, |F g| ≤ K) (hb' : ∀ i g, |F' i g| ≤ K' i) :
    (∫ g, (∑ i, a i * g i) * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, ∑ i, a i * F' i g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hi i : Integrable (F' i) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (MemLp.of_bound (hm' i).aestronglyMeasurable (K' i)
      (ae_of_all _ (fun g => by simpa using hb' i g)) (p := 1)).integrable le_rfl
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (integrable_gaussian_coordinate_mul i hm hb).const_mul _),
    integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul,
    gaussian_pi_integration_by_parts i hm (hm' i) (hd i) hb (hb' i)]

lemma gaussian_replica_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) (σ : Fin r → S) :
    (∫ g, linearGaussian A g x * replicaGibbs w B C g σ
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, replicaGibbs w B C g σ *
      (∑ l, (gaussianCross A C x (σ l) -
        ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hd := gaussian_pi_linear_insertion (A x) (continuous_replicaGibbs hw B C σ).measurable
    (F' := fun i g => replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i))
    (fun i => ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).measurable)
    (fun i g t => hasDerivAt_replicaGibbs_insert hw B C i g σ t)
    (K := 1) (K' := fun i => ∑ l, (|C (σ l) i| + ∑ z, |C z i|))
    (fun g => by rw [abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)];
                 exact replicaGibbs_le_one hw B C g σ)
  have hb i g : |replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i)| ≤
      ∑ l, (|C (σ l) i| + ∑ z, |C z i|) := by
    rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    apply (mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)).trans
    rw [one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro l _
    exact (abs_sub _ _).trans (add_le_add le_rfl
      (finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
        (fun z => C z i) (fun z => Finset.single_le_sum (fun y _ => abs_nonneg (C y i))
          (Finset.mem_univ z))))
  rw [show linearGaussian A = fun g x => ∑ i, A x i * g i from rfl, hd hb]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [gaussianCross, Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    ring

end Replicas

section Perturbation
variable {S : Type*} [Fintype S]

lemma log_finitePartition_le_add {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, H x ≤ J x + K) :
    Real.log (finitePartition w H) ≤ Real.log (finitePartition w J) + K := by
  rw [← Real.log_exp K, ← Real.log_mul (finitePartition_pos hw J).ne' (Real.exp_pos K).ne']
  apply Real.log_le_log (finitePartition_pos hw H)
  unfold finitePartition
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h x)) (hw.1 x)

lemma log_finitePartition_lipschitz {w : S → ℝ} (hw : GibbsReference w)
    {H J : S → ℝ} {K : ℝ} (h : ∀ x, |H x - J x| ≤ K) :
    |Real.log (finitePartition w H) - Real.log (finitePartition w J)| ≤ K := by
  apply abs_le.mpr
  constructor
  · have hh := log_finitePartition_le_add hw (H := J) (J := H) (K := K)
      (fun x => by have := (abs_le.mp (h x)).1; linarith)
    linarith
  · have hh := log_finitePartition_le_add hw (H := H) (J := J) (K := K)
      (fun x => by have := (abs_le.mp (h x)).2; linarith)
    linarith

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

lemma continuous_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Continuous (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x))) := by
  apply Continuous.log
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

lemma integrable_log_finitePartition {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A : S → Fin n → ℝ) (t : ℝ) :
    Integrable (fun g => Real.log (finitePartition w (fun x => B x + t * linearGaussian A g x)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi : Integrable (fun g => |Real.log (finitePartition w B)| +
      |t| * ∑ x, |linearGaussian A g x|)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (integrable_const _).add ((integrable_finsetSum _
      (fun x _ => (integrable_linearGaussian A x).abs)).const_mul _)
  apply hi.mono' (continuous_log_finitePartition hw B A t).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  have hh := log_finitePartition_lipschitz hw (H := fun x => B x + t * linearGaussian A g x)
    (J := B) (K := |t| * ∑ x, |linearGaussian A g x|) (fun x => by
      simp only [add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
        (abs_nonneg t))
  have := abs_le.mp hh
  have hz := abs_le.mp (le_refl |Real.log (finitePartition w B)|)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma gaussian_gibbs_insertion {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) :
    (∫ g, linearGaussian A g x * gaussianGibbs w B C g x
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, gaussianGibbs w B C g x *
      (gaussianCross A C x x - ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  simpa [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
    gaussian_replica_insertion (r := 1) hw B A C x (fun _ => x)

lemma integrable_linearGaussian_mul_gibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x y : S) :
    Integrable (fun g => linearGaussian A g x * gaussianGibbs w B C g y)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_gaussianGibbs hw B C y).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianGibbs w B C g y from finiteGibbs_nonneg hw _ y)]
  exact finiteGibbs_le_one hw _ y

end Perturbation

variable {S : Type*} [Fintype S]

lemma integrable_replica_covariance {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  let K := ∑ z, |gaussianCross A C x z|
  apply Integrable.of_bound
    ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).aestronglyMeasurable
    (∑ l, (|gaussianCross A C x (σ l)|+K))
  apply ae_of_all
  intro g
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  calc
    _ ≤ 1*|∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)| :=
      mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact (abs_sub _ _).trans (add_le_add le_rfl
        (finiteGibbs_average_bound hw _ _ (fun z =>
          show |gaussianCross A C x z| ≤ ∑ y, |gaussianCross A C x y| from
            Finset.single_le_sum (fun y _ => abs_nonneg (gaussianCross A C x y)) (Finset.mem_univ z))))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma referenceReplicaMean_eq_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D =
      (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
      (∫ σ, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν)) := by
  rw [reference_replica_partition]; rfl

lemma finite_reference_weights_sum {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∑ x, ν.real {x} = 1 := by
  have h := integral_fintype (μ := ν) (f := fun _ => (1:ℝ)) Integrable.of_finite
  simpa only [smul_eq_mul,mul_one,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using h.symm

lemma finite_reference_weight_pos {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∃ x, 0 < ν.real {x} := by
  have hsum := finite_reference_weights_sum ν
  have h := Finset.sum_pos_iff_of_nonneg (fun (x:S) (_:x ∈ Finset.univ) => (measureReal_nonneg : 0 ≤ ν.real {x}))
  obtain ⟨x, _,hx⟩ := h.mp (show 0 < ∑ x, ν.real {x} by rw [hsum]; norm_num)
  exact ⟨x,hx⟩

lemma referencePartition_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) :
    referencePartition μ (H ∘ f) = referencePartition ν H := by
  exact hf.hasLaw.integral_comp hmH.exp.aestronglyMeasurable

lemma referenceReplicaMean_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ}
    (hmD : Measurable D) :
    referenceReplicaMean μ (H ∘ f) (fun σ => D (fun i => f (σ i))) =
      referenceReplicaMean ν H D := by
  have hpi : MeasurePreserving (fun σ : Fin r → S => fun i => f (σ i))
      (Measure.pi (fun _ : Fin r => μ)) (Measure.pi (fun _ : Fin r => ν)) := by
    refine ⟨Measurable.of_eval (fun index => hf.measurable.comp (measurable_pi_apply index)),?_⟩
    have hmap : IsProbabilityMeasure (μ.map f) := hf.map_eq.symm ▸ inferInstance
    simpa only [hf.map_eq] using Measure.pi_map_pi (μ := fun _ : Fin r => μ) (f := fun _ : Fin r => f) (fun _ : Fin r => hf.measurable.aemeasurable)
  unfold referenceReplicaMean
  rw [referencePartition_map hf hmH]
  congr 1
  exact hpi.hasLaw.integral_comp ((by fun_prop : Measurable
    (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*D σ)).aestronglyMeasurable)

lemma finite_reference_GibbsReference {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    GibbsReference (fun x => ν.real {x}) :=
  ⟨fun _ => measureReal_nonneg,finite_reference_weight_pos ν⟩

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

lemma gaussian_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin n => g i)
      gaussianCoordinates (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have he := hs.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

lemma cylinderField_eq_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) (g : ℕ → ℝ) :
    cylinderField a g = ∑ i : Fin n, a i*g i := by
  classical
  rw [cylinderField, a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*g i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

lemma finite_family_support_bound {X : Type*} [Fintype X] (a : X → ℕ →₀ ℝ) :
    ∃ n : ℕ, ∀ x i, a x i ≠ 0 → i < n+1 := by
  classical
  let s := Finset.univ.biUnion (fun x => (a x).support)
  refine ⟨s.sup id,fun x i hi => ?_⟩
  have hm : i ∈ s := Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hi⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)

lemma cylinderField_law (a : ℕ →₀ ℝ) :
    gaussianCoordinates.map (cylinderField a) =
      gaussianReal 0 ((a.sum (fun _ c => c^2)).toNNReal) := by
  classical
  let n := a.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he : cylinderField a = (fun g : Fin n → ℝ => ∑ i : Fin n, a i*g i) ∘
      (fun g : ℕ → ℝ => fun i : Fin n => g i) := by
    funext g
    exact cylinderField_eq_prefix a ha g
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    (gaussian_prefix_measurePreserving n).map_eq,(gaussian_weighted_sum_law (fun i : Fin n => a i)).map_eq]
  congr 2
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => a i^2) n

lemma cylinder_variance_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    a.sum (fun _ c => c^2) = ∑ i : Fin n, (a i)^2 := by
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (a i)^2) n).symm

lemma cylinder_variance_sum_le {ι : Type*} [Fintype ι] (a : ι → ℕ →₀ ℝ)
    {K : ℝ} (ha : ∀ i, (a i).sum (fun _ c => c^2) ≤ K) :
    (∑ i, a i).sum (fun _ c => c^2) ≤ (Fintype.card ι : ℝ)^2*K := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound a
  have hs : ∀ j ∈ (∑ i, a i).support, j < n+1 := by
    intro j hj
    by_contra hjn
    have hz i : a i j = 0 := by
      by_contra h
      exact hjn (hn i j h)
    have hz' : (∑ i, a i) j = 0 := by simp only [Finsupp.finsetSum_apply,hz,Finset.sum_const_zero]
    exact Finsupp.mem_support_iff.mp hj hz'
  rw [cylinder_variance_prefix _ hs]
  simp only [Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ j : Fin (n+1), (Fintype.card ι : ℝ)*(∑ i, (a i j)^2) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun _ => (1:ℝ)) (fun i => a i j)
    _ = (Fintype.card ι : ℝ)*∑ i, ∑ j : Fin (n+1), (a i j)^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card ι : ℝ)*∑ _i : ι, K := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      rw [← cylinder_variance_prefix (a i) (fun j hj => hn i j (Finsupp.mem_support_iff.mp hj))]
      exact ha i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] <;> ring

lemma cylinderCross_prefix (a b : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    cylinderCross a b = ∑ i : Fin n, a i*b i := by
  rw [cylinderCross,a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*b i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => a i*b i) n).symm

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

lemma partition_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp ((p:ℝ)*H x)) ν) :
    (∫ x, Real.exp (H x) ∂ν)^p ≤ ∫ x, Real.exp ((p:ℝ)*H x) ∂ν := by
  simpa only [Function.comp_def, Real.exp_nat_mul] using
    (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (H x)).le)) h1
      (by simpa only [Function.comp_def, Real.exp_nat_mul] using hp)

lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp

 

lemma gaussian_field_exp_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (t : ℝ) :
    Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) ∧
      (∫ ω, ∫ x, Real.exp (t*H (ω,x)) ∂ν ∂μ) ≤ Real.exp (t^2*K/2) := by
  have he : Measurable (fun z => Real.exp (t*H z)) := hm.const_mul t |>.exp
  have hsec : ∀ x, Integrable (fun ω => Real.exp (t*H (ω,x))) μ := by
    intro x
    have hx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
    apply (integrable_map_measure (g := fun y : ℝ => Real.exp (t*y)) (μ := μ) (by fun_prop) hx.aemeasurable).mp
    rw [hg x]
    exact integrable_exp_mul_gaussianReal t
  have hb (x : X) : (∫ ω, Real.exp (t*H (ω,x)) ∂μ) ≤ Real.exp (t^2*K/2) := by
    have h := mgf_gaussianReal (X := fun ω => H (ω, x))
      (hg x) t
    simp only [mgf, zero_mul, zero_add] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hv x) (sq_nonneg t)]
  have hi : Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) := by
    apply (integrable_prod_iff' he.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    apply Integrable.of_bound he.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      (Real.exp (t^2*K/2))
    refine Filter.Eventually.of_forall fun x => ?_
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (integral_nonneg (μ := μ) (f := fun ω : Ω => Real.exp (t*H (ω,x))) (fun ω => (Real.exp_pos _).le))] using hb x
  refine ⟨hi, ?_⟩
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _ : X, Real.exp (t^2*K/2) ∂ν :=
      integral_mono hi.integral_prod_right (integrable_const _) hb
    _ = _ := by simp

lemma abs_le_exp_add_exp_neg (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.add_one_le_exp (-x), Real.exp_pos x]

lemma gaussian_field_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) : Integrable H (μ.prod ν) := by
  have hp := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  have hn := (gaussian_field_exp_integrable (ν := ν) hm hg hv (-1:ℝ)).1
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, one_mul, neg_one_mul] using abs_le_exp_add_exp_neg (H z)

 

lemma gaussian_partition_moments {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (p : ℕ) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧
      (∫ ω, Z ω^p ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) ∧
      (∫ ω, (Z ω^p)⁻¹ ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  change Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧ _
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have h1 := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  simp only [one_mul] at h1
  obtain ⟨hip, hbp⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (p:ℝ)
  obtain ⟨hin, hbn⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (-(p:ℝ))
  have hp : ∀ᵐ ω ∂μ, Z ω^p ≤ ∫ x, Real.exp ((p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [h1.prod_right_ae, hip.prod_right_ae] with ω hω hωp
    exact partition_pow_le p hω hωp
  have hn : ∀ᵐ ω ∂μ, (Z ω^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [hH.prod_right_ae, h1.prod_right_ae, hin.prod_right_ae] with ω hω hω1 hωn
    exact partition_inv_pow_le p hω hω1 hωn
  have hz (ω) : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hpint : Integrable (fun ω => Z ω^p) μ := by
    apply hip.integral_prod_left.mono' (hmZ.pow_const p).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hz _) _)] using hp
  have hnint : Integrable (fun ω => (Z ω^p)⁻¹) μ := by
    apply hin.integral_prod_left.mono' ((hmZ.pow_const p).inv).aestronglyMeasurable
    simpa only [Pi.inv_apply, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hz _) _))] using hn
  refine ⟨hpint, hnint, (integral_mono_ae hpint hip.integral_prod_left hp).trans hbp, ?_⟩
  simpa only [neg_sq] using (integral_mono_ae hnint hin.integral_prod_left hn).trans hbn

lemma log_square_le_partition_moments {x : ℝ} (hx : 0 < x) :
    (Real.log x)^2 ≤ 2*(x^2+(x^2)⁻¹) := by
  have hp := Real.log_le_sub_one_of_pos hx
  have hn := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hn
  have hB : |Real.log x| ≤ x+x⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [inv_pos.mpr hx]
  have hs := pow_le_pow_left₀ (abs_nonneg (Real.log x)) hB 2
  rw [sq_abs] at hs
  rw [← inv_pow]
  nlinarith [sq_nonneg (x-x⁻¹)]

 

lemma gaussian_log_partition_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => (Real.log (Z ω))^2) μ ∧
    (∫ ω, (Real.log (Z ω))^2 ∂μ) ≤ 4*Real.exp (2*K) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hip,hin,hbp,hbn⟩ := gaussian_partition_moments (ν := ν) hm hg hv 2
  change Integrable (fun ω => Z ω^2) μ at hip
  change Integrable (fun ω => (Z ω^2)⁻¹) μ at hin
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have he := (gaussian_field_exp_integrable (ν := ν) hm hg hv 1).1
  simp only [one_mul] at he
  have hb : ∀ᵐ ω ∂μ, (Real.log (Z ω))^2 ≤ 2*(Z ω^2+(Z ω^2)⁻¹) := by
    filter_upwards [hH.prod_right_ae, he.prod_right_ae] with ω hω hωe
    apply log_square_le_partition_moments
    exact (Real.exp_pos _).trans_le (exp_integral_le_partition hω hωe)
  have hi : Integrable (fun ω => (Real.log (Z ω))^2) μ := by
    apply ((hip.add hin).const_mul 2).mono' (hmZ.log.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (Z ω)))] using hω
  refine ⟨hi, (integral_mono_ae hi ((hip.add hin).const_mul 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hip hin]
  have hx : (2:ℝ)^2*K/2 = 2*K := by ring
  simp only [Nat.cast_ofNat] at hbp hbn
  rw [hx] at hbp hbn
  linarith

 

lemma uniformIntegrable_of_second_moment_bound {I Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : I → Ω → ℝ} {C : ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (fun ω => (f i ω)^2) μ)
    (hb : ∀ i, (∫ ω, (f i ω)^2 ∂μ) ≤ C) : UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of le_rfl ENNReal.one_ne_top (fun i => (hm i).aestronglyMeasurable)
  intro ε hε
  have hεreal := hε
  let A := (|C|+1)/ε
  have hA : 0 < A := div_pos (by positivity) hεreal
  refine ⟨⟨A,hA.le⟩, fun i => ?_⟩
  let S := {ω : Ω | (⟨A,hA.le⟩ : NNReal) ≤ ‖f i ω‖₊}
  have hs : MeasurableSet S := by
    change MeasurableSet {ω : Ω | A ≤ ‖f i ω‖}
    exact measurableSet_le measurable_const (hm i).norm
  have hfi : Integrable (f i) μ :=
    ((memLp_two_iff_integrable_sq (hm i).aestronglyMeasurable).mpr (hi i)).integrable (by norm_num)
  have hint := hfi.indicator hs
  have hle : ∀ ω, ‖S.indicator (f i) ω‖ ≤ (f i ω)^2/A := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
      have ha : A ≤ |f i ω| := by exact_mod_cast hω
      apply (le_div_iff₀ hA).mpr
      nlinarith [sq_abs (f i ω), mul_le_mul_of_nonneg_left ha (abs_nonneg (f i ω))]
    · rw [Set.indicator_of_notMem hω, norm_zero]
      positivity
  change eLpNorm (S.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hint]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, (f i ω)^2/A ∂μ := integral_mono hint.norm ((hi i).div_const A) hle
    _ = (∫ ω, (f i ω)^2 ∂μ)/A := integral_div _ _
    _ ≤ C/A := div_le_div_of_nonneg_right (hb i) hA.le
    _ ≤ ε := by
      apply (div_le_iff₀ hA).mpr
      dsimp [A]
      rw [mul_div_cancel₀ _ hεreal.ne']
      linarith [le_abs_self C]

 

lemma integral_tendsto_of_second_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (fun ω => (f i ω)^2) μ)
    (hb : ∀ i, (∫ ω, (f i ω)^2 ∂μ) ≤ C)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) atTop (𝓝 (g ω))) :
    Integrable g μ ∧ Tendsto (fun i => ∫ ω, f i ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  have hu := uniformIntegrable_of_second_moment_bound hm hi hb
  have hg := hu.integrable_of_ae_tendsto ht
  refine ⟨hg, ?_⟩
  apply tendsto_integral_of_L1 g hg.aestronglyMeasurable
    (Eventually.of_forall (fun i => (hu.memLp i).integrable le_rfl))
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1:ENNReal) ≤ 1)
      ENNReal.one_ne_top (fun i => (hm i).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg) hu.unifIntegrable ht



lemma normalizedRestriction_probability {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {A : Set X} (hA : ν A ≠ 0) :
    IsProbabilityMeasure (normalizedRestriction ν A) := by
  constructor
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top _ _)

lemma integral_normalizedRestriction {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] (A : Set X) (f : X → ℝ) :
    (∫ x, f x ∂normalizedRestriction ν A) = (∫ x in A, f x ∂ν)/(ν A).toReal := by
  rw [normalizedRestriction, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma integral_restriction_tendsto {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) {f : X → ℝ} (hi : Integrable f ν) :
    Tendsto (fun n => ∫ x in A n, f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  simp_rw [← integral_indicator (hm _)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · exact fun n => hi.aestronglyMeasurable.indicator (hm n)
  · exact hi.norm
  · exact fun n => Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)
  · refine Eventually.of_forall fun x => ?_
    exact tendsto_const_nhds.congr' ((hA x).mono (fun n hn => (indicator_of_mem hn f).symm))

lemma normalized_restriction_integral_tendsto {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) {f : X → ℝ} (hi : Integrable f ν) :
    Tendsto (fun n => ∫ x, f x ∂normalizedRestriction ν (A n))
      atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hmass : Tendsto (fun n => (ν (A n)).toReal) atTop (𝓝 (1:ℝ)) := by
    simpa only [integral_const, Measure.restrict_apply_univ, measureReal_def,
      smul_eq_mul, mul_one, measure_univ, ENNReal.toReal_one] using
      integral_restriction_tendsto hm hA (integrable_const (1:ℝ) (μ := ν))
  have ht := (integral_restriction_tendsto hm hA hi).div hmass (by norm_num : (1:ℝ) ≠ 0)
  convert (config := {transparency := .instances, preTransparency := .instances}) ht using 1
  · funext n
    exact integral_normalizedRestriction (A n) f
  · rw [div_one]

 

lemma normalized_restriction_gibbs_tendsto {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) {H Y : X → ℝ}
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (hi : Integrable (fun x => Real.exp (H x)*Y x) ν)
    (hz : (∫ x, Real.exp (H x) ∂ν) ≠ 0) :
    Tendsto (fun n => (∫ x, Real.exp (H x)*Y x ∂normalizedRestriction ν (A n))/
      (∫ x, Real.exp (H x) ∂normalizedRestriction ν (A n))) atTop
      (𝓝 ((∫ x, Real.exp (H x)*Y x ∂ν)/(∫ x, Real.exp (H x) ∂ν))) :=
  (normalized_restriction_integral_tendsto hm hA hi).div
    (normalized_restriction_integral_tendsto hm hA he) hz



lemma abs_bounded_gibbs_test_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H D : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ x, |D x| ≤ c) :
    |(∫ x, Real.exp (H x)*D x ∂ν)/(∫ x, Real.exp (H x) ∂ν)| ≤ c := by
  have hi := he.mul_bdd hmD.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hD x))
  have hb : |∫ x, Real.exp (H x)*D x ∂ν| ≤ c*(∫ x, Real.exp (H x) ∂ν) := by
    calc
      _ ≤ ∫ x, |Real.exp (H x)*D x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, c*Real.exp (H x) ∂ν := by
        apply integral_mono hi.abs (he.const_mul c)
        intro x
        dsimp only
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        nlinarith [mul_le_mul_of_nonneg_left (hD x) (Real.exp_pos (H x)).le]
      _ = _ := integral_const_mul _ _
  have hz : 0 ≤ ∫ x, Real.exp (H x) ∂ν := integral_nonneg (fun _ => (Real.exp_pos _).le)
  rcases hz.eq_or_lt with hz | hz
  · simp only [← hz,div_zero,abs_zero]
    exact hc
  · rw [abs_div,abs_of_pos hz]
    exact (div_le_iff₀ hz).mpr hb



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma subtypeReference_preserving {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving Subtype.val (subtypeReference ν A) (normalizedRestriction ν A) := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [subtypeReference,Measure.map_smul,
    map_comap_subtype_coe hA]
  rfl

lemma subtypeReference_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0) :
    IsProbabilityMeasure (subtypeReference ν A) := by
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  have : IsProbabilityMeasure ((subtypeReference ν A).map Subtype.val) :=
    (subtypeReference_preserving ν hA).map_eq.symm ▸ inferInstance
  exact OAI.isProbabilityMeasure_of_map_ae measurable_subtype_coe.aemeasurable

lemma countable_reference_exhaustion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ A : ℕ → Set X, (∀ n, (A n).Finite) ∧ (∀ n, ν (A n) ≠ 0) ∧
      (∀ x, ∀ᶠ n in atTop, x ∈ A n) := by
  classical
  let := Encodable.ofCountable X
  have hx : ∃ x : X, ν {x} ≠ 0 := by
    by_contra! hn
    have hz : ν = 0 := Measure.ext_of_singleton (fun x => by simpa using hn x)
    have hu := measure_univ (μ := ν)
    simp only [hz, Measure.coe_zero, Pi.zero_apply] at hu
    exact zero_ne_one hu
  obtain ⟨x₀,hx₀⟩ := hx
  let A : ℕ → Set X := fun n => {x | Encodable.encode x ≤ n+Encodable.encode x₀}
  refine ⟨A,fun n => ?_,fun n => ?_,fun x => ?_⟩
  · exact (Set.finite_Iic _).preimage Encodable.encode_injective.injOn
  · intro hz
    apply hx₀
    exact measure_mono_null (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Nat.le_add_left _ _) hz
  · filter_upwards [eventually_ge_atTop (Encodable.encode x)] with n hn
    exact hn.trans (Nat.le_add_right _ _)

lemma referenceReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    |referenceReplicaMean ν H D| ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))) (Measure.pi (fun _ => ν))
  · exact abs_bounded_gibbs_test_le he hmD hc hD
  · rw [integral_undef he,div_zero,abs_zero]
    exact hc

lemma abs_integral_le_const_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : |∫ ω, F ω ∂μ| ≤ c := by
  calc
    _ ≤ ∫ ω, |F ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂μ := integral_mono ((integrable_of_measurable_abs_le hF hbound).abs)
      (integrable_const _) hbound
    _ = c := by simp

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ConvexDerivativeFluctuation
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma integral_tilted_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) :
    (∫ x, F x ∂ν.tilted H) = (∫ x, Real.exp (H x)*F x ∂ν)/(∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]

lemma measurable_random_tilted_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H F : Ω × X → ℝ} (hH : Measurable H) (hF : Measurable F) :
    Measurable (fun ω => ∫ x, F (ω,x) ∂(ν ω).tilted (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by change IsProbabilityMeasure (ν ω); infer_instance⟩
  simp_rw [integral_tilted_ratio]
  exact ((hH.exp.mul hF).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((hH.exp).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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

lemma referenceReplicaMean_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) (c : ℝ) :
    referenceReplicaMean ν H (fun σ => c*D σ) = c*referenceReplicaMean ν H D := by
  unfold referenceReplicaMean
  rw [show (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*(c*D σ)) =
    (fun σ => c*(Real.exp (∑ i, H (σ i))*D σ)) from by funext σ; ring,
    integral_const_mul]
  ring

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

end IsingPerceptron

namespace IsingPerceptron

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false, if_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true, if_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

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
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

lemma logMean_bounds (μ : Measure A) [IsProbabilityMeasure μ]
    {F : A → ℝ} (hF : Measurable F) {b K : ℝ} (hb : 0 < b)
    (hbound : ∀ a, |F a| ≤ K) : |logMean b μ F| ≤ K := by
  have hi : Integrable (fun a => Real.exp (b*F a)) μ := by
    apply Integrable.of_bound ((measurable_const.mul hF).exp).aestronglyMeasurable (Real.exp (b*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le)
  have hlow : Real.exp (-b*K) ≤ ∫ a, Real.exp (b*F a) ∂μ := by
    calc
      _ = ∫ _, Real.exp (-b*K) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro a
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp (hbound a)).1
        nlinarith
  have hhigh : (∫ a, Real.exp (b*F a) ∂μ) ≤ Real.exp (b*K) := by
    calc
      _ ≤ ∫ _, Real.exp (b*K) ∂μ := integral_mono hi (integrable_const _) (fun a =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le))
      _ = _ := by simp
  have hM := integral_exp_pos μ F hi
  rw [abs_le, logMean]
  constructor
  · apply (le_div_iff₀ hb).mpr
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have := Real.log_le_log hM hhigh
    rw [Real.log_exp] at this
    nlinarith

end IsingPerceptron

namespace IsingPerceptron

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

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

lemma pair_left_injective (j : ℕ) : Function.Injective (Nat.pair j) := by
  intro a b h
  have := congrArg Nat.unpair h
  simpa only [Nat.unpair_pair,Prod.mk.injEq,true_and] using this

lemma tagCoefficients_other {j k : ℕ} (hjk : j ≠ k) (a : ℕ →₀ ℝ) (i : ℕ) :
    tagCoefficients j a (Nat.pair k i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨v,hv⟩
  have := congrArg Nat.unpair hv
  simp only [Nat.unpair_pair,Prod.mk.injEq] at this
  exact hjk this.1

lemma cylinderCross_tag (j k : ℕ) (a b : ℕ →₀ ℝ) :
    cylinderCross (tagCoefficients j a) (tagCoefficients k b) =
      if j = k then cylinderCross a b else 0 := by
  classical
  unfold cylinderCross tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]
  by_cases h : j = k
  · subst k
    simp only [ite_true, if_true,Finsupp.mapDomain_apply (pair_left_injective j)]
  · simp only [h,ite_false, if_false]
    change a.sum (fun i c => c*tagCoefficients k b (Nat.pair j i)) = 0
    simp only [tagCoefficients_other (Ne.symm h),mul_zero]
    simp [Finsupp.sum]

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

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


lemma cylinderField_tag (j : ℕ) (a : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients j a) g = cylinderField a (fun i => g (Nat.pair j i)) := by
  unfold cylinderField tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbationAmplitude_sq (N j : ℕ) :
    (perturbationAmplitude N j)^2 = N*(perturbationScale N)^2*(perturbationWeight j)^2 := by
  unfold perturbationAmplitude
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

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

lemma exp_mul_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) (d : ℝ) :
    Integrable (fun x => Real.exp (d*U x)) P := by
  apply Integrable.of_bound ((measurable_const.mul hU).exp).aestronglyMeasurable (Real.exp (|d| * K))
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    change |d * U x| ≤ |d| * K
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)))

lemma bounded_tilted_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {U A : Ω → ℝ} (hU : Measurable U)
    {K C : ℝ} (hK : ∀ x, |U x| ≤ K) (hA : Measurable A) (hC : ∀ x, |A x| ≤ C) (d : ℝ) :
    |∫ x, A x ∂P.tilted (fun x => d*U x)| ≤ C := by
  let := isProbabilityMeasure_tilted (exp_mul_integrable_of_bound P hU hK d)
  exact abs_integral_le_integral_abs.trans (by
    calc
      (∫ x, |A x| ∂P.tilted (fun x => d*U x)) ≤ ∫ _ : Ω, C ∂P.tilted (fun x => d*U x) :=
        integral_mono (Integrable.of_bound hA.abs.aestronglyMeasurable C
          (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hC x)))
          (integrable_const _) hC
      _ = C := by simp)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) : Integrable U P :=
  Integrable.of_bound hU.aestronglyMeasurable K (ae_of_all _ (fun x => by simpa using hK x))

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

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

lemma uniformCell_right_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ)) atTop (𝓝 u) := by
  simpa only [add_div,Nat.cast_add,Nat.cast_one,add_zero] using
    (uniformCell_left_tendsto hu).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellAverage_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) (hc : ContinuousAt q u) :
    Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hc.tendsto.comp (uniformCell_left_tendsto hu)) (hc.tendsto.comp (uniformCell_right_tendsto hu))
    (fun n => (uniformCellAverage_bounds hq hb n _).1) (fun n => (uniformCellAverage_bounds hq hb n _).2)

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

lemma uniformCellAverage_ae_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  filter_upwards [monotone_ae_continuous_unit hq,ae_restrict_mem measurableSet_Ioo] with u hc hu
  exact uniformCellAverage_tendsto hq hb ⟨hu.1.le,hu.2⟩ hc

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
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ContactFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Faces. -/

noncomputable section

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma floor_on_uniformCell (n : ℕ) (i : Fin (n+1)) {u : ℝ}
    (hu : uniformCut n i.castSucc<u ∧ u<uniformCut n i.succ) : ⌊(n+1:ℕ)*u⌋₊=i.val := by
  have hleft : (i.val:ℝ)<(n+1:ℕ)*u := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mp hu.1
    simpa [uniformCut,mul_comm] using this
  apply (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i.val) hleft.le)).mpr
  constructor
  · exact hleft.le
  · have := (lt_div_iff₀ (by positivity)).mp hu.2
    simpa [uniformCut,mul_comm] using this

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite tensor features for spectral-overlap GG perturbations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma spectralSpinFeature_cross {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ τ : Spin N) :
    (∑ i : I, spectralSpinFeature U I σ i * spectralSpinFeature U I τ i) =
      projectedOverlap U I σ τ := by
  simp only [spectralSpinFeature, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm]
  unfold projectedOverlap
  congr 1
  exact Finset.sum_coe_sort I (fun i => U (spinVector σ) i * U (spinVector τ) i)

/-- The Gaussian tensor coefficient covariance is exactly the required
monomial in the individual spectral overlaps. -/
theorem spectralMonomialFeature_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    (∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature U I d σ v * spectralMonomialFeature U I d τ v) =
      ∏ a, projectedOverlap U (I a) σ τ ^ d a := by
  simp only [spectralMonomialFeature, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (v : Fin (d a) → I a) =>
    IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) v *
      IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) τ) v)]
  simp_rw [IsingPerceptron.tensorFeature_cross, spectralSpinFeature_cross]

theorem spectralMonomial_abs_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    |∏ a, projectedOverlap U (I a) σ τ ^ d a| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro a _
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one U (I a) σ τ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral-monomial enriched Ising model. Gaussian marks have a
separate variance at every site/tensor coordinate and every cascade level.
The spectral coefficients retain their actual dependence on the rotation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The concrete Gaussian covariance is the linear spin-field kernel plus
the required finite sum of spectral-overlap monomials. -/
theorem spinTensorFeature_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude τ i) =
      (site : ℝ) * (∑ i, spinValue (σ i) * spinValue (τ i)) +
        ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
          ∏ a, projectedOverlap U (I a) σ τ ^ degree j a := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (monomial j : ℝ) * amplitude j ^ 2 *
          ∑ v : SpectralTensorIndex I (degree j),
            spectralMonomialFeature U I (degree j) σ v * spectralMonomialFeature U I (degree j) τ v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spectralMonomialFeature_cross]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapPathCompact
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sequential L1 compactness of bounded monotone overlap paths. The
proof extracts the values on the rationals and discards only the
countable discontinuity set of the resulting monotone path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private lemma rational_le_lowerPath (f : ℚ → Icc (0 : ℝ) 1)
    {q : ℚ} {x : ℝ} (hq : (q : ℝ) < x) : (f q : ℝ) ≤ rationalLowerPath f x :=
  le_csSup (rationalLowerValues_bdd f x) ⟨q, hq, rfl⟩

private lemma rationalLowerPath_tendsto (p : ℕ → OverlapPath)
    (f : ℚ → Icc (0 : ℝ) 1)
    (hf : ∀ q : ℚ, Tendsto (fun n => p n (q : ℝ)) atTop (𝓝 (f q : ℝ)))
    (x : ℝ) (hx : ContinuousAt (rationalLowerPath f) x) :
    Tendsto (fun n => p n x) atTop (𝓝 (rationalLowerPath f x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨y, hy, hay⟩ := (lt_csSup_iff (rationalLowerValues_bdd f x)
      (rationalLowerValues_nonempty f x)).mp ha
    obtain ⟨q, hqx, rfl⟩ := hy
    filter_upwards [(hf q).eventually (Ioi_mem_nhds hay)] with n hn
    exact hn.trans_le ((p n).monotone hqx.le)
  · intro b hb
    have hnear : {y : ℝ | rationalLowerPath f y < b} ∈ 𝓝 x :=
      hx (Iio_mem_nhds hb)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    let y := x + ε / 2
    have hxy : x < y := by dsimp [y] <;> linarith
    have hy : rationalLowerPath f y < b := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
      dsimp [y]
      linarith
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
    have hqb : (f q : ℝ) < b := (rational_le_lowerPath f hqy).trans_lt hy
    filter_upwards [(hf q).eventually (Iio_mem_nhds hqb)] with n hn
    exact ((p n).monotone hxq.le).trans_lt hn

/-- Every sequence of overlap quantiles has an L1-convergent subsequence
with another admissible bounded monotone representative. -/
theorem overlapPath_ae_l1_subsequence (p : ℕ → OverlapPath) :
    ∃ q : OverlapPath, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s))) ∧
      Tendsto (fun n => ∫ s, |p (φ n) s - q s| ∂pathMeasure) atTop (𝓝 0) := by
  let f : ℕ → ℚ → Icc (0 : ℝ) 1 := fun n r => ⟨p n r, (p n).nonneg r, (p n).le_one r⟩
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq f
  let q := rationalLowerPath g
  have hr (r : ℚ) : Tendsto (fun n => p (φ n) (r : ℝ)) atTop (𝓝 (g r : ℝ)) :=
    (continuous_subtype_val.tendsto (g r)).comp ((continuous_apply r).tendsto g |>.comp hg)
  have hc : ∀ᵐ s ∂pathMeasure, ContinuousAt q s := by
    let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
    have hz := q.monotone.countable_not_continuousAt.measure_zero (μ := pathMeasure)
    have hae : ∀ᵐ s ∂pathMeasure, s ∉ {x | ¬ContinuousAt q x} := compl_mem_ae_iff.mpr hz
    filter_upwards [hae] with s hs
    exact not_not.mp hs
  have hpoint : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => p (φ n) s) atTop (𝓝 (q s)) := by
    filter_upwards [hc] with s hs
    exact rationalLowerPath_tendsto (fun n => p (φ n)) g hr s hs
  refine ⟨q, φ, hφ, hpoint, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |p (φ n) s - q s|) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((p (φ n)).measurable.sub q.measurable).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_le.mpr ⟨by linarith [(p (φ n)).nonneg s, q.le_one s],
        by linarith [(p (φ n)).le_one s, q.nonneg s]⟩) (by
      filter_upwards [hpoint] with s hs
      simpa only [sub_self, abs_zero] using (hs.sub_const (q s)).abs)
  simpa only [integral_zero] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly measurable Haar-dependent Gaussian tensor fields. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cylinderField_add (a b : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (a + b) g = cylinderField a g + cylinderField b g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderField]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, cylinderField_add, ih]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat Gaussian coefficients for root and finite-depth tensor marks. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorLeafCoefficients_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amplitude n v x)
      (tensorLeafCoefficients V I degree amplitude n v y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then
        ∑ j : SpinTensorIndex I degree, (v i j : ℝ) *
          spinTensorFeature U I degree amplitude x.1 j * spinTensorFeature V I degree amplitude y.1 j
        else 0 := by
  classical
  rw [tensorLeafCoefficients, tensorLeafCoefficients, featureCoefficients_diagonal
    (treeFeatureTag n x.2) (treeFeatureTag n y.2)
    (fun i j h => ((treeFeatureTag_cross n x.2 y.2 i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
  · simp only [hi, ite_true, if_true]
    apply Finset.sum_congr rfl
    intro j _
    have hs : (NNReal.sqrt (v i j) : ℝ) ^ 2 = (v i j : ℝ) :=
      by exact_mod_cast NNReal.sq_sqrt (v i j)
    calc
      _ = (NNReal.sqrt (v i j) : ℝ) ^ 2 *
          spinTensorFeature U I degree amplitude x.1 j *
            spinTensorFeature V I degree amplitude y.1 j := by ring
      _ = _ := by rw [hs]
  · simp only [hi, ite_false, if_false, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's linear enrichment and monomial tree variance increments. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma varianceIncrement_coe {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    (varianceIncrement q i : ℝ) = pathIncrement q i :=
  Real.coe_toNNReal _ (pathIncrement_nonneg hq h0 i)

private lemma prefixPath_weighted_sum (q : ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (c : ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i * c else 0) = q d * c := by
  calc
    _ = (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [pathIncrement_prefix q n d hd]

private lemma prefixPath_linear_monomials {k : ℕ} (h : ℕ → ℝ)
    (q : Fin k → ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (a : ℝ) (b : Fin k → ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then
      pathIncrement h i * a + ∑ j, pathIncrement (q j) i * b j else 0) =
      h d * a + ∑ j, q j d * b j := by
  calc
    _ = (∑ i : Fin (n + 1), ((if i.1 ≤ d then pathIncrement h i * a else 0) +
        ∑ j, if i.1 ≤ d then pathIncrement (q j) i * b j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_add_distrib, prefixPath_weighted_sum h n d hd a, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact prefixPath_weighted_sum (q j) n d hd (b j)

/-- The tensor mark model with these increments has exactly the paper's
linear field covariance plus the displayed joint spectral/tree monomials. -/
theorem tensorPathProfile_covariance {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (tensorLeafCoefficients U I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) y) =
      h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)) +
        ∑ j, amplitude j ^ 2 * (∏ a, projectedOverlap U (I a) x.1 y.1 ^ degree j a) *
          treeOverlap n x.2 y.2 ^ treeDegree j := by
  rw [tensorLeafCoefficients_cross]
  simp_rw [tensorPathProfile, spinTensorFeature_covariance, varianceIncrement_coe hh h0,
    varianceIncrement_coe (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  have he := prefixPath_linear_monomials h (fun j => monomialPath n (treeDegree j)) n
    (labeledCommonDepth n x.2 y.2) (labeledCommonDepth_le n x.2 y.2)
    (∑ a, spinValue (x.1 a) * spinValue (y.1 a))
    (fun j => amplitude j ^ 2 * ∏ a, projectedOverlap U (I a) x.1 y.1 ^ degree j a)
  simp_rw [mul_assoc] at he ⊢
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [monomialPath, treeOverlap]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform covariance bounds for the monomials omitted when the
perturbation cutoff changes by a fixed cavity size. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_weighted_kernel_abs_le {J : ℕ} (u K : Fin J → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |∑ j : Fin J, perturbationWeight j ^ 2 * u j ^ 2 * K j| ≤ 4 := by
  have hw (j : ℕ) : perturbationWeight j ^ 2 ≤ perturbationWeight j := by
    nlinarith [perturbationWeight_nonneg j, perturbationWeight_le_one j]
  calc
    _ ≤ ∑ j : Fin J, |perturbationWeight j ^ 2 * u j ^ 2 * K j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin J, 4 * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hu2 : u j ^ 2 ≤ 4 := by
        have hj := abs_le.mp (hu j)
        nlinarith
      rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc
        _ ≤ perturbationWeight j ^ 2 * u j ^ 2 :=
          mul_le_of_le_one_right (by positivity) (hK j)
        _ ≤ perturbationWeight j ^ 2 * 4 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)
        _ ≤ _ := by nlinarith [hw j]
    _ = 4 * (1 - (1 / 2 : ℝ) ^ J) := by rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ 4 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityComparisonRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-dependent errors in the finite cavity comparison.
The geometric cutoff is retained with its full Gaussian amplitude. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityWeightedKernel_abs_le (N : ℕ) (u K : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |cavityWeightedKernel N u K| ≤ 4 :=
  cavity_weighted_kernel_abs_le (fun j : Fin N => u j) (fun j : Fin N => K j)
    (fun j => hu j) (fun j => hK j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity error bound for the actual finite Gaussian perturbation:
the spectral/tree monomials, their amplitudes and dimension cutoff are
kept explicit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityPerturbationCoefficients_cross {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityPerturbationCoefficients U I u depth x)
      (cavityPerturbationCoefficients U I u depth y) =
      (N * perturbationScale N ^ 2) * cavityWeightedKernel N u (cavityPerturbationKernel U I x y) := by
  rw [cavityPerturbationCoefficients, cavityPerturbationCoefficients,
    tensorPathProfile_covariance U I _ _ depth _ (fun _ => 0) monotone_const le_rfl]
  simp only [zero_mul, Finset.sum_const_zero, zero_add, tensorPerturbationAmplitude, mul_pow, perturbationAmplitude_sq,
    cavityWeightedKernel, Finset.mul_sum, cavityPerturbationKernel]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma cavityPerturbationKernel_abs_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × LabeledLeaf depth) (j : ℕ) :
    |cavityPerturbationKernel U I x y j| ≤ 1 := by
  rw [cavityPerturbationKernel, abs_mul, abs_pow]
  have hT : |treeOverlap depth x.2 y.2| ≤ 1 := by
    rw [abs_of_nonneg (treeOverlap_mem depth x.2 y.2).1]
    exact (treeOverlap_mem depth x.2 y.2).2
  exact (mul_le_mul (spectralMonomial_abs_le_one U I _ x.1 y.1)
    (pow_le_one₀ (abs_nonneg _) hT) (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq
      (one_mul 1)

lemma cavityPerturbationCoefficients_sq_le {N m depth : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (x : Spin N × LabeledLeaf depth) :
    (cavityPerturbationCoefficients U I u depth x).sum (fun _ z => z ^ 2) ≤
      4 * (N * perturbationScale N ^ 2) := by
  rw [← cylinderCross_self, cavityPerturbationCoefficients_cross]
  have hb := cavityWeightedKernel_abs_le N u (cavityPerturbationKernel U I x x) hu
    (cavityPerturbationKernel_abs_le U I x x)
  have ha : 0 ≤ (N : ℝ) * perturbationScale N ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left (abs_le.mp hb).2 ha
  simpa only [mul_comm] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiberFactor
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tied overlap levels remain tied in an almost-everywhere limit. A
monotone factor through the overlap is then constructed explicitly;
no invertibility or absence of plateaus is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

private lemma cavityFiberValues_bdd (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    BddAbove (cavityFiberValues p B D z) := by
  refine ⟨1, ?_⟩
  rintro y (rfl | ⟨s, _, rfl⟩)
  · norm_num
  · exact B.le_one s

private lemma cavityFiberFactor_mono (p B : OverlapPath) (D : Set ℝ) :
    Monotone (fun z => sSup (cavityFiberValues p B D z)) := by
  intro x y hxy
  apply csSup_le_csSup (cavityFiberValues_bdd p B D y) (insert_nonempty _ _)
  rintro z (rfl | ⟨s, hs, rfl⟩)
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨s, ⟨hs.1, hs.2.trans hxy⟩, rfl⟩

private lemma cavityFiberFactor_bounds (p B : OverlapPath) (D : Set ℝ) (z : ℝ) :
    0 ≤ sSup (cavityFiberValues p B D z) ∧ sSup (cavityFiberValues p B D z) ≤ 1 := by
  constructor
  · exact le_csSup (cavityFiberValues_bdd p B D z) (mem_insert _ _)
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, _, rfl⟩)
    · norm_num
    · exact B.le_one s

private lemma cavityFiberFactor_eq (p B : OverlapPath) (D : Set ℝ)
    (hD : ∀ x ∈ D, ∀ y ∈ D, p x = p y → B x = B y)
    {x : ℝ} (hx : x ∈ D) : sSup (cavityFiberValues p B D (p x)) = B x := by
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    rintro y (rfl | ⟨s, hs, rfl⟩)
    · exact B.nonneg x
    · rcases le_or_gt s x with h | h
      · exact B.monotone h
      · have he : p s = p x := le_antisymm hs.2 (p.monotone h.le)
        exact (hD s hs.1 x hx he).le
  · exact le_csSup (cavityFiberValues_bdd p B D (p x))
      (mem_insert_of_mem _ ⟨x, ⟨hx, le_rfl⟩, rfl⟩)

/-- An a.e. limit of functions constant on every overlap fiber is still
a measurable function of that overlap, even on positive-mass plateaus. -/
theorem cavity_limit_factors_through_overlap_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ n x, x ∈ D → ∀ y, y ∈ D → p x = p y → Bseq n x = Bseq n y)
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ x ∈ E, ∀ y ∈ E, p x = p y → B x = B y := by
    intro x hx y hy hxy
    have he : (fun n => Bseq n x) = (fun n => Bseq n y) :=
      funext (fun n => htied n x hx.1 y hy.1 hxy)
    exact tendsto_nhds_unique hx.2 (he ▸ hy.2)
  refine ⟨fun z => sSup (cavityFiberValues p B E z),
    cavityFiberFactor_mono p B E, cavityFiberFactor_bounds p B E, ?_⟩
  filter_upwards [hDae, hlim] with s hs hls
  exact (cavityFiberFactor_eq p B E hE ⟨hs, hls⟩).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMeasurableTests
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous overlap tests determine a bounded measurable residual
once it is known to be a function of that overlap. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_ae_zero_of_measurable_overlap_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ z, |f z| ≤ 1)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ x, Φ (p x) * f (p x) ∂μ) = 0) :
    ∀ᵐ x ∂μ, f (p x) = 0 := by
  let ν := μ.map p
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hs : Integrable (fun z => f z ^ 2) ν :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hb z) 2).trans_eq (one_pow 2))
  have hsmall (ε : ℝ) (hε : 0 < ε) : (∫ z, f z ^ 2 ∂ν) ≤ ε := by
    obtain ⟨Φ, hΦ, hiΦ⟩ := hi.exists_boundedContinuous_integral_sub_le hε
    have hicross : Integrable (fun z => Φ z * f z) ν := by
      apply Integrable.of_bound (Φ.continuous.measurable.mul hf).aestronglyMeasurable ‖Φ‖
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        exact (mul_le_mul (Φ.norm_coe_le_norm z) (hb z) (abs_nonneg _) (norm_nonneg _)).trans_eq
          (mul_one _)
    have herr : Integrable (fun z => (f z - Φ z) * f z) ν := by
      apply (hi.sub hiΦ).abs.mono'
        (((hf.sub Φ.continuous.measurable).mul hf).aestronglyMeasurable)
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb z)
    have hz : (∫ z, Φ z * f z ∂ν) = 0 := by
      change (∫ z, (Φ * f) z ∂μ.map p) = 0
      rw [integral_map hp.aemeasurable ((Φ.continuous.measurable.mul hf).aestronglyMeasurable)]
      exact htest Φ
    have he : (∫ z, f z ^ 2 ∂ν) = (∫ z, (f z - Φ z) * f z ∂ν) +
        ∫ z, Φ z * f z ∂ν := by
      rw [← integral_add herr hicross]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring
    rw [he, hz, add_zero]
    calc
      _ ≤ ∫ z, |f z - Φ z| ∂ν := integral_mono herr (hi.sub hiΦ).abs (fun z => by
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hb z)))
      _ ≤ ε := by simpa only [Real.norm_eq_abs] using hΦ
  have hzero : (∫ z, f z ^ 2 ∂ν) = 0 := by
    apply le_antisymm _ (integral_nonneg (fun z => sq_nonneg (f z)))
    by_contra hn
    have hpos : 0 < ∫ z, f z ^ 2 ∂ν := lt_of_not_ge hn
    have hh := hsmall ((∫ z, f z ^ 2 ∂ν) / 2) (half_pos hpos)
    linarith
  have hae : ∀ᵐ z ∂ν, f z = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z)) hs).mp hzero] with z hz
    exact sq_eq_zero_iff.mp hz
  exact (ae_map_iff hp.aemeasurable (hf (measurableSet_singleton 0))).mp hae

/-- This is the separation step in cavity self-consistency, including
positive-mass plateaus of the limiting total-overlap path. -/
theorem cavity_overlap_self_consistency (p B : OverlapPath) (g : ℝ → ℝ)
    (hg : Monotone g) (hgb : ∀ z, 0 ≤ g z ∧ g z ≤ 1)
    (hfactor : B.val =ᵐ[pathMeasure] fun s => g (p s))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ s, Φ (p s) * (B s - p s) ∂pathMeasure) = 0) :
    B.val =ᵐ[pathMeasure] p.val := by
  let f := fun z => g z - max 0 (min 1 z)
  have hf : Measurable f := hg.measurable.sub (measurable_const.max (measurable_const.min measurable_id))
  have hb (z : ℝ) : |f z| ≤ 1 := by
    have hc : 0 ≤ max 0 (min 1 z) ∧ max 0 (min 1 z) ≤ 1 := by
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    exact abs_le.mpr ⟨by dsimp [f] <;> linarith [(hgb z).1, hc.2],
      by dsimp [f] <;> linarith [(hgb z).2, hc.1]⟩
  have he (s : ℝ) : max 0 (min 1 (p s)) = p s :=
    (congrArg (max 0) (min_eq_right (p.le_one s))).trans (max_eq_right (p.nonneg s))
  have hz := cavity_ae_zero_of_measurable_overlap_tests pathMeasure p p.measurable f hf hb (by
    intro Φ
    rw [← htest Φ]
    apply integral_congr_ae
    filter_upwards [hfactor] with s hs
    simp only [f, he, hs])
  filter_upwards [hfactor, hz] with s hs hsz
  rw [hs]
  exact sub_eq_zero.mp (by simpa only [f, he] using hsz)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityAsymptoticSelfConsistency
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic preservation of plateau values suffices for cavity
self-consistency. Exact ties at every approximation are unnecessary. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_limit_factors_asymptotic_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => Bseq n x - Bseq n y) atTop (𝓝 0))
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ᵐ s ∂pathMeasure, s ∈ E := hDae.and hlim
  have heq : ∀ x, x ∈ E → ∀ y, y ∈ E → p x = p y → B x = B y := by
    intro x hx y hy hxy
    exact sub_eq_zero.mp (tendsto_nhds_unique (hx.2.sub hy.2) (htied x hx.1 y hy.1 hxy))
  exact cavity_limit_factors_through_overlap_on p B (fun _ s => B s) E hE
    (fun _ x hx y hy hxy => heq x hx y hy hxy) (ae_of_all _ fun _ => tendsto_const_nhds)


theorem cavity_self_consistency_asymptotic_l1_on (p : OverlapPath) (B : ℕ → OverlapPath)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => B n x - B n y) atTop (𝓝 0))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg (fun s => abs_nonneg _))
  · intro ε hε
    by_contra hbad
    have hb : ∃ᶠ n in atTop, ε ≤ ∫ s, |B n s - p s| ∂pathMeasure := by
      simpa only [Filter.not_eventually, not_lt] using hbad
    obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hb
    obtain ⟨Q, ψ, hψ, hpoint, hL1⟩ := overlapPath_ae_l1_subsequence (fun n => B (φ n))
    obtain ⟨g, hg, hgb, hfactor⟩ := cavity_limit_factors_asymptotic_on p Q
      (fun n s => B (φ (ψ n)) s) D hDae (fun x hx y hy hxy => (htied x hx y hy hxy).comp
        (hφ.comp hψ).tendsto_atTop) hpoint
    have hQtests (Φ : ℝ →ᵇ ℝ) : (∫ s, Φ (p s) * (Q s - p s) ∂pathMeasure) = 0 := by
      have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
        (F := fun n s => Φ (p s) * (B (φ (ψ n)) s - p s))
        (f := fun s => Φ (p s) * (Q s - p s)) (fun _ => ‖Φ‖)
        (fun n => ((Φ.continuous.measurable.comp p.measurable).mul
          ((B (φ (ψ n))).measurable.sub p.measurable)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_mul]
          have hdiff : |B (φ (ψ n)) s - p s| ≤ 1 := abs_le.mpr
            ⟨by linarith [(B (φ (ψ n))).nonneg s, p.le_one s],
              by linarith [(B (φ (ψ n))).le_one s, p.nonneg s]⟩
          exact (mul_le_mul (Φ.norm_coe_le_norm _) hdiff (abs_nonneg _) (norm_nonneg _)).trans_eq
            (mul_one _)) (by
          filter_upwards [hpoint] with s hs
          exact tendsto_const_nhds.mul (hs.sub_const (p s)))
      exact tendsto_nhds_unique hlim ((htest Φ).comp (hφ.comp hψ).tendsto_atTop)
    have heq := cavity_overlap_self_consistency p Q g hg hgb hfactor hQtests
    have hsame (n : ℕ) : (∫ s, |B (φ (ψ n)) s - Q s| ∂pathMeasure) =
        ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with s hs
      rw [hs]
    have hzero : Tendsto (fun n => ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure) atTop (𝓝 0) := by
      simpa only [hsame] using hL1
    obtain ⟨n, hn⟩ := (hzero.eventually (Iio_mem_nhds hε)).exists
    exact (not_le_of_gt hn) (hφbad (ψ n))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_BaseGaussianVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian variance for the countable spin/leaf partition with base energy. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma cylinder_cgf_memLp_two {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    (t : ℝ) :
    MemLp (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      2 gaussianCoordinates := by
  let H := fun p : (ℕ → ℝ) × X => t * cylinderField (A p.2) p.1
  have hH : Measurable H := (measurable_cylinderFields A).const_mul t
  have hLaw (x : X) : gaussianCoordinates.map (fun g => H (g, x)) =
      gaussianReal 0 (⟨t ^ 2, sq_nonneg t⟩ * (((A x).sum (fun _ c => c ^ 2)).toNNReal)) :=
    cylinder_scaled_law A x t
  have hVar (x : X) :
      ((⟨t ^ 2, sq_nonneg t⟩ : ℝ≥0) * (((A x).sum (fun _ c => c ^ 2)).toNNReal) : ℝ) ≤ t ^ 2 * B := by
    change t ^ 2 * (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ _
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)
  exact (memLp_two_iff_integrable_sq
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable.log.aestronglyMeasurable).mpr
    (gaussian_log_partition_second (ν := ν) hH hLaw hVar).1

/-- Splitting off a fixed integrable base energy is an almost-everywhere
identity for the actual countable Gaussian partition, including nonuniform
and cascade-leaf weights. -/
lemma cylinder_log_partition_base {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    (fun g : ℕ → ℝ => Real.log (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν))
      =ᵐ[gaussianCoordinates]
    (fun g => Real.log (∫ x, Real.exp (H x) ∂ν) +
      cgf (fun x => cylinderField (A x) g) (ν.tilted H) t) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have hVar (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  have he := (gaussian_field_exp_integrable (ν := ν.tilted H)
    (measurable_cylinderFields A) (fun x => cylinderField_law (A x)) hVar t).1.prod_right_ae
  filter_upwards [he] with g hg
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := integral_exp_pos hH
  have hz' : 0 < ∫ x, Real.exp (t * cylinderField (A x) g) ∂ν.tilted H := integral_exp_pos hg
  have hi := integral_exp_tilted (μ := ν) H (fun x => t * cylinderField (A x) g)
  have hid : (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν) =
      (∫ x, Real.exp (H x) ∂ν) *
        (∫ x, Real.exp (t * cylinderField (A x) g) ∂ν.tilted H) := by
    rw [hi]
    simp only [Pi.add_apply]
    field_simp
  rw [hid, Real.log_mul hz.ne' hz'.ne']
  rfl

lemma cylinder_log_partition_memLp_two {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    MemLp (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν)) 2 gaussianCoordinates := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have he := cylinder_log_partition_base ν H hH A hA t
  exact MemLp.ae_eq (Filter.EventuallyEq.symm he)
    ((memLp_const (Real.log (∫ x, Real.exp (H x) ∂ν))).add
      (cylinder_cgf_memLp_two (ν.tilted H) A hA t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianBaseComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stability of the actual Gaussian partition under bounded base-energy changes. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_partition_exp_integrable_ae {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    ∀ᵐ g : ℕ → ℝ ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x + cylinderField (A x) g)) ν := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have hv (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  have he := (gaussian_field_exp_integrable (ν := ν.tilted H)
    (measurable_cylinderFields A) (fun x => cylinderField_law (A x)) hv 1).1.prod_right_ae
  filter_upwards [he] with g hg
  simpa only [one_mul, smul_eq_mul, ← Real.exp_add] using
    (integrable_tilted_iff hH (fun x => Real.exp (1 * cylinderField (A x) g))).mp hg

/-- A uniform deterministic energy change bounds the mean logpartition
change, for every countable prior and bounded-variance Gaussian field. -/
theorem countable_cylinder_log_mean_base_compare {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (hJ : Integrable (fun x => Real.exp (J x)) ν)
    (A : X → ℕ →₀ ℝ) {B K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    (hK : ∀ x, |H x - J x| ≤ K) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates| ≤ K := by
  have hiH := (cylinder_log_partition_memLp_two ν H hH A hA 1).integrable (by norm_num)
  have hiJ := (cylinder_log_partition_memLp_two ν J hJ A hA 1).integrable (by norm_num)
  simp only [one_mul] at hiH hiJ
  rw [← integral_sub hiH hiJ, ← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le_const (μ := gaussianCoordinates) (C := K) ?_).trans_eq (by simp)
  filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA,
    cylinder_partition_exp_integrable_ae ν J hJ A hA] with g hgH hgJ
  have h := logMean_abs_sub_le ν (b := 1) (by norm_num)
    (by simpa only [one_mul] using hgH) (by simpa only [one_mul] using hgJ)
    (fun x => by simpa only [add_sub_add_right_eq_sub] using hK x)
  simpa only [logMean, div_one, one_mul, Real.norm_eq_abs] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBaseExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-prior exhaustion with the bounded deterministic cavity energy
left inside the partition. A uniform second moment gives convergence of
the actual expected logarithms. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_bounded_base_exp_integrable {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M : ℝ} (hH : ∀ x, |H x| ≤ M) :
    Integrable (fun x => Real.exp (H x)) ν := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.exp M)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hH x)))

lemma cavity_bounded_base_log_second {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M : ℝ} (hH : ∀ x, |H x| ≤ M)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    (∫ g : ℕ → ℝ, (Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)) ^ 2
      ∂gaussianCoordinates) ≤ 2 * M ^ 2 + 8 * Real.exp (2 * B) := by
  have hiH := cavity_bounded_base_exp_integrable ν H hH
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hiH
  let L := Real.log (∫ x, Real.exp (H x) ∂ν)
  let Q := fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) (ν.tilted H) 1
  have hc : |L| ≤ M := by
    simpa only [logMean, div_one, one_mul] using
      logMean_bounds ν (measurable_of_countable H) (by norm_num : (0 : ℝ) < 1) hH
  have hc2 : L ^ 2 ≤ M ^ 2 := by
    have hh := abs_le.mp hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith [hh.1] : 0 ≤ M + L)]
  have hv (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  have hs := gaussian_log_partition_second (ν := ν.tilted H) (measurable_cylinderFields A)
    (fun x => cylinderField_law (A x)) hv
  have hs : Integrable (fun g => (Q g) ^ 2) gaussianCoordinates ∧
      (∫ g, (Q g) ^ 2 ∂gaussianCoordinates) ≤ 4 * Real.exp (2 * B) := by
    simpa only [Q, cgf, mgf, one_mul] using hs
  have he := cylinder_log_partition_base ν H hiH A hA 1
  simp only [one_mul] at he
  have hip : Integrable (fun g => (L + Q g) ^ 2) gaussianCoordinates :=
    (memLp_two_iff_integrable_sq ((memLp_const L).add
      (cylinder_cgf_memLp_two (ν.tilted H) A hA 1)).aestronglyMeasurable).mp
      ((memLp_const L).add (cylinder_cgf_memLp_two (ν.tilted H) A hA 1))
  calc
    _ = ∫ g, (L + Q g) ^ 2 ∂gaussianCoordinates :=
      integral_congr_ae (he.mono (fun g hg => congrArg (fun z : ℝ => z ^ 2) hg))
    _ ≤ ∫ g, (2 * M ^ 2 + 2 * (Q g) ^ 2) ∂gaussianCoordinates := by
      apply integral_mono hip ((integrable_const _).add (hs.1.const_mul 2))
      intro g
      change (L + Q g) ^ 2 ≤ 2 * M ^ 2 + 2 * (Q g) ^ 2
      nlinarith [sq_nonneg (L - Q g)]
    _ = 2 * M ^ 2 + 2 * (∫ g, (Q g) ^ 2 ∂gaussianCoordinates) := by
      rw [integral_add (integrable_const _) (hs.1.const_mul 2)]
      simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    _ ≤ _ := by linarith [hs.2]

theorem cavity_bounded_base_restriction_mean_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    {M : ℝ} (hH : ∀ x, |H x| ≤ M)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ g : ℕ → ℝ, Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) g) ∂normalizedRestriction ν (S n))
        ∂gaussianCoordinates) atTop
      (𝓝 (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates)) := by
  let νn := fun n => normalizedRestriction ν (S n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hm (n : ℕ) : Measurable (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) g) ∂νn n)) :=
    (((measurable_of_countable H).comp measurable_snd).add
      (measurable_cylinderFields A)).exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hi (n : ℕ) : Integrable (fun g : ℕ → ℝ => (Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) g) ∂νn n)) ^ 2) gaussianCoordinates := by
    apply (memLp_two_iff_integrable_sq (hm n).aestronglyMeasurable).mp
    simpa only [one_mul] using cylinder_log_partition_memLp_two (νn n) H
      (cavity_bounded_base_exp_integrable (νn n) H hH) A hA 1
  apply (integral_tendsto_of_second_moment_bound hm hi
    (fun n => cavity_bounded_base_log_second (νn n) H hH A hA) ?_).2
  filter_upwards [cylinder_partition_exp_integrable_ae ν H
    (cavity_bounded_base_exp_integrable ν H hH) A hA] with g hg
  have hz : 0 < ∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν := integral_exp_pos hg
  exact (Real.continuousAt_log hz.ne').tendsto.comp
    (normalized_restriction_integral_tendsto hS hExh hg)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_BoundedObservableMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic spectral-diagonal perturbation estimate at a parameter minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_bounded_random_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω × X → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : ∀ ω x, |Y (ω, x)| ≤ B) (t : ℝ) :
    Integrable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) P := by
  have hm : Measurable (fun ω => cgf (fun x => Y (ω, x)) (ν ω) t) := by
    simpa only [cgf, mgf, referencePartition] using
      (measurable_random_referencePartition hν (hY.const_mul t)).log
  apply Integrable.of_bound hm.aestronglyMeasurable (|t| * B)
  exact ae_of_all _ fun ω => by
    have hYm : Measurable (fun x => t * Y (ω, x)) :=
      (hY.comp (measurable_const.prodMk measurable_id)).const_mul t
    have hb : ∀ x, |t * Y (ω, x)| ≤ |t| * B := fun x => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ω x) (abs_nonneg _)
    have h := logMean_bounds (ν ω) hYm (b := 1) (by norm_num) hb
    simpa only [cgf, mgf, logMean, one_mul, div_one, Real.norm_eq_abs] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomBoundedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded random observable has a differentiable disorder-averaged CGF.
This applies to the actual temperature observable retaining common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_bounded_random_tilted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω → X → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB : ∀ ω x, |Y ω x| ≤ B) (t : ℝ) :
    Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t * Y ω x)) P := by
  have hm := measurable_random_tilted_integral hν (hY.const_mul t) hY
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry_apply_pair, id_eq] using bounded_tilted_integral_abs (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityBoundedSecant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Gibbs tests can be compared through logarithmic generating
functions. Hoeffding's bound makes the finite-difference error uniform
over the reference probability, including cavity cutoffs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma cavity_bounded_cgf_secant {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → ℝ) (hY : Measurable Y)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |Y x| ≤ B) (s : ℝ) :
    s * (∫ x, Y x ∂ν) ≤ cgf Y ν s ∧
      cgf Y ν s ≤ s * (∫ x, Y x ∂ν) + B ^ 2 * s ^ 2 / 2 := by
  have hi := exp_mul_integrable_of_bound ν hY hbound s
  have hpos : 0 < mgf Y ν s := MeasureTheory.integral_exp_pos hi
  have hlow : s * (∫ x, Y x ∂ν) ≤ cgf Y ν s := by
    apply (Real.le_log_iff_exp_le hpos).mpr
    have hh := exp_integral_le_partition ((bounded_integrable ν hY hbound).const_mul s) hi
    simpa only [integral_const_mul, mgf] using hh
  have hsub := hasSubgaussianMGF_of_mem_Icc hY.aemeasurable
    (ae_of_all ν (fun x => abs_le.mp (hbound x)))
  have hu := hsub.cgf_le s
  have hshift : cgf (fun x => Y x - ∫ y, Y y ∂ν) ν s =
      cgf Y ν s - s * (∫ x, Y x ∂ν) := by
    change Real.log (mgf (fun x => Y x + -(∫ y, Y y ∂ν)) ν s) = _
    rw [mgf_add_const, Real.log_mul hpos.ne' (Real.exp_ne_zero _), Real.log_exp]
    unfold cgf
    ring
  rw [hshift] at hu
  have hn : (((‖B - -B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = B ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
      Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg hB hB)]
    norm_num
  rw [hn] at hu
  exact ⟨hlow, by linarith⟩

lemma cavity_secant_comparison_algebra {a b F G B ε s : ℝ} (hs : 0 < s)
    (hF : s * a ≤ F ∧ F ≤ s * a + B ^ 2 * s ^ 2 / 2)
    (hG : s * b ≤ G ∧ G ≤ s * b + B ^ 2 * s ^ 2 / 2)
    (hFG : |F - G| ≤ ε) :
    |a - b| ≤ ε / s + B ^ 2 * s / 2 := by
  have hε := abs_le.mp hFG
  have hh : |s * (a - b)| ≤ ε + B ^ 2 * s ^ 2 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hF.1, hF.2, hG.1, hG.2]
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    |a - b| * s = |s * (a - b)| := by rw [abs_mul, abs_of_pos hs, mul_comm]
    _ ≤ ε + B ^ 2 * s ^ 2 / 2 := hh
    _ = (ε / s + B ^ 2 * s / 2) * s := by field_simp

theorem cavity_bounded_random_test_compare {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν η : Ω → Measure X) (hν : Measurable ν) (hη : Measurable η)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (η ω)]
    (Y : Ω → X → ℝ) (hY : Measurable (Function.uncurry Y))
    {B ε s : ℝ} (hB : 0 ≤ B) (hbound : ∀ ω x, |Y ω x| ≤ B) (hs : 0 < s)
    (hcgf : |(∫ ω, cgf (Y ω) (ν ω) s ∂P) -
      ∫ ω, cgf (Y ω) (η ω) s ∂P| ≤ ε) :
    |(∫ ω, ∫ x, Y ω x ∂ν ω ∂P) - ∫ ω, ∫ x, Y ω x ∂η ω ∂P| ≤
      ε / s + B ^ 2 * s / 2 := by
  have hiν : Integrable (fun ω => ∫ x, Y ω x ∂ν ω) P := by
    simpa only [zero_mul, tilted_const] using
      integrable_bounded_random_tilted_mean P ν hν Y hY B hbound 0
  have hiη : Integrable (fun ω => ∫ x, Y ω x ∂η ω) P := by
    simpa only [zero_mul, tilted_const] using
      integrable_bounded_random_tilted_mean P η hη Y hY B hbound 0
  have hbounds (μ : Ω → Measure X) (hμ : Measurable μ)
      [∀ ω, IsProbabilityMeasure (μ ω)]
      (hi : Integrable (fun ω => ∫ x, Y ω x ∂μ ω) P) :
      s * (∫ ω, ∫ x, Y ω x ∂μ ω ∂P) ≤ ∫ ω, cgf (Y ω) (μ ω) s ∂P ∧
      (∫ ω, cgf (Y ω) (μ ω) s ∂P) ≤
        s * (∫ ω, ∫ x, Y ω x ∂μ ω ∂P) + B ^ 2 * s ^ 2 / 2 := by
    have hic := integrable_bounded_random_cgf P μ hμ (Function.uncurry Y) hY B hbound s
    have hb (ω : Ω) := cavity_bounded_cgf_secant (μ ω) (Y ω)
      (hY.comp (measurable_const.prodMk measurable_id)) hB (hbound ω) s
    constructor
    · have hh := integral_mono (hi.const_mul s) hic (fun ω => (hb ω).1)
      simpa only [integral_const_mul, Function.uncurry_apply_pair] using hh
    · have hh := integral_mono hic ((hi.const_mul s).add (integrable_const _))
        (fun ω => (hb ω).2)
      simpa only [Pi.add_apply, Function.uncurry_apply_pair,
        integral_add (hi.const_mul s) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul] using hh
  exact cavity_secant_comparison_algebra hs (hbounds ν hν hiν) (hbounds η hη hiη) hcgf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianPenaltyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gibbs algebra for absorbing a nonuniform covariance error
by a penalty proportional to the squared cavity projection. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_covariance_gibbs_bound {X : Type*} [Fintype X]
    (p V : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    {c : ℝ} (hK : ∀ x y, |K x y| ≤ c * (V x + V y)) :
    |∑ x, p x * (K x x - ∑ y, p y * K x y)| ≤ 4 * c * ∑ x, p x * V x := by
  let B := ∑ x, p x * V x
  have hpair (x : X) : |∑ y, p y * K x y| ≤ c * (V x + B) := by
    calc
      _ ≤ ∑ y, |p y * K x y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, p y * (c * (V x + V y)) := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg (hp y)]
        exact mul_le_mul_of_nonneg_left (hK x y) (hp y)
      _ = c * (V x + B) := by
        simp only [mul_add, Finset.sum_add_distrib]
        have hconst : (∑ y, p y * (c * V x)) = c * V x := by
          rw [← Finset.sum_mul, hsum, one_mul]
        have hvar : (∑ y, p y * (c * V y)) = c * B := by
          dsimp only [B]
          rw [Finset.mul_sum]
          congr 1
          ext y
          ring
        rw [hconst, hvar]
  have hrow (x : X) : |K x x - ∑ y, p y * K x y| ≤ c * (3 * V x + B) := by
    have h := (abs_sub _ _).trans (add_le_add (hK x x) (hpair x))
    linarith
  calc
    _ ≤ ∑ x, |p x * (K x x - ∑ y, p y * K x y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p x * (c * (3 * V x + B)) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hp x)]
      exact mul_le_mul_of_nonneg_left (hrow x) (hp x)
    _ = 4 * c * B := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hconst : (∑ x, p x * (c * B)) = c * B := by
        rw [← Finset.sum_mul, hsum, one_mul]
      have hvar : (∑ x, p x * (c * (3 * V x))) = 3 * c * B := by
        dsimp only [B]
        rw [Finset.mul_sum]
        congr 1
        ext x
        ring
      rw [hconst, hvar]
      ring

lemma cavity_covariance_penalty_nonneg {X : Type*} [Fintype X]
    (p V : X → ℝ) (K : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    {c : ℝ} (hK : ∀ x y, |K x y| ≤ c * (V x + V y)) :
    0 ≤ ∑ x, p x * (4 * c * V x + K x x - ∑ y, p y * K x y) := by
  have h := (abs_le.mp (cavity_covariance_gibbs_bound p V K hp hsum hK)).1
  have he : (∑ x, p x * (4 * c * V x + K x x - ∑ y, p y * K x y)) =
      4 * c * (∑ x, p x * V x) + ∑ x, p x * (K x x - ∑ y, p y * K x y) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    ext x
    ring
  rw [he]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian integration by parts with a nonuniform one-replica penalty.
The bound depends on the cavity projection size, not its maximum over
all spin configurations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_gaussian_penalty_insertion {X : Type*} [Fintype X]
    {d : ℕ} {w : X → ℝ} (hw : GibbsReference w) (H D : X → ℝ)
    (A C : X → Fin (d + 1) → ℝ) :
    (∫ g, ∑ x, gaussianGibbs w H C g x * (D x + linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
    ∫ g, ∑ x, gaussianGibbs w H C g x *
      (D x + gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hiD (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x) μ := by
    apply (Integrable.of_bound (continuous_gaussianGibbs hw H C x).aestronglyMeasurable 1
      (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianGibbs w H C g x from
          finiteGibbs_nonneg hw _ x)]
        exact finiteGibbs_le_one hw _ x))).mul_const
  have hiL (x : X) : Integrable (fun g => gaussianGibbs w H C g x * linearGaussian A g x) μ := by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x
  have hiK (x : X) : Integrable (fun g => gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) μ := by
    simpa only [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
      integrable_replica_covariance (r := 1) hw H A C x (fun _ => x)
  have hleft (g : Fin (d + 1) → ℝ) :
      (∑ x, gaussianGibbs w H C g x * (D x + linearGaussian A g x)) =
        ∑ x, (gaussianGibbs w H C g x * D x + gaussianGibbs w H C g x * linearGaussian A g x) := by
    simp only [mul_add]
  have hright (g : Fin (d + 1) → ℝ) :
      (∑ x, gaussianGibbs w H C g x *
        (D x + gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) =
      ∑ x, (gaussianGibbs w H C g x * D x + gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hiLeft (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x +
      gaussianGibbs w H C g x * linearGaussian A g x) μ := (hiD x).add (hiL x)
  have hiRight (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x +
      gaussianGibbs w H C g x * (gaussianCross A C x x -
        ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) μ := (hiD x).add (hiK x)
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ (fun x _ => hiLeft x),
    integral_finsetSum _ (fun x _ => hiRight x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_add (hiD x) (hiL x), integral_add (hiD x) (hiK x)]
  congr 1
  simpa only [mul_comm] using gaussian_gibbs_insertion hw H A C x

/-- A penalty of `4c V` absorbs a covariance insertion bounded by
`c(V(x)+V(y))`, uniformly over the other base energy. -/
theorem cavity_gaussian_penalty_nonneg {X : Type*} [Fintype X]
    {d : ℕ} {w : X → ℝ} (hw : GibbsReference w) (H V : X → ℝ)
    (A C : X → Fin (d + 1) → ℝ) (c : ℝ)
    (hK : ∀ x y, |gaussianCross A C x y| ≤ c * (V x + V y)) :
    0 ≤ ∫ g, ∑ x, gaussianGibbs w H C g x * (4 * c * V x + linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  rw [cavity_gaussian_penalty_insertion hw H (fun x => 4 * c * V x) A C]
  apply integral_nonneg
  intro g
  exact cavity_covariance_penalty_nonneg (gaussianGibbs w H C g) V (gaussianCross A C)
    (fun x => finiteGibbs_nonneg hw _ x) (finiteGibbs_sum hw _) hK

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotationCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trigonometric interpolation between independent Gaussian fields,
with the cavity-size penalty removed along the same path. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavityGaussianCurve_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurve C A t) g x =
      Real.cos t * linearGaussian C g x + Real.sin t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurve, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurveDerivative_linear {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    linearGaussian (cavityGaussianCurveDerivative C A t) g x =
      -Real.sin t * linearGaussian C g x + Real.cos t * linearGaussian A g x := by
  simp only [linearGaussian, cavityGaussianCurveDerivative, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma cavityGaussianCurve_hasDerivAt {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    HasDerivAt (fun s => linearGaussian (cavityGaussianCurve C A s) g x)
      (linearGaussian (cavityGaussianCurveDerivative C A t) g x) t := by
  simp_rw [cavityGaussianCurve_linear, cavityGaussianCurveDerivative_linear]
  exact ((Real.hasDerivAt_cos t).mul_const _).add ((Real.hasDerivAt_sin t).mul_const _)

lemma cavityPenaltyCurve_hasDerivAt {X : Type*} (H V : X → ℝ) (c t : ℝ) (x : X) :
    HasDerivAt (fun s => cavityPenaltyCurve H V c s x)
      (4 * c * Real.sin t * Real.cos t * V x) t := by
  have h := (hasDerivAt_const t (H x)).sub
    ((((Real.hasDerivAt_cos t).pow 2).const_mul (2 * c)).mul_const (V x))
  change HasDerivAt (fun s => H x - 2 * c * Real.cos s ^ 2 * V x) _ t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma cavityGaussianCurveDerivative_bound {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (g : Fin d → ℝ) (x : X) :
    |linearGaussian (cavityGaussianCurveDerivative C A t) g x| ≤
      |linearGaussian C g x| + |linearGaussian A g x| := by
  rw [cavityGaussianCurveDerivative_linear]
  calc
    _ ≤ |-Real.sin t * linearGaussian C g x| + |Real.cos t * linearGaussian A g x| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_neg]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _)).trans_eq (one_mul _))
        ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _)).trans_eq (one_mul _))

lemma cavityGaussianCurve_cross {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (t : ℝ) (x y : X)
    (hCA : ∀ x y, gaussianCross C A x y = 0) :
    gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      (Real.sin t * Real.cos t) * (gaussianCross A A x y - gaussianCross C C x y) := by
  have hAC : gaussianCross A C x y = 0 := by
    simpa only [gaussianCross, mul_comm] using hCA y x
  have hexpand : gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y =
      -Real.sin t * Real.cos t * gaussianCross C C x y +
      (-Real.sin t * Real.sin t) * gaussianCross C A x y +
      (Real.cos t * Real.cos t) * gaussianCross A C x y +
      Real.cos t * Real.sin t * gaussianCross A A x y := by
    simp only [gaussianCross, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cavityGaussianCurveDerivative, cavityGaussianCurve]
    ring
  rw [hexpand, hCA x y, hAC]
  ring

lemma cavityGaussianCurve_cross_bound {X : Type*} {d : ℕ}
    (C A : X → Fin d → ℝ) (V : X → ℝ) (c t : ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hK : ∀ x y, |gaussianCross A A x y - gaussianCross C C x y| ≤ c * (V x + V y))
    (ht : 0 ≤ Real.sin t * Real.cos t) (x y : X) :
    |gaussianCross (cavityGaussianCurveDerivative C A t) (cavityGaussianCurve C A t) x y| ≤
      (c * Real.sin t * Real.cos t) * (V x + V y) := by
  rw [cavityGaussianCurve_cross C A t x y hCA, abs_mul, abs_of_nonneg ht]
  convert mul_le_mul_of_nonneg_left (hK x y) ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianCurveMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the finite Gaussian interpolation while removing the
nonuniform cavity penalty. The derivative is nonnegative under the
pointwise covariance-error bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

omit [Fintype X] in
lemma cavityPenaltyCurve_derivative_bound (V : X → ℝ) (c t : ℝ) (x : X) :
    |4 * c * Real.sin t * Real.cos t * V x| ≤ 4 * |c| * |V x| := by
  have hsc : |Real.sin t| * |Real.cos t| ≤ 1 := by
    exact (mul_le_mul (Real.abs_sin_le_one t) (Real.abs_cos_le_one t)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  calc
    _ = (4 * |c| * |V x|) * (|Real.sin t| * |Real.cos t|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      ring
    _ ≤ (4 * |c| * |V x|) * 1 := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = _ := mul_one _

lemma cavityGaussianCurveMean_hasDerivAt {d : ℕ} {w : X → ℝ}
    (hw : GibbsReference w) (H V : X → ℝ) (c : ℝ) (C A : X → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (cavityGaussianCurveMean w H V c C A)
      (cavityGaussianCurveSlope w H V c C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let B := fun g : Fin d → ℝ => ∑ x,
    (4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c s x + linearGaussian (cavityGaussianCurve C A s) g x))) μ := by
    simpa only [one_mul] using
      (continuous_log_finitePartition hw (cavityPenaltyCurve H V c s)
        (cavityGaussianCurve C A s) 1).aestronglyMeasurable
  have hi : Integrable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c t x + linearGaussian (cavityGaussianCurve C A t) g x))) μ := by
    simpa only [one_mul] using
      integrable_log_finitePartition hw (cavityPenaltyCurve H V c t) (cavityGaussianCurve C A t) 1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x,
      gaussianGibbs w (cavityPenaltyCurve H V c s) (cavityGaussianCurve C A s) g x *
      (4 * c * Real.sin s * Real.cos s * V x + linearGaussian (cavityGaussianCurveDerivative C A s) g x))
    (bound := B) Filter.univ_mem (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro x _
    exact (continuous_gaussianGibbs hw _ _ x).mul
      (continuous_const.add (by unfold linearGaussian; fun_prop))
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    apply finiteGibbs_average_bound hw
    intro x
    calc
      _ ≤ |4 * c * Real.sin s * Real.cos s * V x| +
          |linearGaussian (cavityGaussianCurveDerivative C A s) g x| := abs_add_le _ _
      _ ≤ 4 * |c| * |V x| + (|linearGaussian C g x| + |linearGaussian A g x|) :=
        add_le_add (cavityPenaltyCurve_derivative_bound V c s x)
          (cavityGaussianCurveDerivative_bound C A s g x)
      _ ≤ B g := by
        simpa only [B, add_assoc] using Finset.single_le_sum
          (f := fun x => 4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
          (fun _ _ => by positivity) (Finset.mem_univ x)
  · exact integrable_finsetSum _ (fun x _ =>
      ((integrable_const _).add (integrable_linearGaussian C x).abs).add
        (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    apply hasDerivAt_log_finitePartition hw
    intro x
    exact (cavityPenaltyCurve_hasDerivAt H V c s x).add (cavityGaussianCurve_hasDerivAt C A s g x)

theorem cavity_finite_gaussian_penalty_comparison {d : ℕ} {w : X → ℝ}
    (hw : GibbsReference w) (H V : X → ℝ) (c : ℝ) (C A : X → Fin (d + 1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hK : ∀ x y, |gaussianCross A A x y - gaussianCross C C x y| ≤ c * (V x + V y)) :
    (∫ g, Real.log (finitePartition w (fun x => H x - 2 * c * V x + linearGaussian C g x))
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) ≤
    ∫ g, Real.log (finitePartition w (fun x => H x + linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := cavityGaussianCurveMean_hasDerivAt hw H V c C A s
  have hslope (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
      0 ≤ cavityGaussianCurveSlope w H V c C A s := by
    have hsc : 0 ≤ Real.sin s * Real.cos s := by
      apply mul_nonneg
      · exact Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
    have h := cavity_gaussian_penalty_nonneg hw (cavityPenaltyCurve H V c s) V
      (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s)
      (c * Real.sin s * Real.cos s) (cavityGaussianCurve_cross_bound C A V c s hCA hK hsc)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    unfold cavityGaussianCurveSlope
    congr 1
    funext g
    congr 1
    funext x
    ring
  have hm : MonotoneOn (cavityGaussianCurveMean w H V c C A)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    exact hslope s (interior_subset hs)
  have hp : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hm ⟨le_rfl, hp⟩ ⟨hp, le_rfl⟩ hp
  simpa only [cavityGaussianCurveMean, cavityPenaltyCurve, linearGaussian, cavityGaussianCurve,
    Real.cos_zero, Real.sin_zero, one_pow, mul_one, one_mul, zero_mul, add_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, zero_add] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCylinderPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cavity comparison for cylinder fields. Independent copies
are realized by disjoint coordinate tags, preserving both endpoint laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma finite_cylinder_penalty_comparison {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H V : X → ℝ) (c : ℝ) (C A : X → ℕ →₀ ℝ)
    (hCA : ∀ x y, cylinderCross (C x) (A y) = 0)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound (Sum.elim C A)
  have hC (x : X) : ∀ j ∈ (C x).support, j < n + 1 :=
    fun j hj => hn (Sum.inl x) j (Finsupp.mem_support_iff.mp hj)
  have hA (x : X) : ∀ j ∈ (A x).support, j < n + 1 :=
    fun j hj => hn (Sum.inr x) j (Finsupp.mem_support_iff.mp hj)
  let C' : X → Fin (n + 1) → ℝ := fun x i => C x i
  let A' : X → Fin (n + 1) → ℝ := fun x i => A x i
  let w := fun x => ν.real {x}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  have hca : ∀ x y, gaussianCross C' A' x y = 0 := by
    intro x y
    simp only [gaussianCross, C', A']
    rw [← cylinderCross_prefix (C x) (A y) (hC x)]
    exact hCA x y
  have hk : ∀ x y, |gaussianCross A' A' x y - gaussianCross C' C' x y| ≤
      c * (V x + V y) := by
    intro x y
    simp only [gaussianCross, C', A']
    rw [← cylinderCross_prefix (A x) (A y) (hA x),
      ← cylinderCross_prefix (C x) (C y) (hC x)]
    exact hK x y
  have he (D : X → ℝ) (Q : X → ℕ →₀ ℝ)
      (hQ : ∀ x j, j ∈ (Q x).support → j < n + 1) :
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (D x + cylinderField (Q x) g) ∂ν)
        ∂gaussianCoordinates) =
      ∫ g, Real.log (finitePartition w (fun x => D x +
        linearGaussian (fun (x : X) (i : Fin (n + 1)) => Q x i) g x))
          ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    have hp (g : ℕ → ℝ) : Real.log (∫ x, Real.exp (D x + cylinderField (Q x) g) ∂ν) =
        Real.log (finitePartition w (fun x => D x +
          linearGaussian (fun (x : X) (i : Fin (n + 1)) => Q x i) (fun i => g i) x)) := by
      rw [integral_fintype Integrable.of_finite]
      simp only [finitePartition, w, cylinderField_eq_prefix _ (hQ _)]
      rfl
    simp_rw [hp]
    exact (gaussian_prefix_measurePreserving (n + 1)).hasLaw.integral_comp
      (by simpa only [one_mul] using
        (continuous_log_finitePartition hw D (fun (x : X) (i : Fin (n + 1)) => Q x i) 1).aestronglyMeasurable)
  rw [he (fun x => H x - 2 * c * V x) C hC, he H A hA]
  exact cavity_finite_gaussian_penalty_comparison hw H V c C' A' hca hk

lemma cylinder_log_mean_tag {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) (H : X → ℝ)
    (A : X → ℕ →₀ ℝ) (j : ℕ) :
    (∫ g : ℕ → ℝ, Real.log (∫ x,
      Real.exp (H x + cylinderField (tagCoefficients j (A x)) g) ∂ν) ∂gaussianCoordinates) =
    ∫ g : ℕ → ℝ, Real.log (∫ x,
      Real.exp (H x + cylinderField (A x) g) ∂ν) ∂gaussianCoordinates := by
  have hm : Measurable (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)) := by
    exact (((measurable_of_countable H).comp measurable_snd).add
      (measurable_cylinderFields A)).exp.stronglyMeasurable.integral_prod_right'.measurable.log
  simpa only [Function.comp_def, cylinderField_tag, gaussianCoordinates] using
    (gaussian_pullback_measurePreserving (Nat.pair j) (pair_left_injective j)).hasLaw.integral_comp
      hm.aestronglyMeasurable

/-- Only the two covariance kernels matter: disjoint Gaussian copies
automatically supply the zero mixed covariance required by interpolation. -/
theorem finite_cylinder_covariance_penalty_comparison {X : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H V : X → ℝ) (c : ℝ)
    (C A : X → ℕ →₀ ℝ)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have h := finite_cylinder_penalty_comparison ν H V c
    (fun x => tagCoefficients 0 (C x)) (fun x => tagCoefficients 1 (A x))
    (fun x y => by simp only [cylinderCross_tag, ite_false, if_false, zero_ne_one])
    (fun x y => by simpa only [cylinderCross_tag, ite_true, if_true] using hK x y)
  simpa only [cylinder_log_mean_tag] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCountablePenalty
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonuniform covariance comparison on the actual countable prior.
Finite restrictions converge in expected log partition, retaining the
cavity-size penalty without replacing it by a uniform maximum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem countable_cylinder_covariance_penalty_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H V : X → ℝ) (c : ℝ)
    {M D : ℝ} (hH : ∀ x, |H x| ≤ M) (hV : ∀ x, |V x| ≤ D)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hp : ∀ x, |H x - 2 * c * V x| ≤ M + 2 * |c| * D := by
    intro x
    calc
      _ ≤ |H x| + |2 * c * V x| := abs_sub _ _
      _ = |H x| + 2 * |c| * |V x| := by norm_num [abs_mul]
      _ ≤ _ := add_le_add (hH x) (mul_le_mul_of_nonneg_left (hV x) (by positivity))
  have hm₀ := cavity_bounded_base_restriction_mean_tendsto ν
    (fun x => H x - 2 * c * V x) hp C hC (fun n => (hS n).measurableSet) hExh hpos
  have hm₁ := cavity_bounded_base_restriction_mean_tendsto ν H hH A hA
    (fun n => (hS n).measurableSet) hExh hpos
  apply le_of_tendsto_of_tendsto hm₀ hm₁
  apply Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := finite_cylinder_covariance_penalty_comparison (subtypeReference ν (S n))
    (fun x => H x) (fun x => V x) c (fun x => C x) (fun x => A x)
    (fun x y => hK x y)
  have he (J : X → ℝ) (Q : X → ℕ →₀ ℝ) (g : ℕ → ℝ) :
      (∫ x : S n, Real.exp (J x + cylinderField (Q x) g) ∂subtypeReference ν (S n)) =
      ∫ x, Real.exp (J x + cylinderField (Q x) g) ∂normalizedRestriction ν (S n) :=
    (subtypeReference_preserving ν (hS n).measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (J x + cylinderField (Q x) g))).aestronglyMeasurable
  simpa only [he (fun x => H x - 2 * c * V x) C, he H A] using hf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityUniformComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform covariance comparison on a fixed cavity cutoff. The bound
also holds after adding any common bounded replica-test energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_log_mean_const_add {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B) (c : ℝ) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (c + H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) =
    c + ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have he : (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (c + H x + cylinderField (A x) g) ∂ν)) =ᵐ[gaussianCoordinates]
      (fun g => c + Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)) := by
    filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA] with g hg
    simpa only [logMean, one_mul, div_one, add_assoc] using
      logMean_const_add ν (by norm_num : (1 : ℝ) ≠ 0)
        (by simpa only [one_mul] using hg) c
  rw [integral_congr_ae he]
  have hi := (cylinder_log_partition_memLp_two ν H hH A hA 1).integrable (by norm_num)
  simp only [one_mul] at hi
  rw [integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul]

lemma countable_cylinder_covariance_mean_le {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {M : ℝ}
    (hH : ∀ x, |H x| ≤ M) (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    2 * K + ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hb : ∀ x, |2 * K + H x| ≤ 2 * K + M := by
    intro x
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (mul_nonneg (by norm_num) hK)]; linarith [hH x])
  have h := countable_cylinder_covariance_penalty_comparison ν (fun x => 2 * K + H x)
    (fun _ => 1) K hb (show ∀ _x : X, |(1 : ℝ)| ≤ 1 from fun _ => by norm_num) C A hC hA
    (fun x y => (hcov x y).trans (by nlinarith))
  have he (x : X) : 2 * K + H x - 2 * K * (1 : ℝ) = H x := by ring
  simp_rw [he] at h
  rwa [cylinder_log_mean_const_add ν H (cavity_bounded_base_exp_integrable ν H hH) A hA] at h

theorem countable_cylinder_uniform_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H J : X → ℝ)
    {M₀ M₁ B₀ B₁ K E : ℝ} (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K + E := by
  have h₁ := countable_cylinder_covariance_mean_le ν H hH C A hC hA hK hcov
  have h₂ := countable_cylinder_covariance_mean_le ν H hH A C hA hC hK
    (fun x y => by simpa only [abs_sub_comm] using hcov x y)
  have hG : |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K := abs_le.mpr ⟨by linarith, by linarith⟩
  have hD := countable_cylinder_log_mean_base_compare ν H J
    (cavity_bounded_base_exp_integrable ν H hH) (cavity_bounded_base_exp_integrable ν J hJ)
    A hA hbase
  exact (abs_sub_le _ _ _).trans (add_le_add hG hD)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded test comparison for finite spin/leaf restrictions. A common
test tilt reduces comparison of Gibbs means to the covariance-only
log-partition estimate and a uniform bounded-variable secant bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma finite_cylinder_test_cgf_eq {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H F : X → ℝ) (A : X → ℕ →₀ ℝ) {B : ℝ}
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B) (s : ℝ) :
    (∫ g : ℕ → ℝ, cgf F (ν.tilted (fun x => H x + cylinderField (A x) g)) s
      ∂gaussianCoordinates) =
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + s * F x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) -
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have he (g : ℕ → ℝ) :
      cgf F (ν.tilted (fun x => H x + cylinderField (A x) g)) s =
      Real.log (∫ x, Real.exp (H x + s * F x + cylinderField (A x) g) ∂ν) -
      Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν) := by
    rw [cgf, mgf, integral_exp_tilted]
    rw [Real.log_div (MeasureTheory.integral_exp_pos Integrable.of_finite).ne'
      (MeasureTheory.integral_exp_pos Integrable.of_finite).ne']
    simp only [Pi.add_apply]
    simp_rw [show ∀ x, (H x + cylinderField (A x) g) + s * F x =
      H x + s * F x + cylinderField (A x) g from fun x => by ring]
  simp_rw [he]
  apply integral_sub
  · simpa only [one_mul] using
      (cylinder_log_partition_memLp_two ν (fun x => H x + s * F x)
        Integrable.of_finite A hA 1).integrable (by norm_num)
  · simpa only [one_mul] using
      (cylinder_log_partition_memLp_two ν H Integrable.of_finite A hA 1).integrable (by norm_num)

theorem cavity_finite_test_comparison {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J F : X → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (C x) g)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => J x + cylinderField (A x) g)
        ∂gaussianCoordinates| ≤
      (2 * (2 * K + E)) / s + B ^ 2 * s / 2 := by
  let μ := fun g : ℕ → ℝ => ν.tilted (fun x => H x + cylinderField (C x) g)
  let η := fun g : ℕ → ℝ => ν.tilted (fun x => J x + cylinderField (A x) g)
  have : ∀ g, IsProbabilityMeasure (μ g) := fun _ => isProbabilityMeasure_tilted Integrable.of_finite
  have : ∀ g, IsProbabilityMeasure (η g) := fun _ => isProbabilityMeasure_tilted Integrable.of_finite
  have hμ : Measurable μ := measurable_random_tilted_measure (ν := fun _ : ℕ → ℝ => ν)
    (H := fun z : (ℕ → ℝ) × X => H z.2 + cylinderField (C z.2) z.1) measurable_const
    (((measurable_of_countable H).comp measurable_snd).add (measurable_cylinderFields C))
  have hη : Measurable η := measurable_random_tilted_measure (ν := fun _ : ℕ → ℝ => ν)
    (H := fun z : (ℕ → ℝ) × X => J z.2 + cylinderField (A z.2) z.1) measurable_const
    (((measurable_of_countable J).comp measurable_snd).add (measurable_cylinderFields A))
  apply cavity_bounded_random_test_compare gaussianCoordinates μ η hμ hη (fun _ => F)
    ((measurable_of_countable F).comp measurable_snd) hB (fun _ => hF) hs
  rw [finite_cylinder_test_cgf_eq ν H F C hC s, finite_cylinder_test_cgf_eq ν J F A hA s]
  have hHS : ∀ x, |H x + s * F x| ≤ M₀ + |s| * B := by
    intro x
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (hH x) (mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)))
  have hJS : ∀ x, |J x + s * F x| ≤ M₁ + |s| * B := by
    intro x
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (hJ x) (mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)))
  have htilt := countable_cylinder_uniform_comparison ν (fun x => H x + s * F x)
    (fun x => J x + s * F x) hHS hJS C A hC hA hK hcov
    (fun x => by simpa only [add_sub_add_right_eq_sub] using hbase x)
  have hzero := countable_cylinder_uniform_comparison ν H J hH hJ C A hC hA hK hcov hbase
  rw [show ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) from
    fun a b c d => by ring]
  exact (abs_sub _ _).trans (by linarith [htilt, hzero])

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTestExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Gibbs tests pass from finite leaf restrictions to the full
countable reference. Only almost-everywhere partition integrability is
needed for the full Gaussian field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_subtype_tilted_integral {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (H F : X → ℝ) :
    (∫ x : S, F x ∂(subtypeReference ν S).tilted (fun x => H x)) =
      ∫ x, F x ∂(normalizedRestriction ν S).tilted H := by
  rw [integral_tilted_eq_div, integral_tilted_eq_div]
  congr 1
  · exact (subtypeReference_preserving ν hS).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (H x) * F x)).aestronglyMeasurable
  · exact (subtypeReference_preserving ν hS).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (H x))).aestronglyMeasurable

lemma cavity_tilted_test_norm_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) : ‖∫ x, F x ∂ν.tilted H‖ ≤ K := by
  have hb := norm_integral_le_of_norm_le_const (μ := ν.tilted H) (f := F)
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hF x))
  exact hb.trans (mul_le_of_le_one_right hK measureReal_le_one)

lemma cavity_tilted_test_restriction_tendsto {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H F : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν) {K : ℝ} (hF : ∀ x, |F x| ≤ K)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) :
    Tendsto (fun n => ∫ x, F x ∂(normalizedRestriction ν (S n)).tilted H) atTop
      (𝓝 (∫ x, F x ∂ν.tilted H)) := by
  have hnum : Integrable (fun x => Real.exp (H x) * F x) ν := by
    apply (hH.mul_const K).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
  have hz : (∫ x, Real.exp (H x) ∂ν) ≠ 0 := (integral_exp_pos hH).ne'
  simp only [integral_tilted_eq_div]
  exact normalized_restriction_gibbs_tendsto hS hExh hH hnum hz

theorem cavity_cylinder_test_restriction_mean_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H F : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B K : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B)
    (hF : ∀ x, |F x| ≤ K) {S : ℕ → Set X} (hS : ∀ n, (S n).Finite)
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ g : ℕ → ℝ, ∫ x, F x
      ∂(normalizedRestriction ν (S n)).tilted (fun x => H x + cylinderField (A x) g)
        ∂gaussianCoordinates) atTop
      (𝓝 (∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (A x) g)
        ∂gaussianCoordinates)) := by
  let νn := fun n => normalizedRestriction ν (S n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  let G := fun (g : ℕ → ℝ) (x : X) => H x + cylinderField (A x) g
  have hG : Measurable (Function.uncurry G) := ((measurable_of_countable H).comp measurable_snd).add
    (measurable_cylinderFields A)
  have hm (n : ℕ) : Measurable (fun g : ℕ → ℝ => ∫ x, F x ∂(νn n).tilted (G g)) :=
    measurable_random_tilted_integral (ν := fun _ : ℕ → ℝ => νn n)
      (H := Function.uncurry G) (F := fun z : (ℕ → ℝ) × X => F z.2) measurable_const hG
      ((measurable_of_countable F).comp measurable_snd)
  apply tendsto_integral_of_dominated_convergence
    (μ := gaussianCoordinates)
    (F := fun n g => ∫ x, F x ∂(νn n).tilted (G g))
    (f := fun g => ∫ x, F x ∂ν.tilted (G g)) (fun _ : ℕ → ℝ => max K 0)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const (max K 0))
  · intro n
    exact ae_of_all _ (fun g => cavity_tilted_test_norm_le (νn n) (G g) F
      (le_max_right K 0) (fun x => (hF x).trans (le_max_left K 0)))
  · filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA] with g hg
    exact cavity_tilted_test_restriction_tendsto ν (G g) F hg hF
      (fun n => (hS n).measurableSet) hExh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCountableTest
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance comparison of bounded Gibbs tests on a countable prior,
proved by finite leaf exhaustion. The estimate is uniform in the cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_countable_test_comparison {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J F : X → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (C x) g)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => J x + cylinderField (A x) g)
        ∂gaussianCoordinates| ≤
      (2 * (2 * K + E)) / s + B ^ 2 * s / 2 := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hmC := cavity_cylinder_test_restriction_mean_tendsto ν H F
    (cavity_bounded_base_exp_integrable ν H hH) C hC hF hS hExh hpos
  have hmA := cavity_cylinder_test_restriction_mean_tendsto ν J F
    (cavity_bounded_base_exp_integrable ν J hJ) A hA hF hS hExh hpos
  apply le_of_tendsto ((hmC.sub hmA).abs)
  apply Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := cavity_finite_test_comparison (subtypeReference ν (S n))
    (fun x => H x) (fun x => J x) (fun x => F x) (fun x => hH x) (fun x => hJ x)
    (fun x => C x) (fun x => A x) (fun x => hC x) (fun x => hA x) hK
    (fun x y => hcov x y) (fun x => hbase x) hB (fun x => hF x) hs
  have heC (g : ℕ → ℝ) := cavity_subtype_tilted_integral ν (hS n).measurableSet
    (fun x => H x + cylinderField (C x) g) F
  have heA (g : ℕ → ℝ) := cavity_subtype_tilted_integral ν (hS n).measurableSet
    (fun x => J x + cylinderField (A x) g) F
  simp_rw [heC, heA] at hf
  exact hf

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRoundedSelfConsistency
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity identity is initially tested at the rounded overlap.
Passing those tests to the limiting overlap gives the L1 conclusion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_rounding_test_difference (p : OverlapPath)
    (q B : ℕ → OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure) atTop (𝓝 0) := by
  let F := fun n s => Φ (p s) * (B n s - p s) - Φ (q n s) * (B n s - q n s)
  have hΦ (z : ℝ) : |Φ z| ≤ ‖Φ‖ := by
    simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm z
  have hdiff (v w : OverlapPath) (s : ℝ) : |v s - w s| ≤ 1 :=
    abs_le.mpr ⟨by linarith [v.nonneg s, w.le_one s],
      by linarith [v.le_one s, w.nonneg s]⟩
  have hi (v w : OverlapPath) : Integrable (fun s => Φ (v s) * (w s - v s)) pathMeasure := by
    apply Integrable.of_bound ((Φ.continuous.measurable.comp v.measurable).mul
      (w.measurable.sub v.measurable)).aestronglyMeasurable ‖Φ‖
    exact ae_of_all _ fun s => by
      change |Φ (v s) * (w s - v s)| ≤ ‖Φ‖
      rw [abs_mul]
      exact (mul_le_mul (hΦ _) (hdiff w v s)
        (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hbound (n : ℕ) (s : ℝ) : |F n s| ≤
      |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s| := by
    have he : F n s = (Φ (p s) - Φ (q n s)) * (B n s - p s) +
        Φ (q n s) * (q n s - p s) := by dsimp only [F] <;> ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left (hdiff (B n) p s) (abs_nonneg _)).trans_eq (mul_one _))
      (mul_le_mul_of_nonneg_right (hΦ _) (abs_nonneg _))
  have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := F) (f := fun _ => (0 : ℝ)) (fun _ => 3 * ‖Φ‖)
    (fun n => ((hi p (B n)).sub (hi (q n) (B n))).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]
      have ha : |Φ (p s) - Φ (q n s)| ≤ 2 * ‖Φ‖ :=
        (abs_sub _ _).trans (by linarith [hΦ (p s), hΦ (q n s)])
      have hb := mul_le_mul_of_nonneg_left (hdiff (q n) p s) (norm_nonneg Φ)
      exact (hbound n s).trans (by linarith)) (by
      filter_upwards [hq] with s hs
      have hφ := Φ.continuous.continuousAt.tendsto.comp hs
      have hb : Tendsto (fun n => |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s|)
          atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => Φ (p s)) atTop (𝓝 (Φ (p s))) := tendsto_const_nhds
        simpa only [Function.comp_apply, sub_self, abs_zero, mul_zero, zero_add] using
          ((hc.sub hφ).abs.add ((hs.sub_const (p s)).abs.const_mul ‖Φ‖))
      apply squeeze_zero_norm (fun n => ?_) hb
      simpa only [Real.norm_eq_abs] using hbound n s)
  have he (n : ℕ) : (∫ s, F n s ∂pathMeasure) =
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure :=
    integral_sub (hi p (B n)) (hi (q n) (B n))
  simpa only [he, integral_zero] using hlim

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous nonnegative right derivative of the finite spectral
R-transform. Its extension at zero is the spectral variance; the constant
extension of `finiteR` to negative arguments is not differentiated there. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem cavityRDerivative_le (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) {K : ℝ} (_hK : 0 ≤ K)
    (hlam : ∀ a, |lam a| ≤ K) (x : ℝ) :
    cavityRDerivative rho lam hrho hsum x ≤ 4 * K ^ 2 := by
  have hR := finiteR_mem_interval rho lam hrho hsum
    (fun a => (abs_le.mp (hlam a)).1) (fun a => (abs_le.mp (hlam a)).2) x
  calc
    cavityRDerivative rho lam hrho hsum x ≤
        ∑ a, projectedResolventDerivative rho lam hrho hsum a x * (4 * K ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _
        (projectedResolventDerivative_pos rho lam hrho hsum a x).le
      have ha := abs_le.mp (hlam a)
      have hlow : -2 * K ≤ lam a - finiteR rho lam hrho hsum x := by linarith
      have hupp : lam a - finiteR rho lam hrho hsum x ≤ 2 * K := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)]
    _ = 4 * K ^ 2 := by rw [← Finset.sum_mul, sum_projectedResolventDerivative, one_mul]

end InvariantIsing

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite field path reconstructed by the cavity covariance.
Its covariance density has the continuous right-derivative value at zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma cavityFieldPrimitive_sub (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (p : OverlapPath) (a b : ℝ) :
    cavityFieldPrimitive rho lam hrho hsum p b - cavityFieldPrimitive rho lam hrho hsum p a =
      ∫ r in a..b, cavityFieldDensity rho lam hrho hsum p r := by
  have hc := continuous_cavityFieldDensity rho lam hrho hsum p
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  unfold cavityFieldPrimitive
  linarith

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

lemma fieldMagnetizationPath_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldMagnetizationPath h s = fieldMagnetizationLevel h i :=
  fieldLevelPath_on_cell h _ _ _ i hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict overlap levels for the finite-cascade approximation.  A small
convex mixture with evenly spaced interior levels removes ties and the
unit top endpoint while moving every level by at most the mixture size. -/

noncomputable section
open Set

namespace InvariantIsing

lemma cavityStrictLevels_dist {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin (n + 1)) : |cavityStrictLevels q ε i - q i| ≤ ε := by
  have hi := cavityInteriorLevel_mem i
  have hq' := hq i
  have hd : |cavityInteriorLevel i - q i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2, hq'.1, hq'.2]
  have he : cavityStrictLevels q ε i - q i = ε * (cavityInteriorLevel i - q i) := by
    dsimp only [cavityStrictLevels]
    ring
  rw [he, abs_mul, abs_of_nonneg hε]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hε

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityStrictUniformPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma cavityUniformLevel_on_cell (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityUniformLevel n s = i := by
  apply Fin.ext
  change min n ⌊(n + 1 : ℕ) * s⌋₊ = i.val
  rw [floor_on_uniformCell n i hs, min_eq_right (Nat.le_of_lt_succ i.isLt)]

lemma cavityStrictUniformPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityStrictUniformPath p n s = cavityStrictUniformLevels p n i := by
  change cavityStrictUniformLevels p n (cavityUniformLevel n s) = _
  rw [cavityUniformLevel_on_cell n i hs]

lemma cavityStrictUniformPath_dist (p : OverlapPath) (n : ℕ) (s : ℝ) :
    |cavityStrictUniformPath p n s - uniformCellAverage p n (uniformCellIndex n s)| ≤
      1 / ((n : ℝ) + 1) :=
  cavityStrictLevels_dist _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n).1.le (cavityUniformLevel n s)

lemma cavityStrictUniformPath_ae_tendsto (p : OverlapPath) :
    ∀ᵐ s ∂pathMeasure, Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) := by
  have ha := uniformCellAverage_ae_tendsto p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩)
  change ∀ᵐ s ∂pathMeasure, _ at ha
  filter_upwards [ha] with s hs
  have hd : Tendsto (fun n => cavityStrictUniformPath p n s -
      uniformCellAverage p n (uniformCellIndex n s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Real.norm_eq_abs] using cavityStrictUniformPath_dist p n s
  simpa only [sub_add_cancel, zero_add] using hd.add hs

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightRegularization
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
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

lemma fieldIncrement_le_last (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fieldIncrement h i).2 ≤ h.height (Fin.last h.depth) := by
  have hh := h.ordered_height (Fin.le_last i)
  change h.height i - (if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩) ≤ _
  split_ifs with hi
  · simpa only [sub_zero] using hh
  · exact (sub_le_self _ (h.nonneg _)).trans hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCurvatureBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical curvature is bounded by the remaining spin variance.
Consequently its mean-coordinate representative vanishes at both endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldCurvatureTransform_le_spin_variance {ζ : ℝ} (hζ : ζ ≤ 1) (v : ℝ≥0)
    {F M Q : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    {K C : ℝ} (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (hbound : ∀ y, Q y + (M y) ^ 2 ≤ 1) (z : ℝ) :
    fieldCurvatureTransform ζ v F M Q z ≤ 1 - (fieldSpinTransition ζ v F M z) ^ 2 := by
  have bM2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have hle := fieldSpinTransition_mono_test ζ v F (hQ.add (hM.pow_const 2))
    measurable_const
    (fun y => (abs_add_le _ _).trans (add_le_add (bQ y) (bM2 y)))
    (fun _ => by norm_num : ∀ y : ℝ, |(1 : ℝ)| ≤ 1) hbound z
  change fieldSpinTransition ζ v F (fun y => Q y + M y ^ 2) z ≤
    fieldSpinTransition ζ v F (fun _ => 1) z at hle
  rw [fieldSpinTransition_add ζ v hF hG hQ (hM.pow_const 2) bQ bM2,
    fieldSpinTransition_const ζ v hF hG] at hle
  have hvar := fieldSpinTransition_square_le ζ v hF hG hM bM z
  have hc : ζ * (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2) ≤
      fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2 := by
    exact mul_le_of_le_one_left (sub_nonneg.mpr hvar) hζ
  unfold fieldCurvatureTransform
  linarith

lemma field_logCosh_spin_variance (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  have hc := (Real.cosh_pos z).ne'
  have hr := Real.cosh_sq_sub_sinh_sq z
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith

lemma fieldScalarLogCoshSecond_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) z ≤
      1 - (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh z) ^ 2 := by
  induction L generalizing z with
  | nil =>
    change 1 / (Real.cosh z) ^ 2 ≤ 1 - (Real.tanh z) ^ 2
    linarith [field_logCosh_spin_variance z]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hb : ∀ y, fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) y +
        (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh y) ^ 2 ≤ 1 := by
      intro y
      linarith [ih ht htζ y]
    exact fieldCurvatureTransform_le_spin_variance (hζ av List.mem_cons_self) av.2
      hv.1 hv.2 ha.1 hq.1 ha.2 hq.2 hb z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conditional spin mean is spatially one-Lipschitz,
uniformly in the number and variances of the finite field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCoshMean_dist_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (x y : ℝ) :
    |fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh x -
      fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y| ≤ |x - y| := by
  have hd z := hasDerivAt_fieldScalarLogCoshMean L hL z
  have hb (z : ℝ) :
      ‖fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
        (fun z => 1 / (Real.cosh z) ^ 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (fieldScalarLogCoshSecond_pos L hL z)]
    exact (fieldScalarLogCoshSecond_le_spin_variance L hL hζ z).trans
      (sub_le_self _ (sq_nonneg _))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (C := 1)
    (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hb z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative conditional-variance bound for a Lipschitz spin
mean. The constant depends only on an upper bound for the Gaussian
variance, rather than on the depth of the scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussianMomentCap_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ fieldGaussianMomentCap C := by
  have hb := (field_centered_tilt_second_moment (U := fun _ => 0) measurable_const
    (C := C) (fun u => by simpa using mul_nonneg hC (abs_nonneg u))).2
  exact (integral_nonneg (fun u => sq_nonneg (1 + |u|))).trans hb

lemma field_centered_spin_variance {U M : ℝ → ℝ}
    (hU : Measurable U) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    {C : ℝ} (hUb : ∀ u, |U u| ≤ C * |u|) (x : ℝ) (v : ℝ≥0) :
    variance (fun u => M (x + Real.sqrt (v : ℝ) * u)) ((gaussianReal 0 1).tilted U) ≤
      (v : ℝ) * fieldGaussianMomentCap C := by
  let μ := (gaussianReal 0 1).tilted U
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  let X := fun u => M (x + Real.sqrt (v : ℝ) * u)
  have hmX : Measurable X := hM.comp (by fun_prop)
  have hmD : AEStronglyMeasurable (fun u => X u - M x) μ :=
    (hmX.sub_const _).aestronglyMeasurable
  have hLp : MemLp (fun u => X u - M x) 2 μ :=
    MemLp.of_bound hmD 2 (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by dsimp only [X] <;> linarith [hMb (x + Real.sqrt (v : ℝ) * u), hMb x]))
  obtain ⟨hi, hb⟩ := field_centered_tilt_second_moment hU hUb
  have hp (u : ℝ) : (X u - M x)^2 ≤ (v : ℝ) * (1 + |u|)^2 := by
    have hl : |X u - M x| ≤ Real.sqrt (v : ℝ) * |u| := by
      simpa only [X, add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
        hML (x + Real.sqrt (v : ℝ) * u) x
    have hs := pow_le_pow_left₀ (abs_nonneg _) hl 2
    rw [sq_abs, mul_pow, Real.sq_sqrt v.coe_nonneg] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg u) (by linarith : |u| ≤ 1 + |u|) 2) v.coe_nonneg)
  calc
    variance X μ = variance (fun u => X u - M x) μ :=
      (variance_sub_const hmX.aestronglyMeasurable (M x)).symm
    _ ≤ ∫ u, (X u - M x)^2 ∂μ := variance_le_expectation_sq hmD
    _ ≤ ∫ u, (v : ℝ) * (1 + |u|)^2 ∂μ := integral_mono hLp.integrable_sq (hi.const_mul _) hp
    _ = (v : ℝ) * ∫ u, (1 + |u|)^2 ∂μ := integral_const_mul _ _
    _ ≤ (v : ℝ) * fieldGaussianMomentCap C := mul_le_mul_of_nonneg_left hb v.coe_nonneg

lemma fieldSpinTransition_centered_standard (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M) (x : ℝ) :
    fieldSpinTransition ζ v F M x =
      ∫ u, M (x + Real.sqrt (v : ℝ) * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)) := by
  rw [fieldSpinTransition_eq_standard ζ v hF hM, gaussianTiltAverage_eq_div,
    integral_tilted_eq_div]
  simp_rw [mul_sub, Real.exp_sub, div_mul_eq_mul_div]
  rw [integral_div, integral_div, div_div_div_cancel_right₀ (Real.exp_ne_zero _)]

lemma fieldSpinTransition_variance_bound (ζ : ℝ) (v : ℝ≥0) {F M : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M)
    (hMb : ∀ z, |M z| ≤ 1) (hML : ∀ x y, |M x - M y| ≤ |x - y|)
    (x : ℝ) {C : ℝ}
    (hUb : ∀ u, |ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)| ≤ C * |u|) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
        (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap C := by
  let U := fun u => ζ * (F (x + Real.sqrt (v : ℝ) * u) - F x)
  have hU : Measurable U := by dsimp only [U]; fun_prop
  have he : Integrable (fun u => Real.exp (U u)) (gaussianReal 0 1) := by
    apply (gaussianReal_exponentialNormMoments 0 1 C).mono' hU.exp.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hUb u))
  let μ := (gaussianReal 0 1).tilted U
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted he
  have hm : Measurable (fun u => M (x + Real.sqrt (v : ℝ) * u)) := hM.comp (by fun_prop)
  have hLp : MemLp (fun u => M (x + Real.sqrt (v : ℝ) * u)) 2 μ :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun u => by
      simpa only [Real.norm_eq_abs] using hMb (x + Real.sqrt (v : ℝ) * u))
  rw [fieldSpinTransition_centered_standard ζ v hF (hM.pow_const 2),
    fieldSpinTransition_centered_standard ζ v hF hM]
  change (∫ u, (M (x + Real.sqrt (v : ℝ) * u))^2 ∂μ) -
    (∫ u, M (x + Real.sqrt (v : ℝ) * u) ∂μ)^2 ≤ _
  have heq := variance_eq_sub hLp
  simp only [Pi.pow_apply] at heq
  rw [← heq]
  exact field_centered_spin_variance hU hM hMb hML hUb x v

lemma fieldSpinTransition_variance_le (ζ : ℝ) (hζ : ζ ∈ Icc 0 1) (v : ℝ≥0)
    {V : ℝ} (hv : (v : ℝ) ≤ V) {F M : ℝ → ℝ}
    (hF : Measurable F) (hFL : ∀ x y, |F x - F y| ≤ |x - y|)
    (hM : Measurable M) (hMb : ∀ z, |M z| ≤ 1)
    (hML : ∀ x y, |M x - M y| ≤ |x - y|) (x : ℝ) :
    fieldSpinTransition ζ v F (fun z => (M z)^2) x -
      (fieldSpinTransition ζ v F M x)^2 ≤ (v : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  apply fieldSpinTransition_variance_bound ζ v hF hM hMb hML x
  intro u
  rw [abs_mul, abs_of_nonneg hζ.1]
  have hf : |F (x + Real.sqrt (v : ℝ) * u) - F x| ≤ Real.sqrt V * |u| := by
    have hh := hFL (x + Real.sqrt (v : ℝ) * u) x
    simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv) (abs_nonneg u))
  exact (mul_le_mul_of_nonneg_left hf hζ.1).trans
    (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hζ.2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCurvatureLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive exponential lower bound for the actual finite-step curvature.
The constant depends only on the finite covariance data, not on the bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCosh_lipschitz (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (x y : ℝ) :
    |fieldScalarValue L (fun z => Real.log (Real.cosh z)) x -
      fieldScalarValue L (fun z => Real.log (Real.cosh z)) y| ≤ |x - y| := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hb := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_fieldScalarLogCosh L hL z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hb.2 z)
      convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldOverlapIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional overlap increments are bounded by their variance
increments, uniformly in all preceding scalar-field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_sub (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u - b u) z =
      fieldSpinTransition ζ v F a z - fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  let : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    isProbabilityMeasure_tilted he
  exact integral_sub
    (Integrable.of_bound ha.aestronglyMeasurable A
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hbB u))

theorem fieldScalarSquares_increment_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1)
    {V : ℝ} (hV : ∀ av ∈ L, (av.2 : ℝ) ≤ V) (i : Fin L.length) (z : ℝ) :
    fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.succ z -
      fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.castSucc z ≤
        ((L.get i).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  induction L generalizing z with
  | nil => exact Fin.elim0 i
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have htV := fun bv hb => hV bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hmean := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    have hreg := fieldScalarSquares_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    refine Fin.cases ?_ (fun j => ?_) i
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0) z -
        (fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh) z)^2 ≤ _
      have hzero : fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0 =
          fun y => (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y)^2 := by
        funext y
        exact fieldScalarSquares_zero _ _ _ _
      rw [hzero]
      exact fieldSpinTransition_variance_le av.1
        ⟨(hL av List.mem_cons_self).le, hζ av List.mem_cons_self⟩ av.2
        (hV av List.mem_cons_self) hval.1 (fieldScalarLogCosh_lipschitz L ht)
        hmean.1 hmean.2 (fieldScalarLogCoshMean_dist_le L ht htζ) z
    · have hb (j : Fin (L.length + 1)) (u : ℝ) :
          |fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j u| ≤ 1 := by
        rw [abs_of_nonneg ((hreg j).2 u).1]
        exact ((hreg j).2 u).2
      change fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.succ) z -
        fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.castSucc) z ≤ _
      rw [← fieldSpinTransition_sub av.1 av.2 hval.1 hval.2
        (hreg j.succ).1 (hreg j.castSucc).1 (hb j.succ) (hb j.castSucc)]
      calc
        _ ≤ fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
            (fun _ => ((L.get j).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V)) z :=
          fieldSpinTransition_mono_test av.1 av.2 _
            ((hreg j.succ).1.sub (hreg j.castSucc).1) measurable_const
            (fun u => (abs_sub _ _).trans (add_le_add (hb j.succ u) (hb j.castSucc u)))
            (fun _ => le_rfl) (fun u => ih ht htζ htV j u) z
        _ = _ := fieldSpinTransition_const av.1 av.2 hval.1 hval.2 _ z

theorem fieldScalarOverlaps_increment_le (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1)
    {V : ℝ} (hV : ∀ av ∈ L, (av.2 : ℝ) ≤ V) (i : Fin L.length) :
    fieldScalarOverlaps L root (fun z => Real.log (Real.cosh z)) Real.tanh i.succ -
      fieldScalarOverlaps L root (fun z => Real.log (Real.cosh z)) Real.tanh i.castSucc ≤
        ((L.get i).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hreg := fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    ht field_abs_tanh_le_one
  have hi (j : Fin (L.length + 1)) : Integrable
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j)
      (gaussianReal 0 root) := by
    apply Integrable.of_bound (hreg j).1.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hreg j).2 z).1]
      exact ((hreg j).2 z).2
  unfold fieldScalarOverlaps
  rw [← integral_sub (hi i.succ) (hi i.castSucc)]
  have hb := integral_mono ((hi i.succ).sub (hi i.castSucc)) (integrable_const _)
    (fieldScalarSquares_increment_le L hL hζ hV i)
  simpa only [integral_const, probReal_univ, one_smul, Pi.sub_apply] using hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMagnetizationModulus
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform modulus for the actual finite-field magnetization levels.
Small height gaps force small overlap gaps, including near tied levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldMagnetizationLevel_increment_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i : Fin h.depth) :
    fieldMagnetizationLevel h i.succ - fieldMagnetizationLevel h i.castSucc ≤
      (h.height i.succ - h.height i.castSucc) * fieldGaussianMomentCap (Real.sqrt V) := by
  let L := scalarFieldIncrements h
  let j : Fin L.length := Fin.cast (scalarFieldIncrements_length h).symm i
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ L, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut k.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hvar : ∀ av ∈ L, (av.2 : ℝ) ≤ V := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    exact (fieldIncrement_le_last h k.succ).trans hV
  have hb := fieldScalarOverlaps_increment_le L (NNReal.mk (h.height 0) (h.nonneg 0))
    hL hζ hvar j
  have hget : ((L.get j).2 : ℝ) = h.height i.succ - h.height i.castSucc := by
    have hg : L.get j = ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
      exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
        NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) j
    rw [hg]
    change (fieldIncrement h i.succ).2 = _
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
    rfl
  rw [hget] at hb
  change fieldScalarOverlaps L _ _ _ _ - fieldScalarOverlaps L _ _ _ _ ≤ _
  convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)

theorem fieldMagnetizationLevel_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V)
    (i j : Fin (h.depth + 1)) (hij : i ≤ j) :
    fieldMagnetizationLevel h j - fieldMagnetizationLevel h i ≤
      (h.height j - h.height i) * fieldGaussianMomentCap (Real.sqrt V) := by
  have hm : Monotone (fun i => h.height i * fieldGaussianMomentCap (Real.sqrt V) -
      fieldMagnetizationLevel h i) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have hk := fieldMagnetizationLevel_increment_le h hV k
    nlinarith
  have hh := hm hij
  nlinarith

theorem fieldMagnetizationLevel_abs_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i j : Fin (h.depth + 1)) :
    |fieldMagnetizationLevel h i - fieldMagnetizationLevel h j| ≤
      |h.height i - h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (fieldMagnetizationLevel_monotone h hij)), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr (h.ordered_height hij)), neg_sub]
    exact fieldMagnetizationLevel_sub_le h hV i j hij
  · rw [abs_of_nonneg (sub_nonneg.mpr (fieldMagnetizationLevel_monotone h hji)),
      abs_of_nonneg (sub_nonneg.mpr (h.ordered_height hji))]
    exact fieldMagnetizationLevel_sub_le h hV j i hji

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFieldModulus
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform plateau control for the actual strict finite cavity fields.
The spectral derivative bound and the conditional-variance estimate
turn convergence of overlap levels into asymptotic preservation of ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFieldPrimitive_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (s t : ℝ) :
    |cavityFieldPrimitive rho lam hrho hsum p s -
      cavityFieldPrimitive rho lam hrho hsum p t| ≤ 4 * K^2 * |s - t| := by
  rw [cavityFieldPrimitive_sub]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 4 * K^2)
    (f := cavityFieldDensity rho lam hrho hsum p) (fun u _ => by
      dsimp only [cavityFieldDensity]
      rw [Real.norm_eq_abs, abs_of_nonneg (cavityRDerivative_nonneg rho lam hrho hsum _)]
      exact cavityRDerivative_le rho lam hrho hsum hK hlam _)
  simpa only [Real.norm_eq_abs] using hb

lemma cavityStrictUniformField_height_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    (cavityStrictUniformField rho lam hrho hsum p n).height i ≤ 4 * K^2 := by
  have hb := cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) (cavityStrictUniformLevels p n i) 0
  have hq := cavityStrictUniformLevels_mem p n i
  have hp0 : cavityFieldPrimitive rho lam hrho hsum (cavityStrictUniformPath p n) 0 = 0 := by
    simp only [cavityFieldPrimitive, intervalIntegral.integral_same]
  rw [hp0, sub_zero, abs_of_nonneg (cavityFieldPrimitive_nonneg _ _ _ _ _ hq.1.le),
    sub_zero, abs_of_pos hq.1] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity) hq.2.le)

lemma cavityStrictUniformField_magnetization_dist_le {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (p : OverlapPath) (n : ℕ) (i j : Fin (n + 1)) :
    |fieldMagnetizationLevel (cavityStrictUniformField rho lam hrho hsum p n) i -
      fieldMagnetizationLevel (cavityStrictUniformField rho lam hrho hsum p n) j| ≤
      (4 * K^2 * |cavityStrictUniformLevels p n i - cavityStrictUniformLevels p n j|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2)) := by
  have hb := fieldMagnetizationLevel_abs_sub_le
    (cavityStrictUniformField rho lam hrho hsum p n)
    (cavityStrictUniformField_height_le rho lam hrho hsum hK hlam p n (Fin.last n)) i j
  refine hb.trans (mul_le_mul_of_nonneg_right ?_
    (fieldGaussianMomentCap_nonneg (Real.sqrt_nonneg _)))
  exact cavityFieldPrimitive_dist_le rho lam hrho hsum hK hlam
    (cavityStrictUniformPath p n) _ _

theorem cavity_strict_field_asymptotic_ties {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K) (p : OverlapPath) :
    ∃ D : Set ℝ, (∀ᵐ s ∂pathMeasure, s ∈ D) ∧
      ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
        Tendsto (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) x -
          fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) y) atTop (𝓝 0) := by
  let D := {s | Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) ∧
    ∀ n, ∃ i : Fin (n + 1), s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)}
  have hD : ∀ᵐ s ∂pathMeasure, s ∈ D := by
    filter_upwards [cavityStrictUniformPath_ae_tendsto p,
      ae_all_iff.mpr (fun n => ae_finite_overlap_cell (uniformCut n)
        (uniformCut_zero n) (uniformCut_last n))] with s hs hc
    exact ⟨hs, hc⟩
  refine ⟨D, hD, ?_⟩
  intro x hx y hy hxy
  have hlim : Tendsto (fun n =>
      (4 * K^2 * |cavityStrictUniformPath p n x - cavityStrictUniformPath p n y|) *
        fieldGaussianMomentCap (Real.sqrt (4 * K^2))) atTop (𝓝 0) := by
    have hh := ((hx.1.sub hy.1).abs.const_mul (4 * K^2)).mul_const
      (fieldGaussianMomentCap (Real.sqrt (4 * K^2)))
    simpa only [hxy, sub_self, abs_zero, mul_zero, zero_mul] using hh
  apply squeeze_zero_norm (fun n => ?_) hlim
  obtain ⟨i, hi⟩ := hx.2 n
  obtain ⟨j, hj⟩ := hy.2 n
  rw [Real.norm_eq_abs,
    fieldMagnetizationPath_on_cell (cavityStrictUniformField rho lam hrho hsum p n) i hi,
    fieldMagnetizationPath_on_cell (cavityStrictUniformField rho lam hrho hsum p n) j hj,
    cavityStrictUniformPath_on_cell p n i hi, cavityStrictUniformPath_on_cell p n j hj]
  exact cavityStrictUniformField_magnetization_dist_le rho lam hrho hsum hK hlam p n i j

theorem cavity_strict_field_self_consistency {m : ℕ} (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K) (p : OverlapPath)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun n =>
      ∫ s, Φ (cavityStrictUniformPath p n s) *
        (fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) s -
          cavityStrictUniformPath p n s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s,
      |fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n) s - p s|
        ∂pathMeasure) atTop (𝓝 0) := by
  obtain ⟨D, hD, htied⟩ := cavity_strict_field_asymptotic_ties rho lam hrho hsum hK hlam p
  apply cavity_self_consistency_asymptotic_l1_on p
    (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n)) D hD htied
  intro Φ
  have hh := (cavity_rounding_test_difference p (cavityStrictUniformPath p)
    (fun n => fieldMagnetizationPath (cavityStrictUniformField rho lam hrho hsum p n))
    (cavityStrictUniformPath_ae_tendsto p) Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-test comparison for the two-replica law used in the
cavity overlap argument. Both replicas share the same Gaussian field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_twoReplica_mean_eq {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (A : X → ℕ →₀ ℝ)
    (F : (Fin 2 → X) → ℝ) (g : ℕ → ℝ) :
    referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F =
      ∫ σ, F σ ∂(Measure.pi (fun _ : Fin 2 => ν)).tilted
        (fun σ => (∑ i, H (σ i)) + cylinderField (∑ i, A (σ i)) g) := by
  rw [referenceReplicaMean_eq_ratio, integral_tilted_eq_div]
  have he (σ : Fin 2 → X) :
      (∑ i, (H (σ i) + cylinderField (A (σ i)) g)) =
        (∑ i, H (σ i)) + cylinderField (∑ i, A (σ i)) g := by
    rw [cylinderField_finset_sum, Finset.sum_add_distrib]
  simp_rw [he]

lemma cavity_twoReplica_sum_bound {X : Type*} (H : X → ℝ) {M : ℝ}
    (hH : ∀ x, |H x| ≤ M) (σ : Fin 2 → X) : |∑ i, H (σ i)| ≤ 2 * M := by
  rw [Fin.sum_univ_two]
  exact (abs_add_le _ _).trans (by linarith [hH (σ 0), hH (σ 1)])


lemma cavity_twoReplica_covariance_bound {X : Type*}
    (C A : X → ℕ →₀ ℝ) {K : ℝ}
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (σ τ : Fin 2 → X) :
    |cylinderCross (∑ i, A (σ i)) (∑ i, A (τ i)) -
      cylinderCross (∑ i, C (σ i)) (∑ i, C (τ i))| ≤ 4 * K := by
  simp only [cylinderCross_finset_left, cylinderCross_sum_right]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin 2, |∑ j : Fin 2,
        (cylinderCross (A (σ i)) (A (τ j)) - cylinderCross (C (σ i)) (C (τ j)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
        |(cylinderCross (A (σ i)) (A (τ j)) - cylinderCross (C (σ i)) (C (τ j)))| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, K :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov (σ i) (τ j)))
    _ = 4 * K := by simp <;> ring

theorem cavity_twoReplica_test_comparison {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) (F : (Fin 2 → X) → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B)
    (hF : ∀ σ, |F σ| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, referenceReplicaMean ν
        (fun x => H x + cylinderField (C x) g) F ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, referenceReplicaMean ν
        (fun x => J x + cylinderField (A x) g) F ∂gaussianCoordinates| ≤
      (16 * K + 4 * E) / s + B ^ 2 * s / 2 := by
  have hcv (σ : Fin 2 → X) : (∑ i, C (σ i)).sum (fun _ z => z ^ 2) ≤ 4 * B₀ := by
    have hh := cylinder_variance_sum_le (fun i : Fin 2 => C (σ i)) (fun i => hC (σ i))
    norm_num at hh
    simpa only [Fin.sum_univ_two] using hh
  have hav (σ : Fin 2 → X) : (∑ i, A (σ i)).sum (fun _ z => z ^ 2) ≤ 4 * B₁ := by
    have hh := cylinder_variance_sum_le (fun i : Fin 2 => A (σ i)) (fun i => hA (σ i))
    norm_num at hh
    simpa only [Fin.sum_univ_two] using hh
  have hb (σ : Fin 2 → X) : |(∑ i, H (σ i)) - ∑ i, J (σ i)| ≤ 2 * E := by
    rw [← Finset.sum_sub_distrib]
    exact cavity_twoReplica_sum_bound (fun x => H x - J x) hbase σ
  have ht := cavity_countable_test_comparison (Measure.pi (fun _ : Fin 2 => ν))
    (fun σ => ∑ i, H (σ i)) (fun σ => ∑ i, J (σ i)) F
    (cavity_twoReplica_sum_bound H hH) (cavity_twoReplica_sum_bound J hJ)
    (fun σ => ∑ i, C (σ i)) (fun σ => ∑ i, A (σ i)) hcv hav
    (show 0 ≤ 4 * K by positivity) (cavity_twoReplica_covariance_bound C A hcov)
    hb hB hF hs
  simp_rw [← cavity_twoReplica_mean_eq] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianTestLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded Gibbs replica test depends on a centered Gaussian field
only through its covariance, including for the countable leaf prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_twoReplica_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (F : (Fin 2 → X) → ℝ) {M B₀ B₁ B : ℝ}
    (hH : ∀ x, |H x| ≤ M) (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y))
    (hB : 0 ≤ B) (hF : ∀ σ, |F σ| ≤ B) :
    (∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (C x) g) F
      ∂gaussianCoordinates) =
    ∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (A x) g) F
      ∂gaussianCoordinates := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let s := ε / (B ^ 2 + 1)
  have hs : 0 < s := div_pos hε (by positivity)
  have ht := cavity_twoReplica_test_comparison ν H H F hH hH C A hC hA
    (show (0 : ℝ) ≤ 0 from le_rfl)
    (fun x y => by rw [hcov x y]; simp)
    (by intro x; simp : ∀ x, |H x - H x| ≤ (0 : ℝ)) hB hF hs
  have he : s * (B ^ 2 + 1) = ε := div_mul_cancel₀ _ (by positivity)
  simp only [mul_zero, add_zero, zero_div, zero_add] at ht ⊢
  exact ht.trans (by nlinarith [sq_nonneg B])

/-- Pull back both the energy and the test by a prior-preserving
configuration map. This retains the common Gaussian disorder. -/
theorem cavity_twoReplica_gaussian_transport {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (e : X → X)
    (he : MeasurePreserving e ν ν) (H : X → ℝ) (hH : Measurable H)
    (C : X → ℕ →₀ ℝ) (hC : ∀ g, Measurable (fun x => cylinderField (C x) g))
    (F : (Fin 2 → X) → ℝ) (hF : Measurable F) :
    (∫ g, referenceReplicaMean ν
      (fun x => H (e x) + cylinderField (C (e x)) g)
      (fun σ => F (fun i => e (σ i))) ∂gaussianCoordinates) =
    ∫ g, referenceReplicaMean ν (fun x => H x + cylinderField (C x) g) F
      ∂gaussianCoordinates := by
  apply integral_congr_ae
  exact ae_of_all _ fun g => referenceReplicaMean_map he (hH.add (hC g)) hF

/-- A symmetry of the deterministic energy and Gaussian covariance,
combined with invariance of the disorder and the prior, gives the full
annealed replica-test symmetry. -/
theorem cavity_twoReplica_ensemble_symmetry {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X]
    (μ : Measure Ω) (R : Ω → Ω) (hR : MeasurePreserving R μ μ)
    (ν : Measure X) [IsProbabilityMeasure ν]
    (e : X → X) (he : MeasurePreserving e ν ν)
    (H : Ω → X → ℝ) (C : Ω → X → ℕ →₀ ℝ)
    (M V : Ω → ℝ) (hH : ∀ ω x, |H ω x| ≤ M ω)
    (hV : ∀ ω x, (C ω x).sum (fun _ z => z ^ 2) ≤ V ω)
    (henergy : ∀ ω x, H (R ω) (e x) = H ω x)
    (hcov : ∀ ω x y, cylinderCross (C (R ω) (e x)) (C (R ω) (e y)) =
      cylinderCross (C ω x) (C ω y))
    (F : (Fin 2 → X) → ℝ) (hFm : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B)
    (hmeas : AEStronglyMeasurable (fun ω => ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) F ∂gaussianCoordinates) μ) :
    (∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) F ∂gaussianCoordinates ∂μ) =
    ∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g)
      (fun σ => F (fun i => e (σ i))) ∂gaussianCoordinates ∂μ := by
  rw [← hR.hasLaw.integral_comp hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only [Function.comp_apply]
    have ht := cavity_twoReplica_gaussian_transport ν e he (H (R ω)) (measurable_of_countable _)
      (C (R ω)) (fun _ => measurable_of_countable _) F hFm
    simp_rw [henergy] at ht
    rw [← ht]
    exact (cavity_twoReplica_same_covariance ν (H ω)
      (fun σ => F (fun i => e (σ i))) (hH ω) (C ω) (fun x => C (R ω) (e x))
      (hV ω) (fun x => hV (R ω) (e x)) (hcov ω) hB
      (fun σ => hFb (fun i => e (σ i)))).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinIsometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.rotationMatrix_specialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed site permutations act on the actual Ising cube and its
projected overlaps. Their pair-spin observables have no sign factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavitySignedSpinPermutation_pair {N : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) (σ τ : Spin N) (i : Fin N) :
    spinValue (cavitySignedSpinPermutation p flip σ i) *
      spinValue (cavitySignedSpinPermutation p flip τ i) =
        spinValue (σ (p i)) * spinValue (τ (p i)) := by
  change spinValue (if flip i then _ else _) * spinValue (if flip i then _ else _) = _
  cases h : flip i <;> simp_all

lemma cavityPermutationSpin_vector {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (σ : Spin N) :
    spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ) =
      specialRotation (spectralPermutation hN p) (spinVector σ) := by
  ext i
  change spinValue (if cavityPermutationFlip hN p i then !(σ (p i)) else σ (p i)) =
    ((permutationSignDiagonal hN p * p.permMatrix ℝ) *ᵥ (spinVector σ).ofLp) i
  rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  simp only [permutationSignDiagonal, Matrix.mulVec_diagonal, Function.comp_apply,
    spinVector_apply]
  have hd := orthogonal_det_eq_one_or_neg_one
    (⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩ : Orthogonal N)
  rcases hd with hd | hd <;> change (p.permMatrix ℝ).det = _ at hd
  · norm_num [cavityPermutationFlip, hd]
  · by_cases hi : i = (⟨0, hN⟩ : Fin N) <;> simp [cavityPermutationFlip, hd, hi]

lemma cavity_specialRotation_mul_apply {N : ℕ} (U V : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) :
    specialRotation (U * V) x = specialRotation U (specialRotation V x) := by
  ext i
  change (((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x.ofLp) i =
    ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ ((V : Matrix (Fin N) (Fin N) ℝ) *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma cavityPermutationSpin_cancel {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (σ : Spin N) :
    specialRotation (U * (spectralPermutation hN p)⁻¹)
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) =
        specialRotation U (spinVector σ) := by
  rw [cavityPermutationSpin_vector, ← cavity_specialRotation_mul_apply]
  simp only [inv_mul_cancel_right]

lemma projectedOverlap_cavityPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) τ) =
        projectedOverlap (specialRotation U) I σ τ := by
  simp only [projectedOverlap, cavityPermutationSpin_cancel]

lemma rotatedEnergy_cavityPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (eig : Fin N → ℝ) (U : SpecialOrthogonal N) (σ : Spin N) :
    rotatedEnergy eig (specialRotation (U * (spectralPermutation hN p)⁻¹))
      (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ) =
        rotatedEnergy eig (specialRotation U) σ := by
  simp only [rotatedEnergy, cavityPermutationSpin_cancel]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prior symmetries for the signed-site action. The cascade
leaf coordinate stays fixed and retains its original random prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma uniformSpinPrior_equiv {N : ℕ} (e : Equiv.Perm (Spin N)) :
    MeasurePreserving e (uniformSpinPrior N : Measure (Spin N))
      (uniformSpinPrior N : Measure (Spin N)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro σ
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton σ)]
  have hp : e ⁻¹' {σ} = {e.symm σ} := by
    ext τ
    exact e.eq_symm_apply.symm
  rw [hp]
  change (PMF.uniformOfFintype (Spin N)).toMeasure {e.symm σ} =
    (PMF.uniformOfFintype (Spin N)).toMeasure {σ}
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

lemma labeledSpinReference_equiv {N depth : ℕ} (e : Equiv.Perm (Spin N))
    (T : LabeledTree depth) :
    MeasurePreserving (fun x : Spin N × LabeledLeaf depth => (e x.1, x.2))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  exact (uniformSpinPrior_equiv e).prod (MeasurePreserving.id _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite Ising model with its actual spectral/tree tensor
perturbation has signed site-permutation symmetry after Haar averaging. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavityPerturbationField {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2) := by
  simp only [cavityPerturbationCoefficients, tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_spinTensorFeature I _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

theorem cavity_full_signed_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N)) (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ, |F σ| ≤ B) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    (∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g) F
      ∂gaussianCoordinates ∂μ) =
    ∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (fun σ => F (fun i =>
        (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) (σ i).1, (σ i).2)))
      ∂gaussianCoordinates ∂μ := by
  dsimp only
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hHm : Measurable (fun z : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) => H z.1.1 z.2 + cylinderField (C z.1.1 z.2) z.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => H U x) := by
      unfold H rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
    exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) F ∂gaussianCoordinates) :=
    (measurable_referenceReplicaMean ν hHm
      ((measurable_of_countable F).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_ensemble_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (labeledSpinReference_equiv e T) H C
    (fun U => ∑ σ : Spin N, |rotatedEnergy eig (specialRotation U) σ|)
    (fun _ => 4 * (N * perturbationScale N ^ 2))
  · intro U x
    exact Finset.single_le_sum
      (f := fun σ : Spin N => |rotatedEnergy eig (specialRotation U) σ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)
  · intro U x
    exact cavityPerturbationCoefficients_sq_le _ I u hu x
  · intro U x
    exact rotatedEnergy_cavityPermutation hN p eig U x.1
  · intro U x y
    simp only [C, e, cavityPerturbationCoefficients_cross, cavityWeightedKernel,
      cavityPerturbationKernel, projectedOverlap_cavityPermutation]
  · exact measurable_of_countable F
  · exact hB
  · exact hF
  · exact hmean.aestronglyMeasurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear combinations of bounded replica tests commute with
the normalized Gibbs average, including a zero denominator. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_referenceReplicaMean_sum {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ}
    (F : ι → (Fin r → X) → ℝ) (hF : ∀ i, Measurable (F i))
    (B : ι → ℝ) (hB : ∀ i σ, |F i σ| ≤ B i) :
    referenceReplicaMean ν H (fun σ => ∑ i, F i σ) =
      ∑ i, referenceReplicaMean ν H (F i) := by
  simp only [referenceReplicaMean_eq_ratio]
  by_cases hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ => ν))
  · have hip (i : ι) : Integrable
        (fun σ : Fin r → X => Real.exp (∑ j, H (σ j)) * F i σ)
        (Measure.pi (fun _ => ν)) := by
      apply (hi.mul_const (B i)).mono'
        ((hi.aestronglyMeasurable.mul (hF i).aestronglyMeasurable))
      exact ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hB i σ) (Real.exp_pos _).le
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => hip i), Finset.sum_div]
  · simp only [integral_undef hi, div_zero, Finset.sum_const_zero]

lemma cavity_nested_replica_sum {Ω Ω' X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : ι → (Fin r → X) → ℝ) (hmF : ∀ i, Measurable (F i))
    (hmeas : ∀ i, Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i σ, |F i σ| ≤ B) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i σ) ∂P ∂μ) =
      ∑ i, ∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P ∂μ := by
  have hiG (ω : Ω) (i : ι) :
      Integrable (fun g => referenceReplicaMean ν (H ω g) (F i)) P :=
    integrable_of_measurable_abs_le ((hmeas i).comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i) (hmF i) hB (hF i))
  have he (ω : Ω) :
      (∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i σ) ∂P) =
        ∑ i, ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P := by
    simp_rw [cavity_referenceReplicaMean_sum ν _ F hmF (fun _ => B) hF]
    exact integral_finsetSum _ (fun i _ => hiG ω i)
  have hiU (i : ι) : Integrable
      (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P) μ :=
    integrable_of_measurable_abs_le
      ((hmeas i).stronglyMeasurable.integral_prod_right'.measurable)
      (fun ω => abs_integral_le_const_of_bound ((hmeas i).comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i) (hmF i) hB (hF i)))
  simp_rw [he]
  exact integral_finsetSum _ (fun i _ => hiU i)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSiteIdentity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cavity-spin insertion identity for the actual full perturbed
model, before any restriction of its Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityFullInner {N m depth : ℕ} (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2) F) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
  let H : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) → ℝ :=
    fun z => rotatedEnergy eig (specialRotation z.1.1) z.2.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation z.1.1) I u depth z.2) z.1.2
  have hmH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
    exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) F)
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.2)
    hmH ((measurable_of_countable F).comp measurable_snd)

lemma cavityFullTest_sum {N m depth : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i σ, |F i σ| ≤ B) :
    cavityFullTest μ T eig I u (fun σ => ∑ i, F i σ) =
      ∑ i, cavityFullTest μ T eig I u (F i) := by
  exact cavity_nested_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _) (fun i => measurable_cavityFullInner T eig I u (F i)) hB hF

lemma cavityFullTest_const_mul {N m depth : ℕ} (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    cavityFullTest μ T eig I u (fun σ => c * F σ) = c * cavityFullTest μ T eig I u F := by
  simp only [cavityFullTest, referenceReplicaMean_const_mul, integral_const_mul]

lemma cavityReplicaOverlap_signed {N depth : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    cavityReplicaOverlap (fun i => (cavitySignedSpinPermutation p flip (σ i).1, (σ i).2)) =
      cavityReplicaOverlap σ := by
  unfold cavityReplicaOverlap cavityTotalSpinOverlap
  simp only [cavitySignedSpinPermutation_pair]
  congr 1
  exact Equiv.sum_comp p (fun i => spinValue ((σ 0).1 i) * spinValue ((σ 1).1 i))

theorem cavity_full_site_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (j : Fin N) :
    cavityFullTest μ T eig I u
      (fun σ => Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 j) * spinValue ((σ 1).1 j)) =
    cavityFullTest μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) := by
  let F := fun i (σ : Fin 2 → Spin N × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 i) * spinValue ((σ 1).1 i)
  let a := fun i => cavityFullTest μ T eig I u (F i)
  have hF (i : Fin N) (σ) : |F i σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have he (i : Fin N) : a i = a j := by
    have h := cavity_full_signed_site_symmetry hN μ T eig I u hu (Equiv.swap i j)
      (F i) (norm_nonneg _) (hF i)
    change a i = cavityFullTest μ T eig I u _ at h
    rw [show (fun σ => F i (fun k =>
        (cavitySignedSpinPermutation (Equiv.swap i j) (cavityPermutationFlip hN (Equiv.swap i j))
          (σ k).1, (σ k).2))) = F j from ?_] at h
    · exact h
    · funext σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        Equiv.swap_apply_left]
      ring
  have htotal : (fun σ : Fin 2 → Spin N × LabeledLeaf depth =>
      Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) =
      (fun σ => (N : ℝ)⁻¹ * ∑ i, F i σ) := by
    funext σ
    simp only [F, cavityReplicaOverlap, cavityTotalSpinOverlap, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htotal, cavityFullTest_const_mul,
    cavityFullTest_sum μ T eig I u F (norm_nonneg _) hF]
  change a j = (N : ℝ)⁻¹ * ∑ i, a i
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOrientation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityOrientationLift_right {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (V : SpecialOrthogonal N) :
    cavityOrientationLift hN (U * cavitySpecialOrthogonal V) = cavityOrientationLift hN U * V := by
  apply Subtype.ext
  have hd : ((cavitySpecialOrthogonal V : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ).det = 1 :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp V.property).2
  have hs : cavityOrientationSign hN (U * cavitySpecialOrthogonal V) = cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Submonoid.coe_mul, Matrix.det_mul, hd, mul_one]
  change cavityOrientationSign hN (U * cavitySpecialOrthogonal V) *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) =
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [hs, Matrix.mul_assoc]

lemma cavityOrientationLift_measure_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [μ.IsMulRightInvariant] :
    (μ.map (cavityOrientationLift hN)).IsMulRightInvariant := by
  constructor
  intro V
  rw [Measure.map_map (measurable_mul_const V) (measurable_cavityOrientationLift hN)]
  have he : (fun S : SpecialOrthogonal N => S * V) ∘ cavityOrientationLift hN =
      cavityOrientationLift hN ∘ (fun U => U * cavitySpecialOrthogonal V) := by
    funext U
    exact (cavityOrientationLift_right hN U V).symm
  rw [he, ← Measure.map_map (measurable_cavityOrientationLift hN)
    (measurable_mul_const (cavitySpecialOrthogonal V)), map_mul_right_eq_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpinSplitOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing finitely many cavity sites changes the ordinary spin
overlap by at most twice their fraction of the system. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma abs_cavityTotalSpinOverlap_le {N : ℕ} (x : Spin N × Spin N) :
    |cavityTotalSpinOverlap x| ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    unfold cavityTotalSpinOverlap
    rw [abs_mul,abs_of_pos (inv_pos.mpr hNpos)]
    calc
      _ ≤ (N:ℝ)⁻¹ * ∑ i, |spinValue (x.1 i) * spinValue (x.2 i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hNpos).le
      _ = (N:ℝ)⁻¹ * N := by simp only [abs_mul,abs_spinValue,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      _ = 1 := inv_mul_cancel₀ hNpos.ne'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySplitTreeSpinTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Site symmetry and the vanishing omitted-site error survive averaging
with the actual, system-size dependent cascade tree law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_full_tree_site_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (site : Fin N) :
    (∫ T, cavityFullTest μ T eig I u (cavityFullSpinInsertion Φ site) ∂θ) =
      ∫ T, cavityFullTest μ T eig I u
        (fun σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ) ∂θ := by
  apply integral_congr_ae
  filter_upwards [] with T
  unfold cavityFullSpinInsertion
  simpa only [mul_assoc] using
    cavity_full_site_identity hN μ T eig I u hu Φ site

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapWeightedTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded continuous extension of the overlap-weighted test from
[-1,1], for the full original-model self-consistency identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BoundedContinuousFunction

namespace InvariantIsing

lemma cavityOverlapWeightedTest_eq (Φ : ℝ →ᵇ ℝ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    cavityOverlapWeightedTest Φ x = Φ x * x := by
  simp only [cavityOverlapWeightedTest,BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hx]

lemma cavity_full_weighted_overlap_identity {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (site : Fin N) :
    (∫ T, cavityFullTest μ T eig I u (cavityFullSpinInsertion Φ site) ∂θ) =
      ∫ T, cavityFullTest μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ)) ∂θ := by
  rw [cavity_full_tree_site_identity hN μ θ eig I u hu Φ site]
  congr 1
  funext T
  congr 1
  funext σ
  exact (cavityOverlapWeightedTest_eq Φ
    (abs_le.mp (abs_cavityTotalSpinOverlap_le ((σ 0).1,(σ 1).1)))).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOriginalSelfConsistency
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cavity self-consistency for the actual original-model spin law,
conditional on the published inputs and the proved geometric/GG limit data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_original_scalar_self_consistency_oai (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A_ : CavityFactorBlocks d n)
    (hA : A_ = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A_}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => cavityRotationArrayLaw (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r => ∫ s,
      |fieldMagnetizationPath (cavityStrictUniformField ρ lam hρ hρsum p r) s-p s| ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hKl a : |lam a| ≤ K := Finset.single_le_sum (fun b _ => abs_nonneg (lam b)) (Finset.mem_univ a)
  apply cavity_strict_field_self_consistency ρ lam hρ hρsum hK hKl p
  intro Φ
  let site : Fin n := ⟨0,hn⟩
  let Ψ := cavityOverlapWeightedTest Φ
  let μO := fun r => (μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))
  let (r : ℕ) : IsProbabilityMeasure (μO r) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cavityOrientationLift _).aemeasurable).mpr inferInstance
  let (r : ℕ) : (μO r).IsMulRightInvariant := cavityOrientationLift_measure_rightInvariant _ _
  let eig := fun r => diagonalPerturbedEigenvalues (fun i => lam (g r i))
    (cavitySpectralGroup (g r)) (v r) 1
  let q := cavityStrictUniformPath p
  let f := fun r => fieldMagnetizationPath (cavityStrictUniformField ρ lam hρ hρsum p r)
  let G := fun r => ∫ T, cavityFullTest (μO r) T (eig r) (cavitySpectralGroup (g r)) (u r)
    (cavityFullSpinInsertion Φ (Fin.natAdd (N r) site)) ∂θ r
  let A := fun r => ∫ t, Φ (q r t) * f r t ∂pathMeasure
  let C := fun r => ∫ t, Φ (q r t) * q r t ∂pathMeasure
  have hspin := cavity_original_spin_limit hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a ha Φ site
  have hs : Tendsto (fun r => G r-A r) atTop (𝓝 0) := hspin
  have hoverlap := cavity_original_overlap_limit hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a ha Ψ
  have ho : Tendsto (fun r => G r-C r) atTop (𝓝 0) := by
    convert hoverlap using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    have hsite := cavity_full_weighted_overlap_identity (Nat.add_pos_left (hN r) n)
      (μO r) (θ r) (eig r) (cavitySpectralGroup (g r)) (u r) (hu r) Φ (Fin.natAdd (N r) site)
    have hlevel : (∫ t, Ψ (q r t) ∂pathMeasure) = C r := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact cavityOverlapWeightedTest_eq Φ ⟨by linarith [(q r).nonneg t],(q r).le_one t⟩
    change G r-C r = _ - _
    rw [← hsite,hlevel]
  have hh := ho.sub hs
  simp only [sub_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  have hi (v : OverlapPath) : Integrable (fun t => Φ (q r t)*v t) pathMeasure := by
    apply integrable_of_measurable_abs_le
      ((Φ.continuous.measurable.comp (q r).measurable).mul v.measurable)
    intro t
    change |Φ (q r t)*v t| ≤ ‖Φ‖
    rw [abs_mul,abs_of_nonneg (v.nonneg t)]
    exact (mul_le_mul_of_nonneg_left (v.le_one t) (abs_nonneg _)).trans
      (by simpa only [mul_one,Real.norm_eq_abs] using Φ.norm_coe_le_norm (q r t))
  change (∫ t, Φ (q r t)*(f r t-q r t) ∂pathMeasure) = (G r-C r)-(G r-A r)
  simp_rw [mul_sub]
  rw [integral_sub (hi (f r)) (hi (q r))]
  dsimp only [A,C]
  ring

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_original_scalar_self_consistency_oai := @OAI.InvariantIsing.cavity_original_scalar_self_consistency_oai
