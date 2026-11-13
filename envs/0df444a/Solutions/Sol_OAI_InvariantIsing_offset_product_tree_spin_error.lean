-- Prove2me | solution 1 for OAI.InvariantIsing.offset_product_tree_spin_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:03:01.853746+00:00
-- url     : https://prove2.me/submissions/f56d8483-1b74-44d1-b0fa-978f62e90378

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma measurable_countable_measure_pi {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] (r : ℕ) :
    Measurable (fun ω => Measure.pi (fun _ : Fin r => ν ω)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : Measure.pi (fun _ : Fin r => ν ω) s =
      ∑' σ : Fin r → X, (∏ i : Fin r, ν ω {σ i}) * Measure.dirac σ s := by
    rw [← Measure.sum_smul_dirac (Measure.pi (fun _ : Fin r => ν ω)),Measure.sum_apply _ hs]
    simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_singleton]
  simp_rw [he]
  apply Measurable.tsum
  intro σ
  exact (Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (measurableSet_singleton _)).comp hν)).mul_const _

lemma measurable_random_referenceReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) {r : ℕ}
    {D : Ω × (Fin r → X) → ℝ} (hD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  let κ : Kernel Ω (Fin r → X) := ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω),
    measurable_countable_measure_pi hν r⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω))
    infer_instance⟩
  have hm : Measurable (fun z : Ω × (Fin r → X) => Real.exp (∑ i, H (z.1,z.2 i))*D z) := by
    apply Measurable.mul _ hD
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun i _ => hH.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((measurable_random_referencePartition hν hH).pow_const r)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem cavity_twoReplica_disorder_symmetry {Ω X : Type*}
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
    (F : Ω → (Fin 2 → X) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ ω σ, |F ω σ| ≤ B)
    (hmeas : AEStronglyMeasurable (fun ω => ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) (F ω) ∂gaussianCoordinates) μ) :
    (∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g) (F ω) ∂gaussianCoordinates ∂μ) =
    ∫ ω, ∫ g, referenceReplicaMean ν
      (fun x => H ω x + cylinderField (C ω x) g)
      (fun σ => F (R ω) (fun i => e (σ i))) ∂gaussianCoordinates ∂μ := by
  rw [← hR.hasLaw.integral_comp hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only [Function.comp_apply]
    have ht := cavity_twoReplica_gaussian_transport ν e he (H (R ω))
      (measurable_of_countable _) (C (R ω)) (fun _ => measurable_of_countable _)
      (F (R ω)) (measurable_of_countable _)
    simp_rw [henergy] at ht
    rw [← ht]
    exact (cavity_twoReplica_same_covariance ν (H ω)
      (fun σ => F (R ω) (fun i => e (σ i))) (hH ω) (C ω)
      (fun x => C (R ω) (e x)) (hV ω) (fun x => hV (R ω) (e x))
      (hcov ω) hB (fun σ => hFb (R ω) (fun i => e (σ i)))).symm

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityDisorderMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded disorder-dependent replica averages and finite sums. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_nested_disorder_replica_sum {Ω Ω' X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : ι → Ω → (Fin r → X) → ℝ) (hmF : ∀ i ω, Measurable (F i ω))
    (hmeas : ∀ i, Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F i z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i ω σ, |F i ω σ| ≤ B) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i ω σ) ∂P ∂μ) =
      ∑ i, ∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P ∂μ := by
  have hiG (ω : Ω) (i : ι) :
      Integrable (fun g => referenceReplicaMean ν (H ω g) (F i ω)) P :=
    integrable_of_measurable_abs_le ((hmeas i).comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i ω) (hmF i ω) hB (hF i ω))
  have he (ω : Ω) :
      (∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i ω σ) ∂P) =
        ∑ i, ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P := by
    simp_rw [cavity_referenceReplicaMean_sum ν _ (fun i => F i ω)
      (fun i => hmF i ω) (fun _ => B) (fun i => hF i ω)]
    exact integral_finsetSum _ (fun i _ => hiG ω i)
  have hiU (i : ι) : Integrable
      (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F i ω) ∂P) μ :=
    integrable_of_measurable_abs_le
      ((hmeas i).stronglyMeasurable.integral_prod_right'.measurable)
      (fun ω => abs_integral_le_const_of_bound ((hmeas i).comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i ω) (hmF i ω) hB (hF i ω)))
  simp_rw [he]
  exact integral_finsetSum _ (fun i _ => hiU i)

lemma cavity_nested_disorder_abs_le {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : Ω → (Fin r → X) → ℝ) (hmF : ∀ ω, Measurable (F ω))
    (hmeas : Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω σ, |F ω σ| ≤ B) :
    |∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P ∂μ| ≤ B := by
  apply abs_integral_le_const_of_bound hmeas.stronglyMeasurable.integral_prod_right'.measurable
  intro ω
  apply abs_integral_le_const_of_bound (hmeas.comp measurable_prodMk_left)
  intro g
  exact referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded cutoff tests for the actual perturbed Ising law, with the
same Haar and Gaussian disorder in the full and restricted models. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityFullHamiltonian {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityPerturbationField I u x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullSiteIdentity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

lemma cavityReplicaOverlap_signed {N depth : ℕ} (p : Equiv.Perm (Fin N))
    (flip : Fin N → Bool) (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    cavityReplicaOverlap (fun i => (cavitySignedSpinPermutation p flip (σ i).1, (σ i).2)) =
      cavityReplicaOverlap σ := by
  unfold cavityReplicaOverlap cavityTotalSpinOverlap
  simp only [cavitySignedSpinPermutation_pair]
  congr 1
  exact Equiv.sum_comp p (fun i => spinValue ((σ 0).1 i) * spinValue ((σ 1).1 i))

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

lemma cavityTotalSpinOverlap_mul_size {N : ℕ} (x : Spin N × Spin N) :
    (N : ℝ) * cavityTotalSpinOverlap x = ∑ i, spinValue (x.1 i) * spinValue (x.2 i) := by
  by_cases hN : N = 0
  · subst N
    simp [cavityTotalSpinOverlap]
  · rw [cavityTotalSpinOverlap, ← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]

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

lemma cavity_spin_split_overlap {N n : ℕ} (σ τ : Spin (N+n)) :
    ((N+n:ℕ):ℝ) * cavityTotalSpinOverlap (σ,τ) =
      (N:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).1,(cavitySpinSplit N n τ).1) +
      (n:ℝ) * cavityTotalSpinOverlap ((cavitySpinSplit N n σ).2,(cavitySpinSplit N n τ).2) := by
  simp only [cavityTotalSpinOverlap_mul_size,Fin.sum_univ_add,
    cavitySpinSplit_left,cavitySpinSplit_right]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityOverlapWeightedTest
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPrefixOverlap
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed initial remainder changes the overlap by at most twice its fraction. -/
noncomputable section
open IsingPerceptron
namespace InvariantIsing

lemma cavity_spin_split_right_overlap_error {r N : ℕ} (hN : 0<N) (σ τ : Spin (r+N)) :
    |cavityTotalSpinOverlap (σ,τ)-
      cavityTotalSpinOverlap ((cavitySpinSplit r N σ).2,(cavitySpinSplit r N τ).2)|≤
      2*(r:ℝ)/(r+N) := by
  let a := cavityTotalSpinOverlap ((cavitySpinSplit r N σ).1,(cavitySpinSplit r N τ).1)
  let b := cavityTotalSpinOverlap ((cavitySpinSplit r N σ).2,(cavitySpinSplit r N τ).2)
  let c := cavityTotalSpinOverlap (σ,τ)
  have hp : (0:ℝ) < r+N := by exact_mod_cast Nat.add_pos_right r hN
  have hs : ((r:ℝ)+N)*c=r*a+N*b := by
    simpa only [Nat.cast_add] using cavity_spin_split_overlap σ τ
  have he : c-b=(r:ℝ)*(a-b)/(r+N) := by
    apply (eq_div_iff hp.ne').mpr
    nlinarith [hs]
  change |c-b|≤_
  rw [he,abs_div,abs_of_pos hp,abs_mul,abs_of_nonneg (Nat.cast_nonneg r)]
  apply div_le_div_of_nonneg_right _ hp.le
  have ha : |a|≤1 := abs_cavityTotalSpinOverlap_le _
  have hb : |b|≤1 := abs_cavityTotalSpinOverlap_le _
  have hab : |a-b|≤2 := (abs_sub a b).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg r)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinBias
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constant energy shift on the constraint set cancels from its
actual conditional Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinLaw_mass {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H : Spin N → ℝ) (T : Finset (Spin N)) :
    (restrictedSpinLaw S H).real T =
      (∑ σ ∈ S ∩ T, Real.exp (H σ)) / ∑ σ ∈ S, Real.exp (H σ) := by
  classical
  rw [measureReal_def, restrictedSpinLaw, cond_apply S.measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real S)⁻¹ *
    (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) H).real
      ((S : Set (Spin N)) ∩ T) = _
  rw [← Finset.coe_inter, spinGibbs_mass_finset, spinGibbs_mass_finset]
  have hZ := (sum_exp_pos H).ne'
  have hZS := (Finset.sum_pos (fun σ _ => Real.exp_pos (H σ)) hS).ne'
  field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normalized constrained prior gives exactly the conditional Gibbs
law. Its log normalizer retains the original cube mass as an explicit
constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedSpinPrior_singleton {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (σ : Spin N) : (restrictedSpinPrior S hS : Measure (Spin N)).real {σ} =
      if σ ∈ S then (S.card : ℝ)⁻¹ else 0 := by
  have hm := restrictedSpinLaw_mass S hS (fun _ => 0) {σ}
  simp only [Finset.coe_singleton] at hm
  change (restrictedSpinLaw S (fun _ => 0)).real {σ} = _
  rw [hm]
  by_cases hσ : σ ∈ S <;> simp [hσ]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedSpinSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A spin permutation preserving a constraint preserves its normalized
prior and its product with the actual cascade leaf law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restrictedSpinPrior_equiv {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (e : Spin N ≃ Spin N) (hinv : ∀ σ, e σ ∈ S ↔ σ ∈ S) :
    MeasurePreserving e (restrictedSpinPrior S hS : Measure (Spin N))
      (restrictedSpinPrior S hS : Measure (Spin N)) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro σ
  have hp : e ⁻¹' {σ} = {e.symm σ} := by
    ext τ
    exact e.eq_symm_apply.symm
  have hi : e.symm σ ∈ S ↔ σ ∈ S := by
    simpa only [e.apply_symm_apply] using (hinv (e.symm σ)).symm
  have he : ((restrictedSpinPrior S hS : Measure (Spin N)).map e).real {σ} =
      (restrictedSpinPrior S hS : Measure (Spin N)).real {σ} := by
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton σ), hp]
    change (restrictedSpinPrior S hS : Measure (Spin N)).real {e.symm σ} = _
    simp only [restrictedSpinPrior_singleton, hi]
  have hh := congrArg ENNReal.ofReal he
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

theorem restricted_labeled_spin_reference_equiv {N depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (T : LabeledTree depth)
    (e : Spin N ≃ Spin N) (hinv : ∀ σ, e σ ∈ S ↔ σ ∈ S) :
    MeasurePreserving (fun x : Spin N × LabeledLeaf depth => (e x.1, x.2))
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T) :=
  (restrictedSpinPrior_equiv S hS e hinv).prod (MeasurePreserving.id (labeledLeafLaw depth T))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_RepeatedBlockPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma even_block_permutation {K : ℕ} (hK : 3 ≤ K) (i j : Fin K) :
    ∃ p : Equiv.Perm (Fin K), Equiv.Perm.sign p = 1 ∧ p i = j := by
  by_cases hij : i = j
  · subst j
    exact ⟨1, by simp, by simp⟩
  have hk : ∃ k : Fin K, k ≠ i ∧ k ≠ j := by
    by_contra! h
    have hs : (Finset.univ : Finset (Fin K)) ⊆ {i,j} := by
      intro k _
      have he : k = i ∨ k = j := by
        by_cases hi : k = i
        · exact Or.inl hi
        · exact Or.inr (h k hi)
      simpa using he
    have hc := Finset.card_le_card hs
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_pair hij] at hc
    omega
  obtain ⟨k,hki,hkj⟩ := hk
  refine ⟨Equiv.swap j k * Equiv.swap i k, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.sign_swap hkj.symm, Equiv.Perm.sign_swap hki.symm]
    norm_num
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated identical cavity constraints admit every even permutation
of their blocks. No coordinate sign flip is introduced. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma consecutiveBlockSitePermutation_apply {n K : ℕ} (p : Equiv.Perm (Fin K))
    (i : Fin n) (b : Fin K) :
    consecutiveBlockSitePermutation p (finProdFinEquiv (b,i)) = finProdFinEquiv (p b,i) := by
  simp [consecutiveBlockSitePermutation]

lemma consecutiveBlockSitePermutation_sign {n K : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p = 1) :
    Equiv.Perm.sign (consecutiveBlockSitePermutation (n := n) p) = 1 := by
  simp [consecutiveBlockSitePermutation, Equiv.Perm.sign_prodCongrLeft, hp]

lemma consecutiveBlockSitePermutation_flip {n K : ℕ} (hN : 0 < K*n)
    (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1) (i : Fin (K*n)) :
    cavityPermutationFlip hN (consecutiveBlockSitePermutation p) i = false := by
  have hs := consecutiveBlockSitePermutation_sign (n := n) p hp
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hs]

lemma consecutiveBlockConstraint_permutation {n K : ℕ} (hN : 0 < K*n)
    (C : Finset (Spin n)) (p : Equiv.Perm (Fin K)) (hp : Equiv.Perm.sign p = 1)
    (σ : Spin (K*n)) :
    cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
      (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)) σ ∈ consecutiveBlockConstraint n K C ↔
      σ ∈ consecutiveBlockConstraint n K C := by
  simp only [mem_consecutiveBlockConstraint]
  have he (b : Fin K) : (fun i : Fin n =>
      cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
        (cavityPermutationFlip hN (consecutiveBlockSitePermutation p)) σ (finProdFinEquiv (b,i))) =
      (fun i : Fin n => σ (finProdFinEquiv (p b,i))) := by
    funext i
    change (if cavityPermutationFlip hN (consecutiveBlockSitePermutation p) _ then _ else _) = _
    rw [consecutiveBlockSitePermutation_flip hN p hp]
    simp only [Bool.false_eq_true, ↓reduceIte, consecutiveBlockSitePermutation_apply]
  simp_rw [he]
  constructor
  · intro h b
    simpa using h (p.symm b)
  · intro h b
    exact h (p b)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_ConsecutiveBlockTransport
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension transport for consecutive constrained blocks. The successor
constraint is exactly the base/cavity product, including its cube mass. -/

noncomputable section
open IsingPerceptron

namespace InvariantIsing

lemma spin_family_dimension_cast {α : Sort*}
    (F : (N : ℕ) → Finset (Spin N) → α) {N M : ℕ}
    (h : N = M) (S : Finset (Spin N)) :
    F M (S.map (spinDimensionCast h).toEmbedding) = F N S := by
  subst M
  congr 1
  ext σ
  simp [spinDimensionCast]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockPrior
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed initial remainder followed by repeated constrained blocks.
Adding a new last block preserves this exact finite spin family. -/
noncomputable section
open IsingPerceptron
namespace InvariantIsing

lemma mem_offsetBlockConstraint {r n K : ℕ} (R : Finset (Spin r))
    (C : Finset (Spin n)) (σ : Spin (r+K*n)) :
    σ∈offsetBlockConstraint K R C ↔
      (fun i => σ (Fin.castAdd (K*n) i))∈R ∧
        ∀ b : Fin K, (fun i => σ (Fin.natAdd r (finProdFinEquiv (b,i))))∈C := by
  rw [offsetBlockConstraint,mem_cavityProductSlice,mem_consecutiveBlockConstraint]
  rfl

lemma offsetBlockJoin_mem {r n K : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n))
    (σ : Spin ((r+K*n)+n)) :
    offsetBlockJoin r n K σ ∈ offsetBlockConstraint (K+1) R C ↔
      σ∈cavityProductSlice (offsetBlockConstraint K R C) C := by
  rw [mem_offsetBlockConstraint,mem_cavityProductSlice,mem_offsetBlockConstraint]
  have hR : (fun i => offsetBlockJoin r n K σ (Fin.castAdd ((K+1)*n) i)) =
      (fun i => (cavitySpinSplit (r+K*n) n σ).1 (Fin.castAdd (K*n) i)) := by
    funext i
    apply congrArg σ
    apply Fin.ext
    rfl
  have hl (b : Fin K) :
      (fun i => offsetBlockJoin r n K σ (Fin.natAdd r (finProdFinEquiv (b.castSucc,i)))) =
      (fun i => (cavitySpinSplit (r+K*n) n σ).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) := by
    funext i
    apply congrArg σ
    apply Fin.ext
    rfl
  have hr :
      (fun i => offsetBlockJoin r n K σ (Fin.natAdd r (finProdFinEquiv (Fin.last K,i)))) =
      (cavitySpinSplit (r+K*n) n σ).2 := by
    funext i
    apply congrArg σ
    apply Fin.ext
    change r+(i.val+n*K)=(r+K*n)+i.val
    simp [Nat.mul_comm,Nat.add_comm,Nat.add_left_comm]
  rw [hR]
  constructor
  · rintro ⟨hR,hC⟩
    exact ⟨⟨hR,fun b => hl b ▸ hC b.castSucc⟩,hr ▸ hC (Fin.last K)⟩
  · rintro ⟨⟨hR,hC⟩,hlast⟩
    refine ⟨hR,fun b => ?_⟩
    refine Fin.lastCases ?_ (fun b => ?_) b
    · rw [hr]
      exact hlast
    · rw [hl]
      exact hC b

lemma offsetBlockConstraint_succ {r n K : ℕ} (R : Finset (Spin r)) (C : Finset (Spin n)) :
    offsetBlockConstraint (K+1) R C =
      (cavityProductSlice (offsetBlockConstraint K R C) C).map (offsetBlockJoin r n K).toEmbedding := by
  ext σ
  rw [Finset.mem_map]
  constructor
  · intro hσ
    exact ⟨(offsetBlockJoin r n K).symm σ,(offsetBlockJoin_mem R C _).mp (by simpa using hσ),by simp⟩
  · rintro ⟨τ,hτ,rfl⟩
    exact (offsetBlockJoin_mem R C τ).mpr hτ

lemma offset_spin_family_succ {α : Sort*}
    (F : (N : ℕ) → Finset (Spin N) → α) {r n : ℕ} (K : ℕ)
    (R : Finset (Spin r)) (C : Finset (Spin n)) :
    F (r+(K+1)*n) (offsetBlockConstraint (K+1) R C)=
      F ((r+K*n)+n) (cavityProductSlice (offsetBlockConstraint K R C) C) := by
  rw [offsetBlockConstraint_succ]
  exact spin_family_dimension_cast F (by simp only [Nat.add_mul,Nat.one_mul]; omega) _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_RepeatedBlockRemainderPrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even block permutations preserve repeated constraints and an
arbitrary fixed remainder constraint. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavityPermutationFlip_eq_false_of_sign {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (hp : Equiv.Perm.sign p = 1) (i : Fin N) :
    cavityPermutationFlip hN p i = false := by
  norm_num [cavityPermutationFlip, Matrix.det_permutation, hp]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even permutations of the repeated blocks preserve an arbitrary initial remainder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma offsetBlockSitePermutation_prefix {r n K : ℕ} (p : Equiv.Perm (Fin K)) (i : Fin r) :
    offsetBlockSitePermutation p (Fin.castAdd (K*n) i)=Fin.castAdd (K*n) i := by
  simp [offsetBlockSitePermutation]

lemma offsetBlockSitePermutation_block {r n K : ℕ} (p : Equiv.Perm (Fin K)) (i : Fin (K*n)) :
    offsetBlockSitePermutation p (Fin.natAdd r i)=Fin.natAdd r (consecutiveBlockSitePermutation p i) := by
  simp [offsetBlockSitePermutation]

lemma offsetBlockSitePermutation_sign {r n K : ℕ} (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p=1) :
    Equiv.Perm.sign (offsetBlockSitePermutation (r := r) (n := n) p)=1 := by
  simp [offsetBlockSitePermutation,Equiv.Perm.sign_sumCongr,consecutiveBlockSitePermutation_sign p hp]

lemma offsetBlockConstraint_permutation {r n K : ℕ} (hKn : 0<K*n)
    (R : Finset (Spin r)) (C : Finset (Spin n)) (p : Equiv.Perm (Fin K))
    (hp : Equiv.Perm.sign p=1) (σ : Spin (r+K*n)) :
    cavitySignedSpinPermutation (offsetBlockSitePermutation p)
      (cavityPermutationFlip (Nat.add_pos_right r hKn) (offsetBlockSitePermutation p)) σ ∈
        offsetBlockConstraint K R C ↔ σ∈offsetBlockConstraint K R C := by
  let f := cavitySignedSpinPermutation (offsetBlockSitePermutation (r := r) (n := n) p)
    (cavityPermutationFlip (Nat.add_pos_right r hKn) (offsetBlockSitePermutation p))
  have hl : (cavitySpinSplit r (K*n) (f σ)).1=(cavitySpinSplit r (K*n) σ).1 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _)=_
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (offsetBlockSitePermutation_sign p hp)]
    simp only [Bool.false_eq_true,↓reduceIte,offsetBlockSitePermutation_prefix]
    rfl
  have hr : (cavitySpinSplit r (K*n) (f σ)).2=
      cavitySignedSpinPermutation (consecutiveBlockSitePermutation p)
        (cavityPermutationFlip hKn (consecutiveBlockSitePermutation p))
        (cavitySpinSplit r (K*n) σ).2 := by
    funext i
    change (if cavityPermutationFlip _ _ _ then _ else _)=(if cavityPermutationFlip _ _ _ then _ else _)
    rw [cavityPermutationFlip_eq_false_of_sign _ _ (offsetBlockSitePermutation_sign p hp),
      consecutiveBlockSitePermutation_flip hKn p hp]
    simp only [Bool.false_eq_true,↓reduceIte,offsetBlockSitePermutation_block]
    rfl
  change f σ∈cavityProductSlice R (consecutiveBlockConstraint n K C) ↔
    σ∈cavityProductSlice R (consecutiveBlockConstraint n K C)
  simp only [mem_cavityProductSlice,hl,hr,consecutiveBlockConstraint_permutation hKn C p hp]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedDisorderTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disorder-dependent bounded tests, used for physical spectral
projections before any restriction of the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_restrictedCavityFullDisorderInner {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2)
      (F p.1)) := by
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T))
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
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) (F p.1))
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.1.1 z.2)
    hmH (hFm.comp (measurable_fst.fst.prodMk measurable_snd))

theorem restricted_full_disorder_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N))
    (hinv : ∀ σ, cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ ∈ S ↔ σ ∈ S)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
    (∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (F U) ∂gaussianCoordinates ∂μ) =
    ∫ U, ∫ g, referenceReplicaMean ν
      (fun x => rotatedEnergy eig (specialRotation U) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
      (fun σ => F (U * (spectralPermutation hN p)⁻¹) (fun i =>
        (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) (σ i).1, (σ i).2)))
      ∂gaussianCoordinates ∂μ := by
  dsimp only
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) (F U) ∂gaussianCoordinates) :=
    (measurable_restrictedCavityFullDisorderInner S hS T eig I u F hFm).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_disorder_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (restricted_labeled_spin_reference_equiv S hS T e hinv) H C
    (fun U => ∑ σ : Spin N, |rotatedEnergy eig (specialRotation U) σ|)
    (fun _ => 4 * (N * perturbationScale N ^ 2))
  · intro U x
    exact Finset.single_le_sum (f := fun σ : Spin N =>
      |rotatedEnergy eig (specialRotation U) σ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x.1)
  · intro U x
    exact cavityPerturbationCoefficients_sq_le _ I u hu x
  · intro U x
    exact rotatedEnergy_cavityPermutation hN p eig U x.1
  · intro U x y
    simp only [C, e, cavityPerturbationCoefficients_cross, cavityWeightedKernel,
      cavityPerturbationKernel, projectedOverlap_cavityPermutation]
  · exact hB
  · exact hF
  · exact hmean.aestronglyMeasurable

lemma restrictedCavityFullDisorderTest_abs_le {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    |restrictedCavityFullDisorderTest S hS μ T eig I u F| ≤ B := by
  exact cavity_nested_disorder_abs_le μ gaussianCoordinates
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_restrictedCavityFullDisorderInner S hS T eig I u F hFm) hB hF

lemma restrictedCavityFullDisorderTest_sum {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : ∀ i, Measurable (Function.uncurry (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i U σ, |F i U σ| ≤ B) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => ∑ i, F i U σ) =
      ∑ i, restrictedCavityFullDisorderTest S hS μ T eig I u (F i) := by
  exact cavity_nested_disorder_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ _ => measurable_of_countable _)
    (fun i => measurable_restrictedCavityFullDisorderInner S hS T eig I u (F i) (hmF i)) hB hF


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_RepeatedBlockSpinIdentity
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the two-spin test over one constrained block equals its
average over every site, and hence the total-overlap test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma restrictedCavityFullDisorderTest_const_mul {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (μ : Measure (SpecialOrthogonal N))
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => c * F U σ) =
      c * restrictedCavityFullDisorderTest S hS μ T eig I u F := by
  simp only [restrictedCavityFullDisorderTest, referenceReplicaMean_const_mul, integral_const_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFullTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff control in the full perturbed model. The bad compression
event is paid for only by its probability, never by an inverse moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma restrictedCavityFullDisorderTest_sub {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F G : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) (hmG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) (hG : ∀ U σ, |G U σ| ≤ B) :
    restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => F U σ - G U σ) =
      restrictedCavityFullDisorderTest S hS μ T eig I u F - restrictedCavityFullDisorderTest S hS μ T eig I u G := by
  let H : Fin 2 → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ :=
    ![F, fun U σ => (-1 : ℝ) * G U σ]
  have hmH : ∀ i, Measurable (Function.uncurry (H i)) := by
    intro i
    fin_cases i
    · exact hmF
    · exact hmG.const_mul (-1)
  have hH : ∀ i U σ, |H i U σ| ≤ B := by
    intro i U σ
    fin_cases i
    · exact hF U σ
    · change |(-1 : ℝ) * G U σ| ≤ B
      simpa only [neg_one_mul, abs_neg] using hG U σ
  have hs := restrictedCavityFullDisorderTest_sum S hS μ T eig I u H hmH hB hH
  simp only [Fin.sum_univ_two] at hs
  change restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => F U σ + (-1 : ℝ) * G U σ) =
    restrictedCavityFullDisorderTest S hS μ T eig I u F +
      restrictedCavityFullDisorderTest S hS μ T eig I u (fun U σ => (-1 : ℝ) * G U σ) at hs
  rw [restrictedCavityFullDisorderTest_const_mul] at hs
  simpa only [neg_one_mul, sub_eq_add_neg] using hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetBlockSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-block spin averaging with an arbitrary fixed remainder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

theorem offset_block_spin_identity {n K r m depth : ℕ} (hn : 0 < n) (hK : 3 ≤ K)
    (C : Finset (Spin n)) (hC : C.Nonempty) (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin K) :
    restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC)
      μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
        ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) *
          spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) =
      restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ) := by
  have hblock : 0 < K*n := Nat.mul_pos (by omega) hn
  have hN : 0 < r+K*n := Nat.add_pos_right r hblock
  let S := offsetBlockConstraint K R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
  let F := fun (i : Fin n) (b : Fin K) (_ : SpecialOrthogonal (r+K*n))
      (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) *
      spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b,i))))
  let a := fun i b => restrictedCavityFullDisorderTest S hS μ T eig I u (F i b)
  have hF (i : Fin n) (b : Fin K) (U) (σ) : |F i b U σ| ≤ ‖Φ‖ := by
    simpa only [F, abs_mul, abs_spinValue, mul_one, Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hm (i : Fin n) (b : Fin K) : Measurable (Function.uncurry (F i b)) :=
    (measurable_of_countable _).comp measurable_snd
  have he (i : Fin n) (b : Fin K) : a i b = a i b₀ := by
    obtain ⟨p,hp,hpb⟩ := even_block_permutation hK b b₀
    have ht := restricted_full_disorder_site_symmetry hN S hS μ T eig I u hu
      (offsetBlockSitePermutation (n := n) p) (offsetBlockConstraint_permutation hblock R C p hp)
      (F i b) (hm i b) (norm_nonneg _) (hF i b)
    change a i b = restrictedCavityFullDisorderTest S hS μ T eig I u _ at ht
    have hf : (fun U σ => F i b (U * (spectralPermutation hN (offsetBlockSitePermutation p))⁻¹)
        (fun k => (cavitySignedSpinPermutation (offsetBlockSitePermutation p)
          (cavityPermutationFlip hN (offsetBlockSitePermutation p)) (σ k).1, (σ k).2))) = F i b₀ := by
      funext U σ
      dsimp only [F]
      rw [cavityReplicaOverlap_signed, mul_assoc, cavitySignedSpinPermutation_pair,
        offsetBlockSitePermutation_block, consecutiveBlockSitePermutation_apply, hpb]
      ring
    rw [hf] at ht
    exact ht
  have hblock : (fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) * spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, F i b₀ U σ) := by
    funext U σ
    simp only [F, mul_assoc, ← Finset.mul_sum]
    ring
  have htotal : (fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ) =
      (fun U σ => ((K*n : ℕ) : ℝ)⁻¹ * ∑ i : Fin n, ∑ b : Fin K, F i b U σ) := by
    funext U σ
    have hs : (∑ i : Fin n, ∑ b : Fin K,
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b,i)))) * spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b,i))))) =
        ∑ j : Fin (K*n), spinValue ((σ 0).1 (Fin.natAdd r j)) * spinValue ((σ 1).1 (Fin.natAdd r j)) := by
      rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type (fun p : Fin K × Fin n =>
        spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv p))) *
        spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv p))))).symm.trans
          (finProdFinEquiv.sum_comp (fun j : Fin (K*n) =>
            spinValue ((σ 0).1 (Fin.natAdd r j)) * spinValue ((σ 1).1 (Fin.natAdd r j))))
    simp only [F, mul_assoc, ← Finset.mul_sum]
    rw [hs]
    unfold offsetRegularBlockOverlap cavityTotalSpinOverlap
    simp only [cavitySpinSplit_right]
    ring
  rw [hblock, htotal, restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_const_mul,
    restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i => F i b₀)
      (fun i => hm i b₀) (norm_nonneg _) (fun i => hF i b₀)]
  have hsum (i : Fin n) : restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun U σ => ∑ b, F i b U σ) = (K : ℝ) * a i b₀ := by
    rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (F i) (hm i)
      (norm_nonneg _) (hF i)]
    change (∑ b, a i b) = _
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumBound (i : Fin n) (U) (σ) : |∑ b, F i b U σ| ≤ (K : ℝ) * ‖Φ‖ := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin K))) => hF i b U σ))
  rw [restrictedCavityFullDisorderTest_sum S hS μ T eig I u (fun i U σ => ∑ b, F i b U σ)
    (fun i => Finset.measurable_sum _ (fun b _ => hm i b))
    (mul_nonneg (Nat.cast_nonneg K) (norm_nonneg Φ)) hsumBound]
  simp_rw [hsum]
  change (n : ℝ)⁻¹ * (∑ i, a i b₀) = ((K*n : ℕ) : ℝ)⁻¹ * ∑ i, (K : ℝ) * a i b₀
  rw [← Finset.mul_sum, Nat.cast_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp


lemma abs_offsetRegularBlockOverlap_le {n K r depth : ℕ}
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) :
    |offsetRegularBlockOverlap σ| ≤ 1 := abs_cavityTotalSpinOverlap_le _

lemma offsetRegularBlockOverlap_error {n K r depth : ℕ} (hN : 0 < K*n)
    (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) :
    |offsetRegularBlockOverlap σ - cavityReplicaOverlap σ| ≤ 2*(r:ℝ)/(r+K*n) := by
  simpa only [offsetRegularBlockOverlap, cavityReplicaOverlap, abs_sub_comm, Nat.cast_mul] using
    cavity_spin_split_right_overlap_error hN (σ 0).1 (σ 1).1

theorem offset_block_spin_error {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 3 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (R : Finset (Spin r)) (hR : R.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) (b₀ : Fin K) :
    |restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
        (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) *
          ((n:ℝ)⁻¹ * ∑ i : Fin n,
            spinValue ((σ 0).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))) *
            spinValue ((σ 1).1 (Fin.natAdd r (finProdFinEquiv (b₀,i)))))) -
      restrictedCavityFullDisorderTest (offsetBlockConstraint K R C)
        (offsetBlockConstraint_nonempty R hR C hC)
        μ T eig I u (fun _ σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ)| ≤
      ‖Φ‖ * (2*(r:ℝ)/(r+K*n)) := by
  rw [offset_block_spin_identity hn hK C hC R hR μ T eig I u hu Φ b₀]
  let S := offsetBlockConstraint K R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
  let F := fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ
  let G := fun (_ : SpecialOrthogonal (r+K*n)) (σ : Fin 2 → Spin (r+K*n) × LabeledLeaf depth) =>
    Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ
  have hmF : Measurable (Function.uncurry F) := (measurable_of_countable _).comp measurable_snd
  have hmG : Measurable (Function.uncurry G) := (measurable_of_countable _).comp measurable_snd
  have hF : ∀ U σ, |F U σ| ≤ ‖Φ‖ := by
    intro U σ
    rw [abs_mul]
    exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
      (abs_offsetRegularBlockOverlap_le σ) (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hG : ∀ U σ, |G U σ| ≤ ‖Φ‖ := by
    intro U σ
    rw [abs_mul]
    exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
      (abs_cavityTotalSpinOverlap_le _) (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  change |restrictedCavityFullDisorderTest S hS μ T eig I u F -
    restrictedCavityFullDisorderTest S hS μ T eig I u G| ≤ _
  rw [← restrictedCavityFullDisorderTest_sub S hS μ T eig I u F G hmF hmG (norm_nonneg _) hF hG]
  apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u (fun U σ => F U σ - G U σ) (hmF.sub hmG)
    (mul_nonneg (norm_nonneg _) (by positivity))
  intro U σ
  change |Φ (cavityReplicaOverlap σ) * offsetRegularBlockOverlap σ -
    Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ| ≤ _
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (cavityReplicaOverlap σ))
    (offsetRegularBlockOverlap_error (Nat.mul_pos (by omega) hn) σ) (abs_nonneg _) (norm_nonneg _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedTreeFullRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded full and restricted Gibbs tests can be averaged over the
original labeled-tree law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_restrictedFullTest_tree {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun T => restrictedCavityFullDisorderTest S hS μ T eig I u (fun _ => F)) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (restrictedSpinPrior S hS : Measure (Spin N))).comp measurable_fst.fst
  let H : Ω × X → ℝ := fun p => cavityFullHamiltonian eig I u (p.1.1.2,p.1.2) p.2
  have hH : Measurable H := by
    have hp : Measurable (fun p : Ω × X => ((p.1.1.2,p.1.2),p.2)) :=
      (measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd
    exact Measurable.comp
      (g := Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u))
      (f := fun p : Ω × X => ((p.1.1.2,p.1.2),p.2))
      (measurable_cavityFullHamiltonian eig I u) hp
  have hh := measurable_random_referenceReplicaMean hν hH
    (D := fun p => F p.2) ((measurable_of_countable F).comp measurable_snd)
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedFullSpinAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinate averaging of full constrained spin tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing

lemma restricted_full_spin_average {N n m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n → Fin N) :
    restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) =
      (n : ℝ)⁻¹ * ∑ i, restrictedFullTest S hS μ T eig I u (cavityFullSpinInsertion Φ (site i)) := by
  have he : (fun (_ : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) =>
      Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i,
        spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) =
      (fun U σ => (n : ℝ)⁻¹ * ∑ i, (fun _ => cavityFullSpinInsertion Φ (site i)) U σ) := by
    funext U σ
    simp only [cavityFullSpinInsertion, ← Finset.mul_sum]
    ring
  unfold restrictedFullTest
  rw [he, restrictedCavityFullDisorderTest_const_mul]
  congr 1
  apply restrictedCavityFullDisorderTest_sum S hS μ T eig I u
    (fun i _ => cavityFullSpinInsertion Φ (site i))
    (fun i => (measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
  intro i U σ
  simpa only [cavityFullSpinInsertion, abs_mul, abs_spinValue, mul_one, one_mul, Real.norm_eq_abs]
    using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)

lemma restricted_full_tree_spin_average {N n m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n → Fin N) :
    (∫ T, restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i)) * spinValue ((σ 1).1 (site i)))) ∂θ) =
      (n : ℝ)⁻¹ * ∑ i, ∫ T, restrictedFullTest S hS μ T eig I u
        (cavityFullSpinInsertion Φ (site i)) ∂θ := by
  simp_rw [restricted_full_spin_average S hS μ _ eig I u Φ site]
  rw [integral_const_mul, integral_finsetSum]
  intro i _
  apply integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree S hS μ eig I u _)
  intro T
  change |restrictedCavityFullDisorderTest S hS μ T eig I u
    (fun _ => cavityFullSpinInsertion Φ (site i))| ≤ ‖Φ‖
  apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
    (fun _ => cavityFullSpinInsertion Φ (site i))
    ((measurable_of_countable (cavityFullSpinInsertion Φ (site i))).comp measurable_snd) (norm_nonneg Φ)
  intro U σ
  simpa only [cavityFullSpinInsertion, abs_mul, abs_spinValue, mul_one, one_mul, Real.norm_eq_abs]
    using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetProductSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-block spin average differs from the full overlap only by the
fixed prefix's proportion. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem offset_product_spin_error {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (r+K*n+n) → ℝ)
    (I : Fin m → Finset (Fin (r+K*n+n))) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (Φ : ℝ →ᵇ ℝ) :
    |restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        spinValue ((σ 0).1 (Fin.natAdd (r+K*n) i)) * spinValue ((σ 1).1 (Fin.natAdd (r+K*n) i)))) -
      restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤
      ‖Φ‖*(2*(r : ℝ)/(r+K*n+n)) := by
  let P := fun (N : ℕ) (S : Finset (Spin N)) => ∀ (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ), (∀ k, |u k| ≤ 2) → ∀ (site : Fin n → Fin N),
    (∀ i, (site i).val=r+K*n+i.val) →
    |restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
      ((n : ℝ)⁻¹ * ∑ i, spinValue ((σ 0).1 (site i))*spinValue ((σ 1).1 (site i)))) -
      restrictedFullTest S hS μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤
      ‖Φ‖*(2*(r : ℝ)/N)
  have hP : P (r+(K+1)*n) (offsetBlockConstraint (K+1) R C) := by
    intro hS μ hμ hμr T eig I u hu site hs
    have he : site=fun i => Fin.natAdd r (finProdFinEquiv (Fin.last K,i)) := by
      funext i
      apply Fin.ext
      rw [hs]
      change r+K*n+i.val=r+(i.val+n*K)
      simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    rw [he]
    have hw : (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ) :
        (Fin 2 → Spin (r+(K+1)*n) × LabeledLeaf depth) → ℝ)=
        (fun σ => Φ (cavityReplicaOverlap σ)*cavityReplicaOverlap σ) := by
      funext σ
      exact cavityOverlapWeightedTest_eq Φ (abs_le.mp (abs_cavityTotalSpinOverlap_le _))
    rw [hw]
    simpa only [restrictedFullTest, Nat.cast_add, Nat.cast_mul] using
      offset_block_spin_error hn (by omega : 3≤K+1) C hC R hR μ T eig I u hu Φ (Fin.last K)
  rw [offset_spin_family_succ P K R C] at hP
  simpa only [Nat.cast_add, Nat.cast_mul] using
    hP _ μ T eig I u hu (Fin.natAdd (r+K*n)) (fun _ => rfl)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_OffsetProductTreeSpin
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the prefix error over the original random cascade tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem offset_product_tree_spin_error_oai {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin (r+K*n+n) → ℝ) (I : Fin m → Finset (Fin (r+K*n+n)))
    (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2) (Φ : ℝ →ᵇ ℝ) :
    |(n : ℝ)⁻¹ * ∑ i : Fin n, ∫ T, restrictedFullTest
      (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i)) ∂θ -
      ∫ T, restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ)) ∂θ| ≤
      ‖Φ‖*(2*(r : ℝ)/(r+K*n+n)) := by
  let S := cavityProductSlice (offsetBlockConstraint K R C) C
  have hS : S.Nonempty := cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC
  have hspin (i : Fin n) : Integrable (fun T => restrictedFullTest S hS μ T eig I u
      (cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))) θ := by
    apply integrable_of_measurable_abs_le (measurable_restrictedFullTest_tree S hS μ eig I u _)
    intro T
    change |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))| ≤ ‖Φ‖
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
      (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))
      ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
    intro U σ
    simpa only [cavityFullSpinInsertion,abs_mul,abs_spinValue,mul_one,one_mul,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  let F := fun (T : LabeledTree depth) => restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
    ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (Fin.natAdd (r+K*n) i)) *
      spinValue ((σ 1).1 (Fin.natAdd (r+K*n) i))))
  let G := fun (T : LabeledTree depth) => restrictedFullTest S hS μ T eig I u
    (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))
  have hF : Integrable F θ := by
    simp only [F, restricted_full_spin_average]
    exact (integrable_finsetSum _ fun i _ => hspin i).const_mul _
  have hG : Integrable G θ := by
    apply integrable_of_measurable_abs_le (measurable_restrictedFullTest_tree S hS μ eig I u _)
    intro T
    change |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun _ => cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤ ‖cavityOverlapWeightedTest Φ‖
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
      (fun _ => cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))
      ((measurable_of_countable _).comp measurable_snd) (norm_nonneg (cavityOverlapWeightedTest Φ))
    intro U σ
    simpa only [cavityFullOverlapInsertion,Real.norm_eq_abs] using
      (cavityOverlapWeightedTest Φ).norm_coe_le_norm (cavityReplicaOverlap σ)
  rw [← restricted_full_tree_spin_average]
  change |(∫ T, F T ∂θ)-(∫ T, G T ∂θ)| ≤ _
  rw [← integral_sub hF hG]
  have hh := norm_integral_le_of_norm_le_const (μ := θ) (f := fun T => F T-G T)
    (C := ‖Φ‖*(2*(r : ℝ)/(r+K*n+n))) (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs] using offset_product_spin_error hn hK R hR C hC μ T eig I u hu Φ)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.offset_product_tree_spin_error_oai := @OAI.InvariantIsing.offset_product_tree_spin_error_oai
