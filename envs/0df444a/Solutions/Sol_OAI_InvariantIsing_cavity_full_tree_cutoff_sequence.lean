-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_full_tree_cutoff_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:22:14.743455+00:00
-- url     : https://prove2.me/submissions/8d67c156-f9d6-4e75-8a5e-c86fdfc40404

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
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
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := _root_.MeasureTheory.integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning on the nondegenerate Gram event does not change the
limit of bounded observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_conditioning_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)
    (hp : 0 < μ.real s) (f : Ω → ℝ) (hf : Integrable f μ)
    (M : ℝ) (hbound : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ| ≤ 2 * M * (1 - μ.real s) := by
  let p := μ.real s
  have hp1 : p ≤ 1 := measureReal_le_one
  have hpc : μ.real sᶜ = 1 - p := by
    simpa only [p, Measure.real, measure_univ, ENNReal.toReal_one] using
      (measureReal_compl (μ := μ) hs)
  have hA : |∫ x in s, f x ∂μ| ≤ p * M := by
    simpa only [Real.norm_eq_abs, mul_comm, p] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ s)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hB : |∫ x in sᶜ, f x ∂μ| ≤ M * (1 - p) := by
    simpa only [Real.norm_eq_abs, hpc, mul_comm] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ sᶜ)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfac : 0 ≤ p⁻¹ - 1 := by
    have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp).mpr hp1
    linarith
  have hmul : (p⁻¹ - 1) * p = 1 - p := by
    rw [sub_mul, inv_mul_cancel₀ hp.ne', one_mul]
  have he : (∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ =
      (p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      ← integral_add_compl hs hf]
    change p⁻¹ • (∫ x in s, f x ∂μ) - _ = _
    simp only [smul_eq_mul]
    ring
  rw [he]
  calc
    |(p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ| ≤
        (p⁻¹ - 1) * |∫ x in s, f x ∂μ| + |∫ x in sᶜ, f x ∂μ| := by
      simpa only [abs_mul, abs_of_nonneg hfac] using
        abs_sub ((p⁻¹ - 1) * (∫ x in s, f x ∂μ)) (∫ x in sᶜ, f x ∂μ)
    _ ≤ (p⁻¹ - 1) * (p * M) + M * (1 - p) :=
      add_le_add (mul_le_mul_of_nonneg_left hA hfac) hB
    _ = 2 * M * (1 - p) := by rw [← mul_assoc, hmul]; ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameMeasurable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the finite Gram normalization, including its
arbitrary singular-matrix values. -/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_matrix_inverse_measurable {q : ℕ} :
    Measurable (Inv.inv : Matrix (Fin q) (Fin q) ℝ → Matrix (Fin q) (Fin q) ℝ) := by
  have he (A : Matrix (Fin q) (Fin q) ℝ) : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp_rw [show (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) =
    (fun A => A.det⁻¹ • A.adjugate) from funext he]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

lemma measurable_cavityNormalizeFrame (n q : ℕ) :
    Measurable (cavityNormalizeFrame : Matrix (Fin n) (Fin q) ℝ → Matrix (Fin n) (Fin q) ℝ) := by
  have hg : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => A.transpose * A) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => ∑ k, A k i * A k j)
    exact Finset.measurable_sum _ (fun k _ =>
      (Matrix.measurable_apply (i := k) (j := i)).mul
        (Matrix.measurable_apply (i := k) (j := j)))
  have hs : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => CFC.sqrt (A.transpose * A)) :=
    CFC.measurable_sqrt.comp hg
  have hi : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
      (CFC.sqrt (A.transpose * A))⁻¹) := cavity_matrix_inverse_measurable.comp hs
  unfold cavityNormalizeFrame
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
    ∑ k, A i k * ((CFC.sqrt (A.transpose * A))⁻¹) k j)
  exact Finset.measurable_sum _ (fun k _ =>
    (Matrix.measurable_apply (i := i) (j := k)).mul (hi.eval_matrix))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCouplingAlgebra
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal spectral directions in the finite cavity coupling.
Each spectral image of the cavity columns is normalized separately.
The resulting frame carries the small square-root stack isometrically
back to the original cavity columns. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityEigenspaceFrame (r m n : ℕ) :
    Measurable (cavityEigenspaceFrame :
      (Fin m → Matrix (Fin r) (Fin n) ℝ) → Matrix (Fin r) (Fin (m * n)) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_cavityNormalizeFrame r n).comp
    (measurable_pi_apply (finProdFinEquiv.symm j).1)).eval_matrix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTests
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded-test cutoff removal, including a zero restricted normalizer,
and the good-compression/bad-compression split for the full-system tail. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem cavity_conditioning_bound_all {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) (hs : MeasurableSet s)
    (f : X → ℝ) (hf : Integrable f μ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ| ≤ 2 * M * (1 - μ.real s) := by
  by_cases hz : μ s = 0
  · rw [cond_eq_zero_of_meas_eq_zero hz, integral_zero_measure, zero_sub, abs_neg]
    have hi := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    have hr : μ.real s = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    rw [hr]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      hi.trans (by simpa only [probReal_univ, mul_one] using (show M ≤ 2 * M * (1 - 0) by linarith))
  · exact cavity_conditioning_bound μ s hs
      (ENNReal.toReal_pos hz (measure_ne_top μ s)) f hf M hb

/-- Restricting both replicas changes a bounded test by at most four
times its bound times the discarded one-replica mass. -/
theorem cavity_twoReplica_cutoff_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) (hs : MeasurableSet s)
    (f : (Fin 2 → X) → ℝ) (hf : Integrable f (Measure.pi (fun _ : Fin 2 => μ)))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond (Measure.pi (fun _ : Fin 2 => μ)) (univ.pi (fun _ => s))) -
      ∫ x, f x ∂Measure.pi (fun _ : Fin 2 => μ)| ≤ 4 * M * μ.real sᶜ := by
  have hmass : (Measure.pi (fun _ : Fin 2 => μ)).real (univ.pi (fun _ => s)) =
      (μ.real s) ^ 2 := by
    simp only [Measure.real, Measure.pi_pi, Fin.prod_univ_two, ENNReal.toReal_mul, pow_two]
  have ht := cavity_conditioning_bound_all (Measure.pi (fun _ : Fin 2 => μ))
    (univ.pi (fun _ => s)) (MeasurableSet.univ_pi (fun _ => hs)) f hf hM hb
  rw [hmass] at ht
  rw [measureReal_compl hs, probReal_univ]
  refine ht.trans ?_
  have hp : 0 ≤ μ.real s := measureReal_nonneg
  have hp1 : μ.real s ≤ 1 := measureReal_le_one
  nlinarith [mul_nonneg hM (sq_nonneg (1 - μ.real s))]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPermutation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral reorderings can be realized inside SO(N). A single row sign
corrects a permutation determinant without changing any squared projection. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma spectralPermutation_coordinate_sq {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (specialRotation (spectralPermutation hN p * U) x i) ^ 2 =
      (specialRotation U x (p i)) ^ 2 := by
  have he : specialRotation (spectralPermutation hN p * U) x i =
      (if i = (⟨0, hN⟩ : Fin N) then (p.permMatrix ℝ).det else 1) *
        specialRotation U x (p i) := by
    change (((permutationSignDiagonal hN p * p.permMatrix ℝ) *
      (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x.ofLp) i = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
    simp only [permutationSignDiagonal, Matrix.mulVec_diagonal,
      Function.comp_apply, specialRotation_apply]
    rfl
  rw [he, mul_pow]
  split_ifs
  · rw [permutationMatrix_det_sq, one_mul]
  · rw [one_pow, one_mul]

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma measurable_cavityFullDisorderInner {N m depth : ℕ}
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) => referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig (specialRotation p.1) x.1 +
        cylinderField (cavityPerturbationCoefficients (specialRotation p.1) I u depth x) p.2)
      (F p.1)) := by
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
  change Measurable (fun p => referenceReplicaMean ν (fun x => H (p, x)) (F p.1))
  exact measurable_referenceReplicaMean ν (H := H) (D := fun z => F z.1.1 z.2)
    hmH (hFm.comp (measurable_fst.fst.prodMk measurable_snd))

theorem cavity_full_disorder_site_symmetry {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (p : Equiv.Perm (Fin N))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
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
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let e := cavitySignedSpinPermutation p (cavityPermutationFlip hN p)
  let H := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    rotatedEnergy eig (specialRotation U) x.1
  let C := fun (U : SpecialOrthogonal N) (x : Spin N × LabeledLeaf depth) =>
    cavityPerturbationCoefficients (specialRotation U) I u depth x
  have hmean : Measurable (fun U => ∫ g, referenceReplicaMean ν
      (fun x => H U x + cylinderField (C U x) g) (F U) ∂gaussianCoordinates) :=
    (measurable_cavityFullDisorderInner T eig I u F hFm).stronglyMeasurable.integral_prod_right'.measurable
  apply cavity_twoReplica_disorder_symmetry μ
    (fun U => U * (spectralPermutation hN p)⁻¹)
    (measurePreserving_mul_right μ _) ν (fun x => (e x.1, x.2))
    (labeledSpinReference_equiv e T) H C
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma cavityFullDisorderTest_abs_le {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hFm : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) :
    |cavityFullDisorderTest μ T eig I u F| ≤ B := by
  exact cavity_nested_disorder_abs_le μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_cavityFullDisorderInner T eig I u F hFm) hB hF

lemma cavityFullDisorderTest_sum {N m depth : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : ι → SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : ∀ i, Measurable (Function.uncurry (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i U σ, |F i U σ| ≤ B) :
    cavityFullDisorderTest μ T eig I u (fun U σ => ∑ i, F i U σ) =
      ∑ i, cavityFullDisorderTest μ T eig I u (F i) := by
  exact cavity_nested_disorder_replica_sum μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ _ => measurable_of_countable _)
    (fun i => measurable_cavityFullDisorderInner T eig I u (F i) (hmF i)) hB hF

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical spectral projections and their exact signed-site action. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_specialRotation_one {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    specialRotation (1 : SpecialOrthogonal N) x = x := by
  ext i
  change ((1 : Matrix (Fin N) (Fin N) ℝ) *ᵥ x.ofLp) i = x i
  simp

lemma cavity_specialRotation_symm {N : ℕ} (U : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) :
    (specialRotation U).symm x = specialRotation U⁻¹ x := by
  apply (specialRotation U).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← cavity_specialRotation_mul_apply,
    mul_inv_cancel, cavity_specialRotation_one]

lemma cavitySpectralProjection_norm_sq_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ‖cavitySpectralProjection U I x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [cavitySpectralProjection, U.symm.norm_map, ← U.norm_map x,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro k _
  change (if k ∈ I then U x k else 0) ^ 2 ≤ (U x k) ^ 2
  split_ifs <;> simp [sq_nonneg]

lemma cavitySpectralProjection_site_sq_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (σ : Spin N) (j : Fin N) :
    (cavitySpectralProjection U I (spinVector σ) j) ^ 2 ≤ N := by
  calc
    _ ≤ ‖cavitySpectralProjection U I (spinVector σ)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ‖spinVector σ‖ ^ 2 := cavitySpectralProjection_norm_sq_le U I _
    _ = N := spinVector_norm_sq σ

lemma cavitySpectralProjection_permutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (I : Finset (Fin N))
    (σ : Spin N) :
    cavitySpectralProjection (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) =
    specialRotation (spectralPermutation hN p)
      (cavitySpectralProjection (specialRotation U) I (spinVector σ)) := by
  apply (specialRotation (U * (spectralPermutation hN p)⁻¹)).injective
  rw [cavitySpectralProjection, LinearIsometryEquiv.apply_symm_apply,
    cavityPermutationSpin_cancel, ← cavity_specialRotation_mul_apply,
    inv_mul_cancel_right]
  simp only [cavitySpectralProjection, LinearIsometryEquiv.apply_symm_apply]

lemma cavitySpectralProjection_permutation_sq {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (I : Finset (Fin N))
    (σ : Spin N) (j : Fin N) :
    (cavitySpectralProjection (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) j) ^ 2 =
    (cavitySpectralProjection (specialRotation U) I (spinVector σ) (p j)) ^ 2 := by
  rw [cavitySpectralProjection_permutation]
  have h := spectralPermutation_coordinate_sq hN p (1 : SpecialOrthogonal N)
    (cavitySpectralProjection (specialRotation U) I (spinVector σ)) j
  simpa only [mul_one, cavity_specialRotation_one] using h

lemma measurable_cavitySpectralProjection_site {N : ℕ}
    (I : Finset (Fin N)) (σ : Spin N) (j : Fin N) :
    Measurable (fun U : SpecialOrthogonal N =>
      cavitySpectralProjection (specialRotation U) I (spinVector σ) j) := by
  simp only [cavitySpectralProjection, cavity_specialRotation_symm, specialRotation_apply]
  apply Finset.measurable_sum
  intro k _
  have hentry : Measurable (fun U : SpecialOrthogonal N =>
      ((U⁻¹ : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ) j k) := by
    change Measurable (fun U : SpecialOrthogonal N => (U : Matrix (Fin N) (Fin N) ℝ) k j)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  apply hentry.mul
  by_cases hk : k ∈ I
  · simpa only [hk, ite_true, if_true, specialRotation_apply] using
      measurable_specialRotation_eval (spinVector σ) k
  · simp only [hk, ite_false, if_false]
    exact measurable_const

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullProjectionMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full perturbed Gibbs law has at most unit mean squared
spectral projection at every physical site. No cutoff is imposed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_cavityProjectionSiteTest {N depth : ℕ}
    (J : Finset (Fin N)) (j : Fin N) :
    Measurable (Function.uncurry (cavityProjectionSiteTest (depth := depth) J j)) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (measurable_cavitySpectralProjection_site J (σ 0).1 j).pow_const 2

lemma cavityProjectionSiteTest_bound {N depth : ℕ}
    (J : Finset (Fin N)) (j : Fin N) (U : SpecialOrthogonal N)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    |cavityProjectionSiteTest J j U σ| ≤ N := by
  rw [cavityProjectionSiteTest, abs_sq]
  exact cavitySpectralProjection_site_sq_le _ J _ j

theorem cavity_full_projection_site_mean_le_one {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2)
    (J : Finset (Fin N)) (j : Fin N) :
    cavityFullDisorderTest μ T eig I u (cavityProjectionSiteTest J j) ≤ 1 := by
  let F := cavityProjectionSiteTest (depth := depth) J
  let a := fun i => cavityFullDisorderTest μ T eig I u (F i)
  have he (i : Fin N) : a i = a j := by
    have ht := cavity_full_disorder_site_symmetry hN μ T eig I u hu (Equiv.swap i j)
      (F i) (measurable_cavityProjectionSiteTest J i) (Nat.cast_nonneg N)
      (cavityProjectionSiteTest_bound J i)
    change a i = cavityFullDisorderTest μ T eig I u _ at ht
    have hf : (fun U σ => F i (U * (spectralPermutation hN (Equiv.swap i j))⁻¹)
        (fun k => (cavitySignedSpinPermutation (Equiv.swap i j)
          (cavityPermutationFlip hN (Equiv.swap i j)) (σ k).1, (σ k).2))) = F j := by
      funext U σ
      simp only [F, cavityProjectionSiteTest, cavitySpectralProjection_permutation_sq,
        Equiv.swap_apply_left]
    rw [hf] at ht
    exact ht
  have hsum : |cavityFullDisorderTest μ T eig I u (fun U σ => ∑ i, F i U σ)| ≤ N := by
    apply cavityFullDisorderTest_abs_le μ T eig I u _
      (Finset.measurable_sum _ fun i _ => measurable_cavityProjectionSiteTest J i)
      (Nat.cast_nonneg N)
    intro U σ
    have hs : (∑ i, F i U σ) =
        ‖cavitySpectralProjection (specialRotation U) J (spinVector (σ 0).1)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [hs, abs_sq]
    exact (cavitySpectralProjection_norm_sq_le _ J _).trans_eq (spinVector_norm_sq _)
  rw [cavityFullDisorderTest_sum μ T eig I u F
    (fun i => measurable_cavityProjectionSiteTest J i) (Nat.cast_nonneg N)
    (fun i => cavityProjectionSiteTest_bound J i)] at hsum
  change |∑ i, a i| ≤ N at hsum
  simp_rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hle := (le_abs_self ((N : ℝ) * a j)).trans hsum
  change a j ≤ 1
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-sided bounded test estimates, valid also at a zero normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_referenceReplicaMean_le_const {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hm : Measurable F) {B c : ℝ}
    (hb : ∀ σ, |F σ| ≤ B) (hc : 0 ≤ c) (hF : ∀ σ, F σ ≤ c) :
    referenceReplicaMean ν H F ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ => ν))
  · have hprod := hi.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hb σ)
    have hnum : (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) * F σ ∂Measure.pi (fun _ : Fin r => ν)) ≤
        c * ∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν) := by
      rw [← integral_const_mul]
      apply integral_mono hprod (hi.const_mul c)
      intro σ
      exact (mul_le_mul_of_nonneg_left (hF σ) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    have hz : 0 ≤ ∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    rcases hz.eq_or_lt with hz | hz
    · rw [← hz, div_zero]
      exact hc
    · exact (div_le_iff₀ hz).mpr hnum
  · rw [integral_undef hi, div_zero]
    exact hc

lemma cavity_nested_disorder_upper {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : Ω → (Fin r → X) → ℝ) (hmF : ∀ ω, Measurable (F ω))
    (hmeas : Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F z.1)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω σ, |F ω σ| ≤ B)
    (c : Ω → ℝ) (hc : Integrable c μ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hFc : ∀ ω σ, F ω σ ≤ c ω) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P ∂μ) ≤ ∫ ω, c ω ∂μ := by
  have hib (ω : Ω) : Integrable (fun g => referenceReplicaMean ν (H ω g) (F ω)) P :=
    integrable_of_measurable_abs_le (hmeas.comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω))
  have hi : Integrable (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F ω) ∂P) μ :=
    integrable_of_measurable_abs_le hmeas.stronglyMeasurable.integral_prod_right'.measurable
      (fun ω => abs_integral_le_const_of_bound (hmeas.comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F ω) (hmF ω) hB (hF ω)))
  apply integral_mono hi hc
  intro ω
  calc
    _ ≤ ∫ _ : Ω', c ω ∂P := integral_mono (hib ω) (integrable_const _)
      (fun g => cavity_referenceReplicaMean_le_const ν (H ω g) (F ω) (hmF ω)
        (hF ω) (hc0 ω) (hFc ω))
    _ = c ω := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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

lemma cavityFullDisorderTest_const_mul {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) (c : ℝ) :
    cavityFullDisorderTest μ T eig I u (fun U σ => c * F U σ) =
      c * cavityFullDisorderTest μ T eig I u F := by
  simp only [cavityFullDisorderTest, referenceReplicaMean_const_mul, integral_const_mul]

lemma cavityFullDisorderTest_sub {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F G : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) (hmG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B) (hG : ∀ U σ, |G U σ| ≤ B) :
    cavityFullDisorderTest μ T eig I u (fun U σ => F U σ - G U σ) =
      cavityFullDisorderTest μ T eig I u F - cavityFullDisorderTest μ T eig I u G := by
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
  have hs := cavityFullDisorderTest_sum μ T eig I u H hmH hB hH
  simp only [Fin.sum_univ_two] at hs
  change cavityFullDisorderTest μ T eig I u (fun U σ => F U σ + (-1 : ℝ) * G U σ) =
    cavityFullDisorderTest μ T eig I u F +
      cavityFullDisorderTest μ T eig I u (fun U σ => (-1 : ℝ) * G U σ) at hs
  rw [cavityFullDisorderTest_const_mul] at hs
  simpa only [neg_one_mul, sub_eq_add_neg] using hs

lemma cavityFullDisorderTest_le_envelope {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F)) {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ U σ, |F U σ| ≤ B)
    (c : SpecialOrthogonal N → ℝ) (hc : Integrable c μ)
    (hc0 : ∀ U, 0 ≤ c U) (hFc : ∀ U σ, F U σ ≤ c U) :
    cavityFullDisorderTest μ T eig I u F ≤ ∫ U, c U ∂μ := by
  exact cavity_nested_disorder_upper μ gaussianCoordinates
    (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (fun U g x => rotatedEnergy eig (specialRotation U) x.1 +
      cylinderField (cavityPerturbationCoefficients (specialRotation U) I u depth x) g)
    F (fun _ => measurable_of_countable _)
    (measurable_cavityFullDisorderInner T eig I u F hmF) hB hF c hc hc0 hFc

lemma measurable_cavityProjectionAxesTest {N m k depth : ℕ}
    (I : Fin m → Finset (Fin N)) (axes : Fin k → Fin N) :
    Measurable (Function.uncurry (cavityProjectionAxesTest (depth := depth) I axes)) :=
  Finset.measurable_sum _ fun t _ => measurable_cavityProjectionSiteTest (I t.1) (axes t.2)

lemma cavityProjectionAxesTest_nonneg {N m k depth : ℕ}
    (I : Fin m → Finset (Fin N)) (axes : Fin k → Fin N)
    (U : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    0 ≤ cavityProjectionAxesTest I axes U σ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma cavityProjectionAxesTest_bound {N m k depth : ℕ}
    (I : Fin m → Finset (Fin N)) (axes : Fin k → Fin N)
    (U : SpecialOrthogonal N) (σ : Fin 2 → Spin N × LabeledLeaf depth) :
    |cavityProjectionAxesTest I axes U σ| ≤ (m : ℝ) * k * N := by
  rw [abs_of_nonneg (cavityProjectionAxesTest_nonneg I axes U σ)]
  calc
    _ ≤ ∑ _ : Fin m × Fin k, (N : ℝ) :=
      Finset.sum_le_sum fun t _ => cavitySpectralProjection_site_sq_le _ _ _ _
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]

lemma cavity_full_projection_axes_mean {N m k depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (axes : Fin k → Fin N) :
    cavityFullDisorderTest μ T eig I u (cavityProjectionAxesTest I axes) ≤ (m : ℝ) * k := by
  change cavityFullDisorderTest μ T eig I u
    (fun U σ => ∑ t : Fin m × Fin k, cavityProjectionSiteTest (I t.1) (axes t.2) U σ) ≤ _
  rw [cavityFullDisorderTest_sum μ T eig I u
    (fun t : Fin m × Fin k => cavityProjectionSiteTest (I t.1) (axes t.2))
    (fun t => measurable_cavityProjectionSiteTest (I t.1) (axes t.2))
    (Nat.cast_nonneg N) (fun t => cavityProjectionSiteTest_bound (I t.1) (axes t.2))]
  calc
    _ ≤ ∑ _ : Fin m × Fin k, (1 : ℝ) := Finset.sum_le_sum fun t _ =>
      cavity_full_projection_site_mean_le_one hN μ T eig I u hu (I t.1) (axes t.2)
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul]

theorem cavity_full_radial_cutoff {N m k d depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (axes : Fin k → Fin N) (good : Set (SpecialOrthogonal N))
    (hgood : MeasurableSet good)
    (y : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) →
      EuclideanSpace ℝ (Fin d))
    (φ : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmφ : Measurable (Function.uncurry φ)) (hφ : ∀ U σ, 0 ≤ φ U σ ∧ φ U σ ≤ 1)
    {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hzero : ∀ U σ, ‖y U σ‖ ≤ B → φ U σ = 0)
    (hgeometry : ∀ U ∈ good, ∀ σ,
      c * ‖y U σ‖ ^ 2 ≤ cavityProjectionAxesTest I axes U σ) :
    cavityFullDisorderTest μ T eig I u φ ≤
      μ.real goodᶜ + ((m : ℝ) * k) / (c * B ^ 2) := by
  let R := cavityProjectionAxesTest (depth := depth) I axes
  let C := (c * B ^ 2)⁻¹
  have hden : 0 < c * B ^ 2 := mul_pos hc (sq_pos_of_pos hB)
  have hC : 0 ≤ C := inv_nonneg.mpr hden.le
  have hmR : Measurable (Function.uncurry R) := measurable_cavityProjectionAxesTest I axes
  have hR0 : ∀ U σ, 0 ≤ R U σ := cavityProjectionAxesTest_nonneg I axes
  have hRb : ∀ U σ, |R U σ| ≤ (m : ℝ) * k * N := cavityProjectionAxesTest_bound I axes
  have hφb : ∀ U σ, |φ U σ| ≤ 1 := fun U σ => by
    rw [abs_of_nonneg (hφ U σ).1]
    exact (hφ U σ).2
  have hdom : ∀ U ∈ good, ∀ σ, φ U σ ≤ C * R U σ := by
    intro U hU σ
    by_cases hy : ‖y U σ‖ ≤ B
    · rw [hzero U σ hy]
      exact mul_nonneg hC (hR0 U σ)
    · have hsq : B ^ 2 ≤ ‖y U σ‖ ^ 2 :=
        (sq_le_sq₀ hB.le (norm_nonneg _)).mpr (le_of_not_ge hy)
      have hprod : c * B ^ 2 ≤ R U σ :=
        (mul_le_mul_of_nonneg_left hsq hc.le).trans (hgeometry U hU σ)
      apply (hφ U σ).2.trans
      dsimp only [C]
      rw [← div_eq_inv_mul, le_div_iff₀ hden, one_mul]
      exact hprod
  let M := 1 + C * ((m : ℝ) * k * N)
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hφM : ∀ U σ, |φ U σ| ≤ M := by
    intro U σ
    apply (hφb U σ).trans
    dsimp only [M]
    exact le_add_of_nonneg_right (mul_nonneg hC (by positivity))
  have hCRM : ∀ U σ, |C * R U σ| ≤ M := by
    intro U σ
    rw [abs_mul, abs_of_nonneg hC]
    exact (mul_le_mul_of_nonneg_left (hRb U σ) hC).trans (by dsimp [M] <;> linarith)
  have hDb : ∀ U σ, |φ U σ - C * R U σ| ≤ 1 + C * ((m : ℝ) * k * N) := by
    intro U σ
    calc
      _ ≤ |φ U σ| + |C * R U σ| := abs_sub _ _
      _ ≤ 1 + C * ((m : ℝ) * k * N) := by
        rw [abs_mul, abs_of_nonneg hC]
        exact add_le_add (hφb U σ) (mul_le_mul_of_nonneg_left (hRb U σ) hC)
  have hbad : Integrable (goodᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hgood.compl
  have hpoint : ∀ U σ, φ U σ - C * R U σ ≤ goodᶜ.indicator (fun _ => (1 : ℝ)) U := by
    intro U σ
    by_cases hU : U ∈ good
    · simpa only [Set.indicator_of_notMem (show U ∉ goodᶜ from fun hn => hn hU)] using
        sub_nonpos.mpr (hdom U hU σ)
    · rw [Set.indicator_of_mem hU]
      exact sub_le_iff_le_add.mpr ((hφ U σ).2.trans (le_add_of_nonneg_right (mul_nonneg hC (hR0 U σ))))
  have ht := cavityFullDisorderTest_le_envelope μ T eig I u
    (fun U σ => φ U σ - C * R U σ) (hmφ.sub (hmR.const_mul C))
    hM hDb (goodᶜ.indicator (fun _ => (1 : ℝ))) hbad
    (fun U => Set.indicator_nonneg (fun _ _ => zero_le_one) U) hpoint
  rw [cavityFullDisorderTest_sub μ T eig I u φ (fun U σ => C * R U σ)
    hmφ (hmR.const_mul C) hM hφM hCRM, cavityFullDisorderTest_const_mul,
    integral_indicator hgood.compl, setIntegral_const, smul_eq_mul, mul_one] at ht
  have hmean := cavity_full_projection_axes_mean hN μ T eig I u hu axes
  have hscale := mul_le_mul_of_nonneg_left hmean hC
  have he : C * ((m : ℝ) * k) = ((m : ℝ) * k) / (c * B ^ 2) := by
    simp only [C, div_eq_mul_inv, mul_comm]
  rw [he] at hscale
  dsimp only [R] at ht
  linarith

theorem cavity_full_tail_probability {N m k d depth : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (axes : Fin k → Fin N) (good : Set (SpecialOrthogonal N))
    (hgood : MeasurableSet good)
    (y : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) →
      EuclideanSpace ℝ (Fin d)) (hmy : Measurable (Function.uncurry y))
    {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hgeometry : ∀ U ∈ good, ∀ σ,
      c * ‖y U σ‖ ^ 2 ≤ cavityProjectionAxesTest I axes U σ) :
    cavityFullDisorderTest μ T eig I u (fun U σ => if B < ‖y U σ‖ then 1 else 0) ≤
      μ.real goodᶜ + ((m : ℝ) * k) / (c * B ^ 2) := by
  apply cavity_full_radial_cutoff hN μ T eig I u hu axes good hgood y
  · exact Measurable.ite (measurableSet_lt measurable_const hmy.norm)
      measurable_const measurable_const
  · intro U σ
    split_ifs <;> norm_num
  · exact hc
  · exact hB
  · intro U σ hy
    simp only [not_lt.mpr hy, ite_false, if_false]
  · exact hgeometry

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralImages
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separate spectral images of the cavity columns. These are the
concrete inputs to the normalized-frame coupling construction. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavitySpectralImage {r m n : ℕ} (g : Fin r → Fin m) (a : Fin m) :
    Measurable (fun A : Matrix (Fin r) (Fin n) ℝ => cavitySpectralImage g A a) := by
  apply Measurable.of_eval_matrix
  intro i j
  by_cases h : g i = a
  · simpa only [cavitySpectralImage, h, ite_true, if_true] using
      (Matrix.measurable_apply (i := i) (j := j))
  · simpa only [cavitySpectralImage, h, ite_false, if_false] using
      (measurable_const : Measurable (fun _ : Matrix (Fin r) (Fin n) ℝ => (0 : ℝ)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPhysicalBase
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable base interaction built from the actual cavity columns. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityColumns (N n : ℕ) :
    Measurable (cavityColumns : Orthogonal (N + n) → Matrix (Fin (N + n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_apply (i := i) (j := Fin.natAdd N j)).comp measurable_subtype_coe

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic control of the special coordinates by the unnormalized
spectral images. Only the inverse square-root norms on the good event enter. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_frame_transpose_contraction {r d : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 (B.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have ho : Orthonormal ℝ (fun i : Fin d =>
      (WithLp.toLp 2 (fun j : Fin r => B j i) : EuclideanSpace ℝ (Fin r))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      mul_comm] using h
  have hb := ho.sum_inner_products_le (s := Finset.univ) z
  simpa only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, PiLp.toLp_apply, Matrix.mulVec, Matrix.transpose_apply,
    Real.norm_eq_abs, sq_abs, mul_comm] using hb

lemma cavity_normalized_image_norm {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin r))
    {L : ℝ} (hL : 0 ≤ L) (hbound : ‖(CFC.sqrt (A.transpose * A))⁻¹‖ ≤ L) :
    ‖(WithLp.toLp 2 ((cavityNormalizeFrame A).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
    L ^ 2 * ‖(WithLp.toLp 2 (A.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  let S := (CFC.sqrt (A.transpose * A))⁻¹
  have hSt : ‖S.transpose‖ ≤ L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose S).le.trans hbound
  have hn := (Matrix.l2_opNorm_mulVec S.transpose
    (WithLp.toLp 2 (A.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))).trans
    (mul_le_mul_of_nonneg_right hSt (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr hn
  simpa only [cavityNormalizeFrame, Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    mul_pow, S, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv] using hs

lemma cavity_eigenspace_projection_norm {r m n : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame A).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 =
    ∑ a, ‖(WithLp.toLp 2 ((cavityNormalizeFrame (A a)).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin (m * n), (∑ j : Fin r,
      cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j (finProdFinEquiv.symm i).2 * z j) ^ 2) =
    ∑ a, ∑ i : Fin n, (∑ j : Fin r, cavityNormalizeFrame (A a) j i * z j) ^ 2
  calc
    _ = ∑ t : Fin m × Fin n, (∑ j : Fin r,
        cavityNormalizeFrame (A t.1) j t.2 * z j) ^ 2 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp finProdFinEquiv
          (fun i : Fin (m * n) => (∑ j : Fin r,
            cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j
              (finProdFinEquiv.symm i).2 * z j) ^ 2)).symm
    _ = _ := Fintype.sum_prod_type _

theorem cavity_special_projection_control {r m n d : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a, ‖(CFC.sqrt ((A a).transpose * A a))⁻¹‖ ≤ L) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame A * B).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
    L ^ 2 * ∑ a, ‖(WithLp.toLp 2 ((A a).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  apply (cavity_frame_transpose_contraction B hB
    (WithLp.toLp 2 ((cavityEigenspaceFrame A).transpose *ᵥ z.ofLp))).trans
  rw [cavity_eigenspace_projection_norm, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => cavity_normalized_image_norm (A a) z hL (hbound a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unnormalized cavity-column projections are precisely physical
spectral projections at the added sites. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_spectral_image_projection {N n m : ℕ}
    (g : Fin (N + n) → Fin m) (U : SpecialOrthogonal (N + n))
    (x : EuclideanSpace ℝ (Fin (N + n))) (a : Fin m) (j : Fin n) :
    ((cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U)) a).transpose *ᵥ
      (specialRotation U x).ofLp) j =
    cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a) x (Fin.natAdd N j) := by
  rw [cavitySpectralProjection, cavity_specialRotation_symm]
  change (∑ i : Fin (N + n),
    (if g i = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) else 0) *
      specialRotation U x i) =
    ∑ i : Fin (N + n),
      (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) i (Fin.natAdd N j) *
        (if i ∈ cavitySpectralGroup g a then specialRotation U x i else 0)
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : g i = a <;> simp [cavitySpectralGroup, hi]

theorem cavity_full_special_coordinates_control {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1) (U : SpecialOrthogonal (N + n))
    (σ : Spin (N + n)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    ‖cavityFullSpecialCoordinates g B U σ‖ ^ 2 ≤ L ^ 2 *
      ∑ a, ∑ j : Fin n,
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a)
          (spinVector σ) (Fin.natAdd N j)) ^ 2 := by
  have h := cavity_special_projection_control
    (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) B hB
    (specialRotation U (spinVector σ)) hL hbound
  simpa only [cavityFullSpecialCoordinates, EuclideanSpace.real_norm_sq_eq,
    PiLp.toLp_apply, cavity_spectral_image_projection] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGeometricTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-model cutoff estimate for the actual normalized spectral
image construction, with no inverse-Gram estimate on the bad event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurable_cavityFullSpecialCoordinates {N n m d : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (σ : Spin (N + n)) :
    Measurable (fun U => cavityFullSpecialCoordinates g (B U) U σ) := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hA : Measurable (fun U : SpecialOrthogonal (N + n) =>
      cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) :=
    measurable_pi_iff.mpr fun a => ((measurable_cavitySpectralImage g a).comp
      (measurable_cavityColumns N n)).comp hO
  have hW := (measurable_cavityEigenspaceFrame (N + n) m n).comp hA
  have hmul : Continuous (fun p : Matrix (Fin (N + n)) (Fin (m * n)) ℝ ×
      Matrix (Fin (m * n)) (Fin d) ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hV := hmul.measurable.comp (hW.prodMk hB)
  have hz : Measurable (fun U : SpecialOrthogonal (N + n) =>
      ((cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U).transpose *ᵥ (specialRotation U (spinVector σ)).ofLp)) := by
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun U : SpecialOrthogonal (N + n) => ∑ i : Fin (N + n),
      (cavityEigenspaceFrame (cavitySpectralImage g (cavityColumns (cavitySpecialOrthogonal U))) *
        B U) i j * specialRotation U (spinVector σ) i)
    apply Finset.measurable_sum
    intro i _
    exact hV.eval_matrix.mul (measurable_specialRotation_eval (spinVector σ) i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.measurable).comp hz

theorem cavity_full_geometric_tail {N n m d depth : ℕ} (hN : 0 < N + n)
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (hB : ∀ U, (B U).transpose * B U = 1)
    (good : Set (SpecialOrthogonal (N + n))) (hgood : MeasurableSet good)
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hbound : ∀ U ∈ good, ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L) :
    cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u
      (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) ≤
    μ.real goodᶜ + L ^ 2 * ((m : ℝ) * n) / R ^ 2 := by
  let y := fun (U : SpecialOrthogonal (N + n))
    (σ : Fin 2 → Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B U) U (σ 0).1
  have hmy : Measurable (Function.uncurry y) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact measurable_cavityFullSpecialCoordinates g B hmB (σ 0).1
  have hgeom : ∀ U ∈ good, ∀ σ,
      (L ^ 2)⁻¹ * ‖y U σ‖ ^ 2 ≤
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
    intro U hU σ
    have h := cavity_full_special_coordinates_control g (B U) (hB U) U (σ 0).1 hL.le (hbound U hU)
    have he : (∑ a, ∑ j : Fin n,
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g a)
          (spinVector (σ 0).1) (Fin.natAdd N j)) ^ 2) =
        cavityProjectionAxesTest (cavitySpectralGroup g) (Fin.natAdd N) U σ := by
      exact (Fintype.sum_prod_type (fun t : Fin m × Fin n =>
        (cavitySpectralProjection (specialRotation U) (cavitySpectralGroup g t.1)
          (spinVector (σ 0).1) (Fin.natAdd N t.2)) ^ 2)).symm
    rw [he] at h
    exact (inv_mul_le_iff₀ (sq_pos_of_pos hL)).mpr h
  have ht := cavity_full_tail_probability hN μ T eig (cavitySpectralGroup g) u hu
    (Fin.natAdd N) good hgood y hmy (inv_pos.mpr (sq_pos_of_pos hL)) hR hgeom
  have hid : ((m : ℝ) * n) / ((L ^ 2)⁻¹ * R ^ 2) =
      L ^ 2 * ((m : ℝ) * n) / R ^ 2 := by
    field_simp
  simpa only [hid, y] using ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityReplicaCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma measurable_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω)
      (fun σ => F (ω, σ))) := by
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (measurable_referenceReplicaMean ν (H := H) hH
    (Measurable.ite hS hF measurable_const)).div
      (measurable_referenceReplicaMean ν (H := H) hH
        (Measurable.ite hS measurable_const measurable_const))

lemma cavity_cutoff_replica_eq_cond {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      ∫ σ, F σ ∂cond (Measure.pi (fun _ : Fin 2 => ν.tilted H))
        (univ.pi (fun _ => s)) := by
  let P := Measure.pi (fun _ : Fin 2 => ν.tilted H)
  let S := univ.pi (fun _ : Fin 2 => s)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hnum : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then F σ else 0) = S.indicator F := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  have hden : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then (1 : ℝ) else 0) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  rw [cavityCutoffReplicaMean, referenceReplicaMean_eq_tilted ν H hH,
    referenceReplicaMean_eq_tilted ν H hH, hnum, hden]
  change (∫ σ, S.indicator F σ ∂P) / (∫ σ, S.indicator (fun _ => (1 : ℝ)) σ ∂P) = _
  rw [integral_indicator hS, integral_indicator hS, integral_const]
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_inv, Measure.real, Measure.restrict_apply_univ, mul_one, div_eq_inv_mul]
  rfl

theorem cavity_cutoff_replica_error {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F - referenceReplicaMean ν H F| ≤
      4 * M * (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted hH
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F, referenceReplicaMean_eq_tilted ν H hH]
  exact cavity_twoReplica_cutoff_bound (ν.tilted H) s hs F
    (Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable M
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hF σ)) hM hF

lemma cavity_reference_tail_eq {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) :
    referenceReplicaMean ν H (fun σ : Fin 2 → X => if σ 0 ∈ sᶜ then 1 else 0) =
      (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted hH
  rw [referenceReplicaMean_eq_tilted ν H hH]
  have he : (fun σ : Fin 2 → X => if σ 0 ∈ sᶜ then (1 : ℝ) else 0) =
      fun σ => (sᶜ).indicator (fun _ : X => (1 : ℝ)) (σ 0) := by
    funext σ
    simp only [indicator_apply]
  rw [he, integral_comp_eval]
  · rw [integral_indicator hs.compl, integral_const]
    simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  · exact (measurable_const.indicator hs.compl).aestronglyMeasurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A random cutoff changes bounded replica tests by its discarded
one-replica probability, after averaging over the common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F]
  have h := norm_integral_le_of_norm_le_const
    (μ := cond (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)))
    (f := F) (C := M) (ae_of_all _ (fun σ => by
      simpa only [Real.norm_eq_abs] using hF σ))
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hM measureReal_le_one)

theorem cavity_random_cutoff_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hmH : Measurable H)
    (hiH : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) ν)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hmF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ ω σ, |F (ω, σ)| ≤ M) :
    |(∫ ω, cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω) (fun σ => F (ω, σ)) ∂P) -
      (∫ ω, referenceReplicaMean ν (fun x => H (ω, x)) (fun σ => F (ω, σ)) ∂P)| ≤
      4 * M * ∫ ω, referenceReplicaMean ν (fun x => H (ω, x))
        (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then 1 else 0) ∂P := by
  have hms (ω : Ω) : MeasurableSet (s ω) := hs.preimage measurable_prodMk_left
  have hmcut := measurable_cavityCutoffReplicaMean ν H hmH s hs F hmF
  have hmfull := measurable_referenceReplicaMean ν (H := H) hmH hmF
  have hmTail : Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then (1 : ℝ) else 0)) := by
    apply measurable_referenceReplicaMean ν (H := H)
      (D := fun p : Ω × (Fin 2 → X) => if p.2 0 ∈ (s p.1)ᶜ then 1 else 0) hmH
    exact Measurable.ite ((hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).compl)
      measurable_const measurable_const
  have hic : Integrable (fun ω =>
      cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω) (fun σ => F (ω, σ))) P :=
    Integrable.of_bound hmcut.aestronglyMeasurable M (hiH.mono fun ω hω => by
      simpa only [Real.norm_eq_abs] using
        cavity_cutoff_replica_abs_le ν _ hω _ (hms ω) _ hM (hF ω))
  have hif : Integrable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ => F (ω, σ))) P := Integrable.of_bound hmfull.aestronglyMeasurable M
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs] using referenceReplicaMean_abs_le ν _ _
        (measurable_of_countable _) hM (hF ω))
  have hit : Integrable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then (1 : ℝ) else 0)) P :=
    Integrable.of_bound hmTail.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      apply referenceReplicaMean_abs_le ν _ _ (measurable_of_countable _) zero_le_one
      intro σ
      split_ifs <;> norm_num)
  rw [← integral_sub hic hif]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (hic.sub hif).norm (hit.const_mul _)
  filter_upwards [hiH] with ω hω
  rw [Real.norm_eq_abs, cavity_reference_tail_eq ν _ hω _ (hms ω)]
  exact cavity_cutoff_replica_error ν _ hω _ (hms ω) _ hM (hF ω)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
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

lemma cavity_full_exp_integrable_ae {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) :
    ∀ᵐ p ∂μ.prod gaussianCoordinates, Integrable
      (fun x => Real.exp (cavityFullHamiltonian eig I u p x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  apply (Measure.ae_prod_iff_ae_ae (_root_.measurableSet_integrable (μ := ν)
    (f := fun p x => Real.exp (cavityFullHamiltonian (depth := depth) eig I u p x))
    (measurable_cavityFullHamiltonian (depth := depth) eig I u).exp.stronglyMeasurable)).mpr
  exact ae_of_all _ fun U => cylinder_partition_exp_integrable_ae ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1)
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig (specialRotation U) σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)))
    (cavityPerturbationCoefficients (specialRotation U) I u depth)
    (cavityPerturbationCoefficients_sq_le _ I u hu)

theorem cavity_full_cutoff_error {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) | p.2 ∈ s p.1})
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig I u s F - cavityFullDisorderTest μ T eig I u F| ≤
      4 * M * cavityFullDisorderTest μ T eig I u
        (fun U σ => if σ 0 ∈ (s U)ᶜ then 1 else 0) := by
  let P := μ.prod gaussianCoordinates
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let H := cavityFullHamiltonian (depth := depth) eig I u
  let G : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → Spin N × LabeledLeaf depth) → ℝ :=
    fun p => F p.1.1 p.2
  let S := fun p : SpecialOrthogonal N × (ℕ → ℝ) => s p.1
  have hmH : Measurable (Function.uncurry H) := measurable_cavityFullHamiltonian eig I u
  have hmG : Measurable G := hmF.comp (measurable_fst.fst.prodMk measurable_snd)
  have hmS : MeasurableSet {p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) | p.2 ∈ S p.1} :=
    hs.preimage (measurable_fst.fst.prodMk measurable_snd)
  have hiH := cavity_full_exp_integrable_ae μ T eig I u hu
  have hmC := measurable_cavityCutoffReplicaMean ν (Function.uncurry H) hmH S hmS G hmG
  have hmR := measurable_referenceReplicaMean ν (H := Function.uncurry H) hmH hmG
  have hmTail : Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      referenceReplicaMean ν (H p) (fun σ : Fin 2 → Spin N × LabeledLeaf depth =>
        if σ 0 ∈ (S p)ᶜ then (1 : ℝ) else 0)) := by
    apply measurable_referenceReplicaMean ν (H := Function.uncurry H)
      (D := fun p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
        (Fin 2 → Spin N × LabeledLeaf depth) =>
        if p.2 0 ∈ (S p.1)ᶜ then 1 else 0) hmH
    exact Measurable.ite ((hmS.preimage
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).compl)
      measurable_const measurable_const
  have hms (p : SpecialOrthogonal N × (ℕ → ℝ)) : MeasurableSet (S p) :=
    hmS.preimage measurable_prodMk_left
  have hiC : Integrable (fun p => cavityCutoffReplicaMean ν (H p) (S p) (fun σ => G (p, σ))) P :=
    Integrable.of_bound hmC.aestronglyMeasurable M (hiH.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using
        cavity_cutoff_replica_abs_le ν _ hp _ (hms p) _ hM (hF p.1))
  have hiR : Integrable (fun p => referenceReplicaMean ν (H p) (fun σ => G (p, σ))) P :=
    integrable_of_measurable_abs_le hmR (fun p => referenceReplicaMean_abs_le ν _ _
      (measurable_of_countable _) hM (hF p.1))
  have hiTail : Integrable (fun p => referenceReplicaMean ν (H p)
      (fun σ : Fin 2 → Spin N × LabeledLeaf depth => if σ 0 ∈ (S p)ᶜ then 1 else 0)) P :=
    integrable_of_measurable_abs_le hmTail (fun p => referenceReplicaMean_abs_le ν _ _
      (measurable_of_countable _) zero_le_one (fun σ => by split_ifs <;> norm_num))
  have ht := cavity_random_cutoff_error P ν (Function.uncurry H) hmH hiH S hmS G hmG hM
    (fun p => hF p.1)
  dsimp only [P, Function.uncurry] at ht
  rw [integral_prod _ hiC, integral_prod _ hiR, integral_prod _ hiTail] at ht
  exact ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTightness
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the actual special-coordinate cutoff from bounded tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Classical Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma measurableSet_cavitySpecialCutoff {N n m d depth : ℕ}
    (g : Fin (N + n) → Fin m)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : Measurable B) (R : ℝ) :
    MeasurableSet {p : SpecialOrthogonal (N + n) × (Spin (N + n) × LabeledLeaf depth) |
      p.2 ∈ cavitySpecialCutoff g B R p.1} := by
  have hm : Measurable (fun p : SpecialOrthogonal (N + n) ×
      (Spin (N + n) × LabeledLeaf depth) =>
      cavityFullSpecialCoordinates g (B p.1) p.1 p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    exact measurable_cavityFullSpecialCoordinates g B hB x.1
  exact measurableSet_le hm.norm measurable_const

theorem cavity_full_special_cutoff_error {N n m d depth : ℕ}
    (μ : Measure (SpecialOrthogonal (N + n))) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin (N + n) → ℝ) (g : Fin (N + n) → Fin m)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (B : SpecialOrthogonal (N + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : Measurable B) (R : ℝ)
    (F : SpecialOrthogonal (N + n) → (Fin 2 → Spin (N + n) × LabeledLeaf depth) → ℝ)
    (hmF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig (cavitySpectralGroup g) u
        (cavitySpecialCutoff g B R) F - cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u F| ≤
      4 * M * cavityFullDisorderTest μ T eig (cavitySpectralGroup g) u
        (fun U σ => if R < ‖cavityFullSpecialCoordinates g (B U) U (σ 0).1‖ then 1 else 0) := by
  simpa only [cavitySpecialCutoff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using
    cavity_full_cutoff_error μ T eig (cavitySpectralGroup g) u hu
      (cavitySpecialCutoff g B R) (measurableSet_cavitySpecialCutoff g B hmB R) F hmF hM hF

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCutoffTotalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cutoff is bounded also when its partition integral
is undefined: the existing zero convention then gives zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le_all {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (s : Set X) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  by_cases hi : Integrable (fun x => Real.exp (H x)) ν
  · exact cavity_cutoff_replica_abs_le ν H hi s (Set.to_countable s).measurableSet F hM hF
  · have hz : referencePartition ν H = 0 := integral_undef hi
    simp only [cavityCutoffReplicaMean, referenceReplicaMean, hz, zero_pow (by decide : 2 ≠ 0),
      div_zero, abs_zero]
    exact hM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityRandomPriorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of a normalized cutoff when the labeled cascade prior
is part of the retained disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_random_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean (ν ω) (fun x => H (ω,x)) (s ω)
      (fun σ => F (ω,σ))) := by
  classical
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hn := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then F p else (0 : ℝ))
    (Measurable.ite hS hF measurable_const)
  have hd := measurable_random_referenceReplicaMean hν hH
    (D := fun p : Ω × (Fin 2 → X) => if ∀ i, p.2 i ∈ s p.1 then (1 : ℝ) else 0)
    (Measurable.ite hS measurable_const measurable_const)
  exact hn.div hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeCutoffMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original cutoff average is measurable in the actual labeled
tree. The Gaussian and rotation coordinates remain unchanged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma measurable_cavityFullCutoffDisorderTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (hs : MeasurableSet {p : SpecialOrthogonal N × (Spin N × LabeledLeaf depth) |
      p.2 ∈ s p.1})
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun T => cavityFullCutoffDisorderTest μ T eig I u s F) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.fst
  let H : Ω × X → ℝ := fun p => cavityFullHamiltonian eig I u (p.1.1.2,p.1.2) p.2
  have hH : Measurable H := by
    have hp : Measurable (fun p : Ω × X => ((p.1.1.2,p.1.2),p.2)) :=
      (measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd
    exact Measurable.comp
      (g := Function.uncurry (cavityFullHamiltonian (depth := depth) eig I u))
      (f := fun p : Ω × X => ((p.1.1.2,p.1.2),p.2))
      (measurable_cavityFullHamiltonian eig I u) hp
  have hS : MeasurableSet {p : Ω × X | p.2 ∈ s p.1.1.2} :=
    hs.preimage (measurable_fst.fst.snd.prodMk measurable_snd)
  have hG : Measurable (fun p : Ω × (Fin 2 → X) => F p.1.1.2 p.2) :=
    hF.comp (measurable_fst.fst.snd.prodMk measurable_snd)
  have hh := measurable_random_cavityCutoffReplicaMean ν hν H hH
    (fun p => s p.1.2) hS (fun p => F p.1.1.2 p.2) hG
  exact ((hh.stronglyMeasurable.integral_prod_right' (ν := gaussianCoordinates)).integral_prod_right'
    (ν := μ)).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityTreeFullRegular
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma measurable_cavityFullTest_tree {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [SFinite μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) :
    Measurable (fun T => cavityFullTest μ T eig I u F) := by
  let Ω := (LabeledTree depth × SpecialOrthogonal N) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.fst
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

lemma cavityFullCutoffDisorderTest_abs_le {N m depth : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (s : SpecialOrthogonal N → Set (Spin N × LabeledLeaf depth))
    (F : SpecialOrthogonal N → (Fin 2 → Spin N × LabeledLeaf depth) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ U σ, |F U σ| ≤ M) :
    |cavityFullCutoffDisorderTest μ T eig I u s F| ≤ M := by
  have hi U : ‖∫ z, cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) ∂gaussianCoordinates‖ ≤ M := by
    have hh := norm_integral_le_of_norm_le_const (μ := gaussianCoordinates)
      (f := fun z => cavityCutoffReplicaMean
        (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
        (cavityFullHamiltonian eig I u (U,z)) (s U) (F U))
      (C := M) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using cavity_cutoff_replica_abs_le_all
          (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
          (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) hM (hF U))
    simpa only [probReal_univ,mul_one] using hh
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun U => ∫ z, cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityFullHamiltonian eig I u (U,z)) (s U) (F U) ∂gaussianCoordinates)
    (C := M) (ae_of_all _ hi)
  simpa only [cavityFullCutoffDisorderTest,Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFullTreeCutoff
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the original special-coordinate cutoff after averaging
over the actual random tree, uniformly in its depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_full_tree_cutoff_sequence_oai {n m d : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k + n)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k + n) → ℝ)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (u : ℕ → ℕ → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (B : (k : ℕ) → SpecialOrthogonal (N k + n) → Matrix (Fin (m * n)) (Fin d) ℝ)
    (hmB : ∀ k, Measurable (B k)) (hB : ∀ k U, (B k U).transpose * B k U = 1)
    (good : (k : ℕ) → Set (SpecialOrthogonal (N k + n)))
    (hgood : ∀ k, MeasurableSet (good k))
    (hp : Tendsto (fun k => (μ k).real (good k)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ k U, U ∈ good k → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (F : (k : ℕ) → (Fin 2 → Spin (N k + n) × LabeledLeaf (depth k)) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ k σ, |F k σ| ≤ M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 < b j) (hblim : Tendsto b atTop atTop) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ k in atTop,
      |(∫ T, cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k) ∂θ k) -
        ∫ T, cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
          (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k) ∂θ k| < ε := by
  have he : Tendsto (fun k => (μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
    simpa only [measureReal_compl (hgood _),probReal_univ,sub_self] using ht
  have hscaled : Tendsto (fun k => 4*M*(μ k).real (good k)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (4*M)
  have hinv := tendsto_inv_atTop_zero.comp hblim
  have hrad : Tendsto (fun j => 4*M*L^2*((m:ℝ)*n)/(b j)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,inv_pow,zero_pow (by decide : 2 ≠ 0),mul_zero]
      using (hinv.pow 2).const_mul (4*M*L^2*((m:ℝ)*n))
  intro ε hε
  filter_upwards [hrad.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with j hj
  filter_upwards [hscaled.eventually (Iio_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with k hk
  let O := fun T : LabeledTree (depth k) =>
    cavityFullTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k) (F k)
  let C := fun T : LabeledTree (depth k) =>
    cavityFullCutoffDisorderTest (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      (cavitySpecialCutoff (g k) (B k) (b j)) (fun _ => F k)
  have hmF : Measurable (Function.uncurry (fun _ : SpecialOrthogonal (N k+n) => F k)) :=
    (measurable_of_countable (F k)).comp measurable_snd
  have hOm : Measurable O := measurable_cavityFullTest_tree _ _ _ _ _
  have hCm : Measurable C := measurable_cavityFullCutoffDisorderTest_tree _ _ _ _ _
    (measurableSet_cavitySpecialCutoff (g k) (B k) (hmB k) (b j)) _ hmF
  have hOi : Integrable O (θ k) := integrable_of_measurable_abs_le hOm (fun T =>
    cavityFullDisorderTest_abs_le (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      (fun _ => F k) hmF hM (fun _ => hF k))
  have hCi : Integrable C (θ k) := integrable_of_measurable_abs_le hCm (fun T =>
    cavityFullCutoffDisorderTest_abs_le (μ k) T (eig k) (cavitySpectralGroup (g k)) (u k)
      _ _ hM (fun _ => hF k))
  have hbound T : |O T-C T| ≤
      (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by
    have hcut := cavity_full_special_cutoff_error (μ k) T (eig k) (g k) (u k)
      (hu k) (B k) (hmB k) (b j) (fun _ => F k) hmF hM (fun _ => hF k)
    rw [abs_sub_comm] at hcut
    have htail := cavity_full_geometric_tail (hN k) (μ k) T (eig k) (g k)
      (u k) (hu k) (B k) (hmB k) (hB k) (good k) (hgood k) hL (hb j) (hbound k)
    have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ 4*M by positivity)
    have heq : 4*M*((μ k).real (good k)ᶜ + L^2*((m:ℝ)*n)/(b j)^2) =
        (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by ring
    rw [heq] at hmul
    exact hcut.trans hmul
  change |(∫ T, O T ∂θ k)-(∫ T, C T ∂θ k)| < ε
  rw [← integral_sub hOi hCi]
  have hh := norm_integral_le_of_norm_le_const (μ := θ k) (f := fun T => O T-C T)
    (C := (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2)
    (ae_of_all _ fun T => by simpa only [Real.norm_eq_abs] using hbound T)
  have hh' : |∫ T, O T-C T ∂θ k| ≤
      (4*M)*(μ k).real (good k)ᶜ + 4*M*L^2*((m:ℝ)*n)/(b j)^2 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
  exact hh'.trans_lt (by linarith)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_full_tree_cutoff_sequence_oai := @OAI.InvariantIsing.cavity_full_tree_cutoff_sequence_oai
