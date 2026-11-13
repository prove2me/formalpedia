-- Prove2me | solution 1 for OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:13:09.999427+00:00
-- url     : https://prove2.me/submissions/c1115d7f-88f8-4c1c-aeeb-fdb6c3ce3cb4

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_tensorGrowingArrayLaw_off_ward_limit

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

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

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

lemma integrable_linear_mul_replica {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => linearGaussian A g x*replicaGibbs w B C g σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_replicaGibbs hw B C σ).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  exact replicaGibbs_le_one hw B C g σ

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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Ward
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume Gibbs rotation identity

Differentiation of a normalized Gibbs average produces the observable
variation and its covariance with the Hamiltonian variation. Haar invariance
then gives their exact integral identity. The spin prior may have zero weights.
No limiting Ward equations or pressure bounds are assumed here.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

lemma abs_gibbsAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ σ, |A σ| ≤ K) :
    |gibbsAverage w H A| ≤ K := finiteGibbs_average_bound hw H A hA

lemma measurable_gibbsAverage {Ω : Type*} [MeasurableSpace Ω]
    (w : S → ℝ) (H A : Ω → S → ℝ)
    (hH : ∀ σ, Measurable (fun ω => H ω σ))
    (hA : ∀ σ, Measurable (fun ω => A ω σ)) :
    Measurable (fun ω => gibbsAverage w (H ω) (A ω)) := by
  unfold gibbsAverage finiteGibbs finitePartition
  exact Finset.measurable_sum _ fun σ _ =>
    ((measurable_const.mul (hH σ).exp).div
      (Finset.measurable_sum _ fun τ _ => measurable_const.mul (hH τ).exp)).mul (hA σ)

/-- Derivative of a finite Gibbs expectation: the variation of the observable
plus its Gibbs covariance with the variation of the Hamiltonian. -/
lemma hasDerivAt_gibbsAverage {w : S → ℝ} (hw : GibbsReference w)
    {H A : ℝ → S → ℝ} {dH dA : S → ℝ} {t : ℝ}
    (hH : ∀ σ, HasDerivAt (fun s => H s σ) (dH σ) t)
    (hA : ∀ σ, HasDerivAt (fun s => A s σ) (dA σ) t) :
    HasDerivAt (fun s => gibbsAverage w (H s) (A s))
      (gibbsAverage w (H t) dA +
        gibbsAverage w (H t) (fun σ => A t σ * dH σ) -
        gibbsAverage w (H t) (A t) * gibbsAverage w (H t) dH) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (hasDerivAt_finiteGibbs hw hH σ).mul (hA σ))
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [gibbsAverage]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring

lemma abs_gibbsVariation_le {w : S → ℝ} (hw : GibbsReference w)
    (H A dH dA : S → ℝ) {K L M : ℝ}
    (hK : 0 ≤ K)
    (hA : ∀ σ, |A σ| ≤ K) (hH : ∀ σ, |dH σ| ≤ L)
    (hdA : ∀ σ, |dA σ| ≤ M) :
    |gibbsAverage w H dA + gibbsAverage w H (fun σ => A σ * dH σ) -
      gibbsAverage w H A * gibbsAverage w H dH| ≤ M + 2 * K * L := by
  have ha := abs_gibbsAverage_le hw H A hA
  have hh := abs_gibbsAverage_le hw H dH hH
  have hda := abs_gibbsAverage_le hw H dA hdA
  have hprod := abs_gibbsAverage_le hw H (fun σ => A σ * dH σ) (fun σ => by
    rw [abs_mul]
    exact mul_le_mul (hA σ) (hH σ) (abs_nonneg _) hK)
  calc
    _ ≤ |gibbsAverage w H dA| + |gibbsAverage w H (fun σ => A σ * dH σ)| +
        |gibbsAverage w H A * gibbsAverage w H dH| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + K * L + K * L := by
      rw [abs_mul]
      exact add_le_add (add_le_add hda hprod) (mul_le_mul ha hh (abs_nonneg _) hK)
    _ = M + 2 * K * L := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth coordinate-plane rotations for the finite Haar Ward calculation. -/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

lemma planeGenerator_mulVec {N : ℕ} (i j k : Fin N) (v : Fin N → ℝ) :
    (planeGenerator i j *ᵥ v) k =
      (if k = i then v j else 0) - (if k = j then v i else 0) := by
  simp [planeGenerator, Matrix.sub_mulVec, Matrix.single_mulVec, Function.update_apply, eq_comm]

/-- The coordinate derivative along a genuine Haar-preserving plane rotation. -/
lemma hasDerivAt_planeRotation_coordinate {N : ℕ} (i j k : Fin N)
    (U : Orthogonal N) (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (fun s => matrixRotation (planeRotation i j s * U) v k)
      ((if k = i then matrixRotation (planeRotation i j t * U) v j else 0) -
        (if k = j then matrixRotation (planeRotation i j t * U) v i else 0)) t := by
  let A := planeGenerator i j
  let ev := matrixVectorCoordinate k v.ofLp
  have he := (hasDerivAt_exp_smul_const' A t).mul_const
    (U : Matrix (Fin N) (Fin N) ℝ)
  have hd := ev.hasFDerivAt.comp_hasDerivAt t he
  refine hd.congr_deriv (Eq.symm ?_)
  · change _ = ((A * NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ
        v.ofLp) k
    rw [mul_assoc, ← Matrix.mulVec_mulVec]
    exact (planeGenerator_mulVec i j k
      ((NormedSpace.exp (t • A) * (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v.ofLp)).symm

lemma hasDerivAt_planeRotation_energy {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (eig : Fin N → ℝ) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => rotatedEnergy eig (matrixRotation (planeRotation i j s * U)) σ)
      ((eig i - eig j) * matrixRotation (planeRotation i j t * U) (spinVector σ) i *
        matrixRotation (planeRotation i j t * U) (spinVector σ) j) t := by
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_planeRotation_coordinate i j k U (spinVector σ) t).pow 2).const_mul
      (eig k))).const_mul (1 / 2 : ℝ)
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [Nat.cast_ofNat, mul_sub, mul_ite, mul_zero, sub_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CoordinateWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coordinate Haar Ward identity for the Ising Hamiltonian

This proves the finite-dimensional identity for the unperturbed model with an
arbitrary deterministic spin prior and magnetic field.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_spinCoordinate {N : ℕ} (σ : Spin N) (i : Fin N) :
    Measurable (fun U : Orthogonal N => spinCoordinate U σ i) := by
  simp only [spinCoordinate, matrixRotation_apply, spinVector_apply]
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun U : Orthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact he.mul_const _

lemma measurable_orbitHamiltonian {N : ℕ} (eig c : Fin N → ℝ) (σ : Spin N) :
    Measurable (fun U : Orthogonal N => orbitHamiltonian eig c U σ) := by
  exact ((Finset.measurable_sum _ fun i _ =>
    ((measurable_spinCoordinate σ i).pow_const 2).const_mul (eig i)).const_mul
      (1 / 2 : ℝ)).add_const _

lemma spinCoordinate_sq_le {N : ℕ} (U : Orthogonal N) (σ : Spin N) (i : Fin N) :
    spinCoordinate U σ i ^ 2 ≤ N := by
  rw [← rotated_spin_sq_sum (matrixRotation U) σ]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma abs_coordinateProduct_le {N : ℕ} (i j : Fin N) (U : Orthogonal N) (σ : Spin N) :
    |coordinateProduct i j U σ| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  have hs : |coordinateProduct i j U σ| ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [sq_abs, coordinateProduct, mul_pow]
    simpa only [pow_two] using mul_le_mul hi hj (sq_nonneg _) (Nat.cast_nonneg _)
  exact (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp hs

lemma abs_coordinateSquareDifference_le {N : ℕ} (i j : Fin N)
    (U : Orthogonal N) (σ : Spin N) :
    |spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2| ≤ N := by
  have hi := spinCoordinate_sq_le U σ i
  have hj := spinCoordinate_sq_le U σ j
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (spinCoordinate U σ j)],
    by nlinarith [sq_nonneg (spinCoordinate U σ i)]⟩

lemma hasDerivAt_plane_coordinateProduct {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (U : Orthogonal N) (σ : Spin N) (t : ℝ) :
    HasDerivAt (fun s => coordinateProduct i j (planeRotation i j s * U) σ)
      (spinCoordinate (planeRotation i j t * U) σ j ^ 2 -
        spinCoordinate (planeRotation i j t * U) σ i ^ 2) t := by
  have hd := (hasDerivAt_planeRotation_coordinate i j i U (spinVector σ) t).mul
    (hasDerivAt_planeRotation_coordinate i j j U (spinVector σ) t)
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [spinCoordinate, ite_true, if_true, hij, Ne.symm hij, ite_false, if_false, sub_zero, zero_sub]
    ring

lemma gibbsAverage_const_mul {S : Type*} [Fintype S] (w H A : S → ℝ) (a : ℝ) :
    gibbsAverage w H (fun σ => a * A σ) = a * gibbsAverage w H A := by
  simp only [gibbsAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma referencePartition_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ) :
    referencePartition ν H = ∑ x, ν.real {x}*Real.exp (H x) := by
  exact integral_fintype Integrable.of_finite

lemma referenceReplicaMean_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ)
    {r : ℕ} (D : (Fin r → S) → ℝ) :
    referenceReplicaMean ν H D =
      ∑ σ : Fin r → S, (∏ i, ν.real {σ i}*Real.exp (H (σ i))/referencePartition ν H)*D σ := by
  classical
  rw [referenceReplicaMean, integral_fintype Integrable.of_finite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod,smul_eq_mul,
    Real.exp_sum,Finset.prod_div_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  ring

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

lemma cylinderCross_prefix (a b : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    cylinderCross a b = ∑ i : Fin n, a i*b i := by
  rw [cylinderCross,a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*b i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => a i*b i) n).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
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

lemma normalizedRestriction_pi {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    (A : ι → Set X) (hA : ∀ i, ν (A i) ≠ 0) :
    Measure.pi (fun i => normalizedRestriction ν (A i)) =
      normalizedRestriction (Measure.pi (fun _ : ι => ν)) (Set.univ.pi A) := by
  classical
  have : ∀ i, IsProbabilityMeasure (normalizedRestriction ν (A i)) :=
    fun i => normalizedRestriction_probability (hA i)
  apply Measure.pi_eq
  intro S hS
  simp only [normalizedRestriction,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hS),← Set.pi_inter_distrib]
  simp_rw [Measure.pi_pi,Measure.restrict_apply (hS _)]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (measure_ne_top _ _)),
    ← Finset.prod_mul_distrib]

lemma replica_restriction_eventually {ι X : Type*} [Finite ι]
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (σ : ι → X) :
    ∀ᶠ n in atTop, σ ∈ Set.univ.pi (fun _ : ι => A n) := by
  filter_upwards [Filter.eventually_all.mpr (fun i => hA (σ i))] with n hn
  exact Set.mem_univ_pi.mpr hn

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

lemma referenceReplicaMean_subtype {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ} (hmD : Measurable D) :
    referenceReplicaMean (subtypeReference ν A) (fun x => H x)
      (fun σ => D (fun i => (σ i : X))) = referenceReplicaMean (normalizedRestriction ν A) H D := by
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hA hp
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  exact referenceReplicaMean_map (subtypeReference_preserving ν hA) hmH hmD

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

lemma integrable_exp_of_integer_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (hm : Measurable Y)
    (he : ∀ n : ℤ, Integrable (fun x => Real.exp ((n:ℝ)*Y x)) ν) (t : ℝ) :
    Integrable (fun x => Real.exp (t*Y x)) ν := by
  obtain ⟨n,hn⟩ := exists_nat_gt |t|
  have hp := he (n:ℤ)
  have hm' := he (-(n:ℤ))
  apply (hp.add hm').mono' (hm.const_mul t |>.exp.aestronglyMeasurable)
  refine ae_of_all _ fun x => ?_
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Int.cast_natCast,Int.cast_neg]
  by_cases hy : 0 ≤ Y x
  · have h : t*Y x ≤ (n:ℝ)*Y x := mul_le_mul_of_nonneg_right ((le_abs_self t).trans hn.le) hy
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have h : t*Y x ≤ -(n:ℝ)*Y x := mul_le_mul_of_nonpos_right (by linarith [neg_abs_le t]) (le_of_not_ge hy)
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CountableReplicaRestriction
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Leaf exhaustion for bounded replica observables of an arbitrary
integrable Gibbs Hamiltonian. No Gaussian insertion remains in the Ward
terms to which this lemma will be applied. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma referenceReplicaMean_restriction_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ}
    (D : (Fin r → X) → ℝ) {B : ℝ} (hD : ∀ σ, |D σ| ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => referenceReplicaMean (normalizedRestriction ν (S n)) H D) atTop
      (𝓝 (referenceReplicaMean ν H D)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (S n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ : Fin r => ν)) := by
    simpa only [Real.exp_sum] using
      (Integrable.fintype_prod (fun _ : Fin r => hH))
  have hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)) * D σ)
      (Measure.pi (fun _ : Fin r => ν)) :=
    he.mul_bdd (measurable_of_countable D).aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hD σ)
  have hz : (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) ≠ 0 := by
    rw [reference_replica_partition]
    exact pow_ne_zero _ (_root_.MeasureTheory.integral_exp_pos hH).ne'
  have ht := normalized_restriction_gibbs_tendsto
    (fun n => MeasurableSet.univ_pi (fun _ : Fin r => hS n))
    (replica_restriction_eventually hexh) he hi hz
  simpa only [referenceReplicaMean_eq_ratio,
    ← normalizedRestriction_pi (fun _ : Fin r => S _) (fun _ => hpos _)] using ht

theorem expected_referenceReplicaMean_restriction_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    {r : ℕ} (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z, |D z| ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ ω, referenceReplicaMean (normalizedRestriction ν (S n))
      (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) atTop
      (𝓝 (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (S n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    exact (measurable_random_referenceReplicaMean
      (ν := fun _ : Ω => normalizedRestriction ν (S n)) measurable_const hH hD).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact referenceReplicaMean_abs_le _ _ _
        (hD.comp (measurable_const.prodMk measurable_id)) hB (fun σ => hbound (ω,σ))
  · filter_upwards [he] with ω hω
    exact referenceReplicaMean_restriction_tendsto ν (fun x => H (ω,x)) hω
      (fun σ => D (ω,σ)) (fun σ => hbound (ω,σ)) hS hexh hpos

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_CountableWardMixture
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform fixed-prior Ward bounds survive a measurable mixture of
countable reference measures. -/

noncomputable section

open MeasureTheory IsingPerceptron

namespace InvariantIsing

lemma measurable_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D) :
    Measurable (fun p : T × Ω =>
      referenceReplicaMean (ν p.1) (fun x => H (p.2,x)) (fun σ => D (p.2,σ))) := by
  have : ∀ p : T × Ω, IsProbabilityMeasure ((ν ∘ Prod.fst) p) := fun p => by
    change IsProbabilityMeasure (ν p.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact measurable_random_referenceReplicaMean (hν.comp measurable_fst)
    (hH.comp (measurable_fst.snd.prodMk measurable_snd))
    (hD.comp (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_integral_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [SFinite P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D) :
    Measurable (fun t => ∫ ω,
      referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) :=
  (measurable_mixtureReplicaMean ν hν H hH D hD).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_mixtureReplicaMean {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ξ : Measure T) [IsProbabilityMeasure ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → X) → ℝ) (hD : Measurable D)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |D z| ≤ B) :
    Integrable (fun t => ∫ ω,
      referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ)) ∂P) ξ := by
  have hm := measurable_integral_mixtureReplicaMean P ν hν H hH D hD
  apply integrable_of_measurable_abs_le (c := B) hm
  intro t
  apply abs_integral_le_const_of_bound (c := B)
    ((measurable_mixtureReplicaMean ν hν H hH D hD).comp (measurable_const.prodMk measurable_id))
  intro ω
  change |referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D (ω,σ))| ≤ B
  exact referenceReplicaMean_abs_le (ν t) _ _ (measurable_of_countable _) hB (fun σ => hb (ω,σ))

end InvariantIsing

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

lemma featureCoefficients_variance {I : Type*} [Fintype I]
    (t : I → ℕ) (ht : Function.Injective t) (a : I → ℝ) :
    (featureCoefficients t a).sum (fun _ c => c^2) = ∑ i, (a i)^2 := by
  rw [← cylinderCross_self,featureCoefficients_diagonal t t (fun _ _ h => ht h)]
  simp [pow_two]

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true, if_true,ih]

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

lemma treeFeatureTag_injective {J : Type*} [Encodable J] (n : ℕ) (v : LabeledLeaf n) :
    Function.Injective (treeFeatureTag (J := J) n v) := by
  intro i j h
  exact ((treeFeatureTag_cross n v v i j).mp h).1

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

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

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

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma integrable_exp_bounded_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H B : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hB : Measurable B) {K : ℝ} (hbound : ∀ x, B x ≤ K) :
    Integrable (fun x => Real.exp (B x+H x)) ν := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (H x)*Real.exp (B x)) ν :=
    he.aestronglyMeasurable.mul hB.exp.aestronglyMeasurable
  apply (he.const_mul (Real.exp K)).mono'
  · simpa only [Real.exp_add,mul_comm,Pi.mul_apply] using hm
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_add]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound x)) (Real.exp_pos _).le)

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

end IsingPerceptron

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
namespace IsingPerceptron

lemma replica_injective_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] {r : ℕ} (ι : Fin r → ℕ) (hi : Function.Injective ι) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ (ι i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  have h0 : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have h := h0.precomp hi
  have he := h.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

end IsingPerceptron

 

 

 

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
namespace IsingPerceptron

lemma tendsto_nat_rpow_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-c)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop

lemma perturbationScale_tendsto : Tendsto perturbationScale atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-1/16:ℝ)) atTop (𝓝 0)
  simpa only [neg_div] using tendsto_nat_rpow_neg (c := 1/16) (by norm_num)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite perturbation sums for the manuscript's geometric weights. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma perturbationWeight_linear_le (j : ℕ) :
    ((j : ℝ) + 1) * perturbationWeight j ≤ 1 := by
  induction j with
  | zero => norm_num [perturbationWeight]
  | succ j ih =>
    have hw := perturbationWeight_nonneg j
    have he : perturbationWeight (j + 1) = perturbationWeight j / 2 := by
      unfold perturbationWeight
      rw [pow_succ]
      ring
    rw [he]
    push_cast
    nlinarith

lemma perturbationWeight_degree_sum_le {N m : ℕ} (degree : Fin N → Fin m → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    (∑ j : Fin N, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ)) ≤ D := by
  calc
    _ ≤ ∑ j : Fin N, D * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ perturbationWeight j ^ 2 * (D * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hdegree j) (sq_nonneg _)
        _ = (D * perturbationWeight j) * (((j : ℝ) + 1) * perturbationWeight j) := by ring
        _ ≤ (D * perturbationWeight j) * 1 := mul_le_mul_of_nonneg_left
          (perturbationWeight_linear_le j) (mul_nonneg hD (perturbationWeight_nonneg j))
        _ = _ := mul_one _
    _ = D * (1 - (1 / 2 : ℝ) ^ N) := by rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ D := mul_le_of_le_one_right hD (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

lemma tensorPerturbationAmplitude_sq_le (N : ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (j : Fin N) :
    tensorPerturbationAmplitude N u j ^ 2 ≤
      4 * N * perturbationScale N ^ 2 * perturbationWeight j ^ 2 := by
  have hu2 : u j ^ 2 ≤ 4 := by
    have hb := abs_le.mp (hu j)
    nlinarith
  rw [tensorPerturbationAmplitude, mul_pow, perturbationAmplitude_sq]
  exact (mul_le_mul_of_nonneg_left hu2 (by positivity)).trans_eq (by ring)

/-- The fixed linear bound on the enumerated monomial degrees gives a
dimension-independent normalized rotation modulus. Only the finite sum
through dimension `N` is used. -/
theorem tensorPerturbationAmplitude_degree_sum_le {N m : ℕ}
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (degree : Fin N → Fin m → ℕ)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) :
    (∑ j : Fin N, tensorPerturbationAmplitude N u j ^ 2 * ∑ a, (degree j a : ℝ)) ≤
      4 * N * perturbationScale N ^ 2 * D := by
  calc
    _ ≤ ∑ j : Fin N, (4 * N * perturbationScale N ^ 2 * perturbationWeight j ^ 2) *
        ∑ a, (degree j a : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (tensorPerturbationAmplitude_sq_le N u hu j)
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = (4 * N * perturbationScale N ^ 2) *
        ∑ j : Fin N, perturbationWeight j ^ 2 * ∑ a, (degree j a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (perturbationWeight_degree_sum_le degree D hD hdegree)
      (by positivity)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_MonomialEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete complete enumeration of the spectral/tree monomials with linear degree cap. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma multidegreeDecode_sum_le (m j : ℕ) :
    (∑ i, multidegreeDecode m j i) ≤ j := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [multidegreeDecode, Fin.cases_zero, Fin.cases_succ]
    exact (Nat.add_le_add_left (ih (Nat.unpair j).2) _).trans (Nat.unpair_add_le j)

lemma enumeratedMonomial_degree_le (m j : ℕ) :
    (∑ a, enumeratedSpectralDegree m j a) + enumeratedTreeDegree m j ≤ j + 1 := by
  simpa only [Fin.sum_univ_castSucc, enumeratedSpectralDegree, enumeratedTreeDegree] using
    multidegreeDecode_sum_le (m + 1) (j + 1)

lemma enumeratedSpectralDegree_real_sum_le (m j : ℕ) :
    (∑ a, (enumeratedSpectralDegree m j a : ℝ)) ≤ (j : ℝ) + 1 := by
  have h := (Nat.le_add_right (∑ a, enumeratedSpectralDegree m j a)
    (enumeratedTreeDegree m j)).trans (enumeratedMonomial_degree_le m j)
  exact_mod_cast h

end InvariantIsing

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

theorem spinTensorFeature_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) ≤
      (site : ℝ) * N + ∑ j, (monomial j : ℝ) * amplitude j ^ 2 := by
  have he : (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      spinTensorFeature U I degree amplitude σ i ^ 2) =
      ∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
        spinTensorFeature U I degree amplitude σ i * spinTensorFeature U I degree amplitude σ i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, spinTensorFeature_covariance]
  simp only [← sq, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have hp : (∏ a, projectedOverlap U (I a) σ σ ^ degree j a) ≤ 1 :=
    (le_abs_self _).trans (spectralMonomial_abs_le_one U I (degree j) σ σ)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_MixedSpectralFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-rotation tensor covariances for Gaussian mean comparison. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma spectralSpinFeature_mixed_cross {N : ℕ} (U V : Rotation N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    (∑ i : I, spectralSpinFeature U I σ i * spectralSpinFeature V I τ i) =
      mixedProjectedOverlap U V I σ τ := by
  simp only [spectralSpinFeature, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N), ← Finset.sum_div]
  rw [div_eq_mul_inv, mul_comm]
  unfold mixedProjectedOverlap
  congr 1
  exact Finset.sum_coe_sort I (fun i => U (spinVector σ) i * V (spinVector τ) i)

lemma spectralMonomialFeature_mixed_cross {N m : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) :
    (∑ v : SpectralTensorIndex I d,
      spectralMonomialFeature U I d σ v * spectralMonomialFeature V I d τ v) =
      ∏ a, mixedProjectedOverlap U V (I a) σ τ ^ d a := by
  simp only [spectralMonomialFeature, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (v : Fin (d a) → I a) =>
    IsingPerceptron.tensorFeature (d a) (spectralSpinFeature U (I a) σ) v *
      IsingPerceptron.tensorFeature (d a) (spectralSpinFeature V (I a) τ) v)]
  simp_rw [IsingPerceptron.tensorFeature_cross, spectralSpinFeature_mixed_cross]

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

lemma tensorLeafCoefficients_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (x : Spin N × LabeledLeaf n) :
    (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) x).sum (fun _ c => c ^ 2) ≤
      ∑ i, ((site i : ℝ) * N + ∑ j, (monomial i j : ℝ) * amplitude j ^ 2) := by
  rw [← cylinderCross_self, tensorLeafCoefficients_cross]
  simp only [labeledCommonDepth_self,
    show ∀ i : Fin (n + 1), i.1 ≤ n from fun i => Nat.le_of_lt_succ i.isLt, ite_true, if_true]
  apply Finset.sum_le_sum
  intro i _
  simpa only [pow_two, mul_assoc] using
    spinTensorFeature_variance_le U I degree amplitude (site i) (monomial i) x.1

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

lemma varianceIncrement_sum {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (n : ℕ) :
    (∑ i : Fin (n + 1), (varianceIncrement q i : ℝ)) = q n := by
  simp_rw [varianceIncrement_coe hq h0]
  rw [Fin.sum_univ_eq_sum_range, pathIncrement_sum]

lemma monomialVarianceIncrement_sum_le (n : ℕ) (r : ℕ) :
    (∑ i : Fin (n + 1), (varianceIncrement (monomialPath n r) i : ℝ)) ≤ 1 := by
  rw [varianceIncrement_sum (monomialPath_monotone n r) (monomialPath_nonneg n r 0)]
  exact monomialPath_diag_le_one n r

lemma tensorPathProfile_variance_cap {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) :
    (tensorLeafCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x).sum (fun _ c => c ^ 2) ≤
      h n * N + ∑ j, amplitude j ^ 2 := by
  have hc := tensorLeafCoefficients_variance_le U I degree amplitude n
    (fun i => varianceIncrement h i)
    (fun i j => varianceIncrement (monomialPath n (treeDegree j)) i) x
  refine hc.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, varianceIncrement_sum hh h0,
    Finset.sum_comm]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (treeDegree j))
    (sq_nonneg (amplitude j))).trans_eq (one_mul _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected actual spectral/tree monomial as an independent Gaussian factor. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespaceTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) : Function.Injective (tensorNamespaceTag I degree) := by
  rintro ⟨i, p, a⟩ ⟨j, q, b⟩ h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      cases he
      rfl
    | inr b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨a, s⟩
      rcases b with ⟨b, t⟩
      have hp := Nat.pair_eq_pair.mp h
      have hab : a = b := Fin.ext (Nat.add_right_cancel hp.1)
      subst b
      have he := Encodable.encode_inj.mp hp.2
      cases he
      rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomCoefficientIBP
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Gaussian insertion when the finite coefficient vectors depend on external
disorder. This permits the Haar-dependent spectral-overlap tensor features.
The Gaussian coordinates remain independent of the external disorder.
-/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

omit [IsProbabilityMeasure P] in
/-- All exponential tilts are integrable for almost every joint disorder.
Only integer tilts are intersected before extending to every real parameter. -/
lemma randomCoefficient_all_exp_ae (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1, hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t * cylinderField (A p.1.1 p.2) p.1.2)) := (hA.const_mul t).exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((A ω x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (A ω x).sum (fun _ c => c ^ 2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha ω x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields (A ω))
      (fun x => cylinderField_law (A ω x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n : ℝ) * cylinderField (A z.1 x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n : ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen exponential integrability and selected-field log partition identities. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNamespacedCoefficients_variance_eq {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) =
      (tensorLeafCoefficients U I degree amplitude n v x).sum (fun _ c => c ^ 2) := by
  have hi : Function.Injective (fun i : Fin (n + 1) × SpinTensorIndex I degree =>
      tensorNamespaceTag I degree (i.1.1, (labeledAddress n x.2).take i.1, i.2)) := by
    intro i j hij
    apply treeFeatureTag_injective n x.2
    exact congrArg Encodable.encode ((tensorNamespaceTag_injective I degree) hij)
  rw [tensorNamespacedCoefficients, featureCoefficients_variance _ hi,
    tensorLeafCoefficients, featureCoefficients_variance _ (treeFeatureTag_injective n x.2)]

lemma tensorNamespacedPath_variance_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) :
    (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x).sum (fun _ c => c ^ 2) ≤
      h n * N + ∑ j, amplitude j ^ 2 := by
  rw [tensorNamespacedCoefficients_variance_eq]
  exact tensorPathProfile_variance_cap U I degree amplitude n treeDegree h hh h0 x

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite replica contractions in the spectral Ward calculation

The sums over two spectral coordinate groups contract into products of
projected overlaps. These are exact finite identities, with no symmetry or
full-support requirement on the deterministic spin prior.
-/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

lemma gibbsAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → ℝ) :
    gibbsAverage w H (fun σ => ∑ i ∈ I, A i σ) = ∑ i ∈ I, gibbsAverage w H (A i) := by
  simp only [gibbsAverage, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma gibbsPairAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → S → ℝ) :
    gibbsPairAverage w H (fun σ τ => ∑ i ∈ I, A i σ τ) =
      ∑ i ∈ I, gibbsPairAverage w H (A i) := by
  simp only [gibbsPairAverage, Finset.mul_sum]
  trans ∑ σ, ∑ i ∈ I, ∑ τ, finiteGibbs w H σ * finiteGibbs w H τ * A i σ τ
  · apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

lemma gibbsAverage_mul_gibbsAverage (w H A B : S → ℝ) :
    gibbsAverage w H A * gibbsAverage w H B =
      gibbsPairAverage w H (fun σ τ => A σ * B τ) := by
  simp only [gibbsAverage, gibbsPairAverage, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorReplicaAverageLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite replica averages under the tensor Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma referenceReplicaMean_zero {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {q : ℕ} (D : (Fin q → X) → ℝ) :
    referenceReplicaMean ν (fun _ => 0) D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin q => ν) := by
  rw [referenceReplicaMean_eq_tilted ν (fun _ => 0) (by simp) D]
  simp only [show (fun _ : X => (0 : ℝ)) = 0 from rfl, tilted_zero]

lemma measurable_tensorNamespacedReplicaMean {N m k q : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (D : SpecialOrthogonal N → (Fin q → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun p : TensorFlatDisorder N n =>
      referenceReplicaMean (tensorNamespacedReference eig c I degree amplitude n r h p)
        (fun _ => 0) (D p.1.1)) := by
  exact measurable_random_referenceReplicaMean
    (measurable_tensorNamespacedReference eig c I degree amplitude n r h) measurable_const
    (hD.comp (measurable_fst.fst.fst.prodMk measurable_snd))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spectral overlap array laws retain the common rotation disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology ENNReal NNReal

namespace InvariantIsing

lemma spectralJointEntry_spectral {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) (a : Fin m) :
    (spectralJointEntry U I n x y a.castSucc : ℝ) = projectedOverlap U (I a) x.1 y.1 := by
  simp only [spectralJointEntry, Fin.lastCases_castSucc]

theorem spectralArrayLaw_integral {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)]
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
    (∫ x, F x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1)))) =
      ∫ ω, ∫ σ, F (spectralReplicaArray U I n (ω, σ))
        ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hm := measurable_spectralReplicaArray U hU I n
  have hi : Integrable (F ∘ spectralReplicaArray U I n) (disorderReplicaLaw P ν hν) := by
    exact (MeasureTheory.integrable_map_measure hF.aestronglyMeasurable hm.aemeasurable).mp
      (compact_integrable hF)
  change (∫ x, F x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)) = _
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact Measure.integral_compProd hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-replica tests of the actual tensor spectral-array law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

/-- Injection into the infinite replica sequence gives the exact actual
finite-replica mean, while retaining its common rotation. -/
theorem tensorNamespacedArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(tensorNamespacedArrayLaw μ eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amplitude n b r h D := by
  rw [tensorNamespacedArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold tensorNamespacedReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := tensorNamespacedReference eig c I degree amplitude n r h p
  have ht := integral_map hm.aemeasurable (μ := Measure.infinitePi (fun _ : ℕ => ν))
    (measurable_of_countable (D p.1.1)).aestronglyMeasurable
  rw [replica_injective_map ν ι hi] at ht
  change (∫ σ, F (fun ij : ℕ × ℕ =>
    spectralJointEntry (specialRotation p.1.1) I n (σ ij.1) (σ ij.2))
    ∂Measure.infinitePi (fun _ : ℕ => ν)) = ∫ σ, D p.1.1 σ ∂Measure.pi (fun _ : Fin z => ν)
  simp_rw [he]
  exact ht.symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TripleContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica contractions for the off-diagonal spectral Ward equation. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

lemma gibbsTripleAverage_finset_sum (w H : S → ℝ) (I : Finset ι) (A : ι → S → S → S → ℝ) :
    gibbsTripleAverage w H (fun σ τ η => ∑ i ∈ I, A i σ τ η) =
      ∑ i ∈ I, gibbsTripleAverage w H (A i) := by
  simp only [gibbsTripleAverage, Finset.mul_sum]
  trans ∑ σ, ∑ τ, ∑ i ∈ I, ∑ η,
    finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A i σ τ η
  · apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    rw [Finset.sum_comm]
  · trans ∑ σ, ∑ i ∈ I, ∑ τ, ∑ η,
      finiteGibbs w H σ * finiteGibbs w H τ * finiteGibbs w H η * A i σ τ η
    · apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardError
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite covariance derivative contractions in the tensor perturbation
error of the spectral Ward identity (manuscript, §3, lines 421--439). -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma hasDerivAt_mixedProjectedOverlap_plane {N : ℕ} (U : Orthogonal N)
    (K : Finset (Fin N)) (i j : Fin N) (σ τ : Spin N) :
    HasDerivAt (fun s => mixedProjectedOverlap (matrixRotation (planeRotation i j s * U))
      (matrixRotation U) K σ τ) (projectedOverlapEndpointDerivative U K i j σ τ) 0 := by
  have hd := (HasDerivAt.fun_sum (u := K) (fun k _ =>
    (hasDerivAt_planeRotation_coordinate i j k U (spinVector σ) 0).mul_const
      (matrixRotation U (spinVector τ) k))).const_mul (N : ℝ)⁻¹
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [planeRotation_zero, one_mul, projectedOverlapEndpointDerivative, spinCoordinate,
      sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- This is the derivative in one tensor endpoint. The other endpoint and
all tree coordinates remain fixed during the plane rotation. -/
theorem hasDerivAt_spectralMonomial_mixed_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (i j : Fin N) (σ τ : Spin N) :
    HasDerivAt (fun s => ∏ a,
      mixedProjectedOverlap (matrixRotation (planeRotation i j s * U)) (matrixRotation U) (I a) σ τ ^ d a)
      (spectralMonomialEndpointDerivative U I d i j σ τ) 0 := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun a _ =>
    (hasDerivAt_mixedProjectedOverlap_plane U (I a) i j σ τ).pow (d a))
  have hs (a : Fin m) : mixedProjectedOverlap (matrixRotation (planeRotation i j 0 * U))
      (matrixRotation U) (I a) σ τ = projectedOverlap (matrixRotation U) (I a) σ τ := by
    simp only [planeRotation_zero, one_mul]
    rfl
  simpa only [Pi.pow_apply, hs, smul_eq_mul, spectralMonomialEndpointDerivative,
    spectralMonomialEndpointCoefficient, mul_assoc] using hd

lemma spectralMonomialEndpointCoefficient_abs_le {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ τ : Spin N) (a : Fin m) :
    |spectralMonomialEndpointCoefficient U I d σ τ a| ≤ d a := by
  have hpow (b : Fin m) (r : ℕ) : |projectedOverlap (matrixRotation U) (I b) σ τ ^ r| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one _ _ _ _)
  have hp : |∏ b ∈ Finset.univ.erase a, projectedOverlap (matrixRotation U) (I b) σ τ ^ d b| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun b _ => hpow b (d b))
  unfold spectralMonomialEndpointCoefficient
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (d a) : (0 : ℝ) ≤ (d a : ℝ))]
  calc
    _ ≤ 1 * ((d a : ℝ) * 1) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_left (hpow a (d a - 1)) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) zero_le_one
    _ = _ := by ring

/-- The two coordinate sums contract into products of normalized projected
inner products, with one remaining factor `1/N`. -/
theorem projectedEndpointContraction_eq {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) :
    projectedEndpointContraction U I J K η θ σ τ =
      (N : ℝ)⁻¹ * (projectedOverlap (matrixRotation U) (I ∩ K) η τ *
        projectedOverlap (matrixRotation U) J θ σ -
        projectedOverlap (matrixRotation U) I η σ * projectedOverlap (matrixRotation U) (J ∩ K) θ τ) := by
  classical
  have hi : (∑ i ∈ I, if i ∈ K then spinCoordinate U η i * spinCoordinate U τ i else 0) =
      ∑ i ∈ I ∩ K, spinCoordinate U η i * spinCoordinate U τ i := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  have hj : (∑ j ∈ J, if j ∈ K then spinCoordinate U θ j * spinCoordinate U τ j else 0) =
      ∑ j ∈ J ∩ K, spinCoordinate U θ j * spinCoordinate U τ j := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  have hterm (i j : Fin N) : spinCoordinate U η i * spinCoordinate U θ j *
      projectedOverlapEndpointDerivative U K i j σ τ = (N : ℝ)⁻¹ *
      ((if i ∈ K then spinCoordinate U η i * spinCoordinate U τ i else 0) *
          (spinCoordinate U θ j * spinCoordinate U σ j) -
        (spinCoordinate U η i * spinCoordinate U σ i) *
          (if j ∈ K then spinCoordinate U θ j * spinCoordinate U τ j else 0)) := by
    unfold projectedOverlapEndpointDerivative
    split_ifs <;> ring
  simp_rw [projectedEndpointContraction, hterm]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hi, hj]
  simp only [projectedOverlap, spinCoordinate]
  ring

theorem projectedEndpointContraction_abs_le {N : ℕ} (U : Orthogonal N)
    (I J K : Finset (Fin N)) (η θ σ τ : Spin N) :
    |projectedEndpointContraction U I J K η θ σ τ| ≤ 2 * (N : ℝ)⁻¹ := by
  rw [projectedEndpointContraction_eq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  have hab (K L : Finset (Fin N)) (s t u w : Spin N) :
      |projectedOverlap (matrixRotation U) K s t * projectedOverlap (matrixRotation U) L u w| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (projectedOverlap_abs_le_one _ _ _ _) (projectedOverlap_abs_le_one _ _ _ _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hd : |projectedOverlap (matrixRotation U) (I ∩ K) η τ * projectedOverlap (matrixRotation U) J θ σ -
      projectedOverlap (matrixRotation U) I η σ * projectedOverlap (matrixRotation U) (J ∩ K) θ τ| ≤ 2 := by
    have h1 := hab (I ∩ K) J η τ θ σ
    have h2 := hab I (J ∩ K) η σ θ τ
    exact (abs_sub _ _).trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]

theorem spectralMonomialEndpointContraction_eq {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) :
    spectralMonomialEndpointContraction U groups d I J η θ σ τ =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J, spinCoordinate U η i * spinCoordinate U θ j *
        spectralMonomialEndpointDerivative U groups d i j σ τ := by
  unfold spectralMonomialEndpointContraction projectedEndpointContraction spectralMonomialEndpointDerivative
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem spectralMonomialEndpointContraction_abs_le {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (I J : Finset (Fin N)) (η θ σ τ : Spin N) :
    |spectralMonomialEndpointContraction U groups d I J η θ σ τ| ≤
      2 * (N : ℝ)⁻¹ * ∑ a, (d a : ℝ) := by
  unfold spectralMonomialEndpointContraction
  calc
    _ ≤ ∑ a, |spectralMonomialEndpointCoefficient U groups d σ τ a *
        projectedEndpointContraction U I J (groups a) η θ σ τ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (d a : ℝ) * (2 * (N : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (spectralMonomialEndpointCoefficient_abs_le U groups d σ τ a)
        (projectedEndpointContraction_abs_le U I J (groups a) η θ σ τ) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem tensorWardPerturbationError_eq {N m : ℕ} (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ)
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    tensorWardPerturbationError U groups degree treeDegree n u I J η θ x y =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ I, ∑ j ∈ J, spinCoordinate U η i * spinCoordinate U θ j *
        ∑ r, tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
          spectralMonomialEndpointDerivative U groups (degree r) i j x.1 y.1 := by
  unfold tensorWardPerturbationError
  simp_rw [spectralMonomialEndpointContraction_eq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- One covariance contraction after Gaussian integration by parts, for
the actual finite geometric-weight perturbation. It is uniform in tree
depth, all four spin replicas, and the coordinate groups. -/
theorem tensorWardPerturbationError_abs_le {N m : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (groups : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (n : ℕ) (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D) (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (I J : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    |tensorWardPerturbationError U groups degree treeDegree n u I J η θ x y| ≤
      8 * D * perturbationScale N ^ 2 := by
  have ht (r : Fin N) : |treeOverlap n x.2 y.2 ^ treeDegree r| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg (treeOverlap_mem n x.2 y.2).1]
    exact pow_le_one₀ (treeOverlap_mem n x.2 y.2).1 (treeOverlap_mem n x.2 y.2).2
  unfold tensorWardPerturbationError
  calc
    _ ≤ ∑ r, |tensorPerturbationAmplitude N u r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointContraction U groups (degree r) I J η θ x.1 y.1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, tensorPerturbationAmplitude N u r ^ 2 *
        (2 * (N : ℝ)⁻¹ * ∑ a, (degree r a : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hcoef : tensorPerturbationAmplitude N u r ^ 2 * |treeOverlap n x.2 y.2 ^ treeDegree r| ≤
          tensorPerturbationAmplitude N u r ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) (ht r)
      exact mul_le_mul hcoef
        (spectralMonomialEndpointContraction_abs_le U groups (degree r) I J η θ x.1 y.1)
        (abs_nonneg _) (sq_nonneg _)
    _ = 2 * (N : ℝ)⁻¹ * ∑ r, tensorPerturbationAmplitude N u r ^ 2 * ∑ a, (degree r a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ 2 * (N : ℝ)⁻¹ * (4 * N * perturbationScale N ^ 2 * D) :=
      mul_le_mul_of_nonneg_left (tensorPerturbationAmplitude_degree_sum_le u hu degree D hD hdegree) (by positivity)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialPlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine coordinate-plane rotations and infinitesimal Haar invariance on
`SO(N)`, the rotation group used by the actual enriched model. -/

noncomputable section

open MeasureTheory Filter IsingPerceptron
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

lemma measurable_specialToOrthogonal {N : ℕ} :
    Measurable (specialToOrthogonal : SpecialOrthogonal N → Orthogonal N) :=
  measurable_subtype_coe.subtype_mk

/-- A dominated infinitesimal left rotation has Haar mean zero. -/
lemma integral_special_rotation_derivative_eq_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [μ.IsMulLeftInvariant] (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    (f : SpecialOrthogonal N → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (f' : ℝ → SpecialOrthogonal N → ℝ) (hf' : AEStronglyMeasurable (f' 0) μ)
    (B : SpecialOrthogonal N → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ B U)
    (hderiv : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t) :
    ∫ U, f' 0 U ∂μ = 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun U => f (R t * U)) μ := by
    apply Filter.Eventually.of_forall
    intro t
    have hmul : Measurable (fun U : SpecialOrthogonal N => R t * U) := by
      apply Measurable.subtype_mk
      change Measurable (fun U : SpecialOrthogonal N =>
        (R t : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ))
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      simp only [Matrix.mul_apply]
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          ((measurable_pi_apply k).comp measurable_subtype_coe))
    exact (hf.comp hmul).aestronglyMeasurable
  have hi : Integrable (fun U => f (R 0 * U)) μ := by simpa only [hR, one_mul] using hfi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hf'
    hbound hB hderiv
  have he : (fun t => ∫ U, f (R t * U) ∂μ) = fun _ : ℝ => ∫ U, f U ∂μ := by
    funext t
    exact integral_mul_left_eq_self f (R t)
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (∫ U, f U ∂μ))


variable {S : Type*} [Fintype S]

/-- Exact finite-volume Haar Ward identity. All regularity assumptions concern
finite-dimensional derivatives; none assumes a limiting overlap identity. -/
theorem integral_special_gibbs_rotation_identity {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H A : SpecialOrthogonal N → S → ℝ)
    (hHm : ∀ σ, Measurable (fun U => H U σ))
    (hAm : ∀ σ, Measurable (fun U => A U σ))
    (dH dA : ℝ → SpecialOrthogonal N → S → ℝ)
    (hdHm : ∀ σ, Measurable (fun U => dH 0 U σ))
    (hdAm : ∀ σ, Measurable (fun U => dA 0 U σ))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) (dH t U σ) t)
    (hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t)
    (K L M : ℝ) (hK : 0 ≤ K)
    (hAb : ∀ U σ, |A U σ| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dH t U σ| ≤ L)
    (hdAb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dA t U σ| ≤ M) :
    (∫ U, gibbsAverage w (H U) (dA 0 U) +
      gibbsAverage w (H U) (fun σ => A U σ * dH 0 U σ) -
      gibbsAverage w (H U) (A U) * gibbsAverage w (H U) (dH 0 U) ∂μ) = 0 := by
  let f : SpecialOrthogonal N → ℝ := fun U => gibbsAverage w (H U) (A U)
  let f' : ℝ → SpecialOrthogonal N → ℝ := fun t U =>
    gibbsAverage w (H (R t * U)) (dA t U) +
      gibbsAverage w (H (R t * U)) (fun σ => A (R t * U) σ * dH t U σ) -
      gibbsAverage w (H (R t * U)) (A (R t * U)) *
        gibbsAverage w (H (R t * U)) (dH t U)
  have hm : Measurable f := measurable_gibbsAverage w H A hHm hAm
  have hi : Integrable f μ := (integrable_const K).mono' hm.aestronglyMeasurable
    (ae_of_all μ fun U => by
      simpa only [Real.norm_eq_abs] using
        (abs_gibbsAverage_le hw (H U) (A U) (hAb U)))
  have hm' : Measurable (f' 0) := by
    simp only [f', hR, one_mul]
    exact ((measurable_gibbsAverage w H (dA 0) hHm hdAm).add
      (measurable_gibbsAverage w H (fun U σ => A U σ * dH 0 U σ) hHm
        (fun σ => (hAm σ).mul (hdHm σ)))).sub
      ((measurable_gibbsAverage w H A hHm hAm).mul
        (measurable_gibbsAverage w H (dH 0) hHm hdHm))
  have hb : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ M + 2 * K * L := by
    exact ae_of_all _ fun U t ht => by
      simpa only [f', Real.norm_eq_abs] using
        abs_gibbsVariation_le hw (H (R t * U)) (A (R t * U)) (dH t U) (dA t U)
          hK (hAb _) (hdHb U t ht) (hdAb U t ht)
  have hd : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t :=
    ae_of_all _ fun U t ht => hasDerivAt_gibbsAverage hw (hHd U t ht) (hAd U t ht)
  have he := integral_special_rotation_derivative_eq_zero μ R hR f hm hi f'
    hm'.aestronglyMeasurable (fun _ => M + 2 * K * L) (integrable_const _) hb hd
  simpa only [f', hR, one_mul] using he


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFiniteWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-prior Gaussian insertions in the spectral Haar Ward calculation.
The covariance correction is derived by Gaussian integration by parts, with
no assumed Ward identity. Finite spin/leaf restrictions are permitted to
have zero prior weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S]

lemma integrable_gaussian_gibbs_linear_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x)
      (fun x => O x * linearGaussian A g x))
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsAverage
  apply integrable_finsetSum
  intro x _
  convert (integrable_linearGaussian_mul_gibbs hw H A C x x).const_mul (O x) using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  change _ = O x * (linearGaussian A g x * finiteGibbs w _ x)
  ring

lemma integrable_gaussian_gibbs_linear_product {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O *
      gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g))
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O) :=
    measurable_gibbsAverage w _ _ (fun x => by unfold linearGaussian; fun_prop)
      (fun _ => measurable_const)
  apply (integrable_gaussian_gibbs_linear_test hw H (fun _ => 1) A C).mul_bdd
    hm.aestronglyMeasurable (c := ∑ x, |O x|)
    (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs]
      exact abs_gibbsAverage_le hw _ O (fun x =>
        Finset.single_le_sum (fun y _ => abs_nonneg (O y)) (Finset.mem_univ x))) |>.congr
        (ae_of_all _ fun g => by simp only [one_mul] <;> ring)

lemma integrable_gaussian_gibbs_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g : Fin d → ℝ =>
      gibbsAverage w (fun x => H x + linearGaussian C g x) O) :=
    measurable_gibbsAverage w _ (fun _ => O)
      (fun x => by unfold linearGaussian; fun_prop) (fun _ => measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ x, |O x|)
  exact ae_of_all _ fun g => by
    rw [Real.norm_eq_abs]
    exact abs_gibbsAverage_le hw _ O (fun x =>
      Finset.single_le_sum (fun y _ => abs_nonneg (O y)) (Finset.mem_univ x))

/-- The Gibbs insertion in the current replica produces the derivative
covariance with one subtraction replica. -/
lemma gaussian_gibbs_test_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
      (fun x => O x * linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * gaussianCross A C x x) -
        gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * gaussianCross A C x y)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hi (x : S) : Integrable (fun g => O x * (gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ z, gaussianGibbs w H C g z * gaussianCross A C x z))) μ := by
    simpa only [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
      (integrable_replica_covariance (r := 1) hw H A C x (fun _ => x)).const_mul (O x)
  have he (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * gaussianCross A C x x) -
        gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * gaussianCross A C x y) =
      ∑ x, O x * (gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ z, gaussianGibbs w H C g z * gaussianCross A C x z)) := by
    simp only [gibbsAverage, gibbsPairAverage, gaussianGibbs,
      ← Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro z _
      ring
  have hl (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * linearGaussian A g x) =
      ∑ x, O x * (linearGaussian A g x * gaussianGibbs w H C g x) := by
    unfold gibbsAverage gaussianGibbs
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [he, hl]
  rw [integral_finsetSum _ (fun x _ =>
      (integrable_linearGaussian_mul_gibbs hw H A C x x).const_mul (O x)),
    integral_finsetSum _ (fun x _ => hi x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_const_mul, integral_const_mul, gaussian_gibbs_insertion hw]

lemma gaussian_gibbs_normalization_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x) O *
      gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * (gaussianCross A C y x + gaussianCross A C y y)) -
        2 * gibbsTripleAverage w (fun x => H x + linearGaussian C g x)
          (fun x y z => O x * gaussianCross A C y z)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hr (g : Fin (d + 1) → ℝ) (x y : S) :
      replicaGibbs w H C g ![x, y] = gaussianGibbs w H C g x * gaussianGibbs w H C g y := by
    simp only [replicaGibbs, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hi (x y : S) : Integrable (fun g => O x * (linearGaussian A g y *
      (gaussianGibbs w H C g x * gaussianGibbs w H C g y))) μ := by
    simpa only [hr] using (integrable_linear_mul_replica hw H A C y ![x, y]).const_mul (O x)
  have hi' (x y : S) : Integrable (fun g => O x *
      (gaussianGibbs w H C g x * gaussianGibbs w H C g y *
        (gaussianCross A C y x + gaussianCross A C y y -
          2 * ∑ z, gaussianGibbs w H C g z * gaussianCross A C y z))) μ := by
    have hh := (integrable_replica_covariance hw H A C y ![x, y]).const_mul (O x)
    simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext g
    ring
  have hl (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x) O *
        gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g) =
      ∑ x, ∑ y, O x * (linearGaussian A g y *
        (gaussianGibbs w H C g x * gaussianGibbs w H C g y)) := by
    simp only [gibbsAverage, Finset.sum_mul_sum, gaussianGibbs]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he (g : Fin (d + 1) → ℝ) :
      gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * (gaussianCross A C y x + gaussianCross A C y y)) -
        2 * gibbsTripleAverage w (fun x => H x + linearGaussian C g x)
          (fun x y z => O x * gaussianCross A C y z) =
      ∑ x, ∑ y, O x * (gaussianGibbs w H C g x * gaussianGibbs w H C g y *
        (gaussianCross A C y x + gaussianCross A C y y -
          2 * ∑ z, gaussianGibbs w H C g z * gaussianCross A C y z)) := by
    simp only [gibbsPairAverage, gibbsTripleAverage, gaussianGibbs, Finset.mul_sum,
      ← Finset.sum_sub_distrib, mul_sub]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro z _
      ring
  simp_rw [hl, he]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y)),
    integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi' x y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => hi x y),
    integral_finsetSum _ (fun y _ => hi' x y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_const_mul, integral_const_mul]
  have hh := gaussian_replica_insertion hw H A C y ![x, y]
  simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
  convert congrArg (fun a : ℝ => O x * a) hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun g => by ring

lemma integrable_gaussian_pair_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H : S → ℝ) (O : S → S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsPairAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsPairAverage
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  have hp := (integrable_const (O x y) : Integrable (fun _ : Fin d → ℝ => O x y)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1))).mul_bdd
    ((continuous_gaussianGibbs hw H C x).mul
      (continuous_gaussianGibbs hw H C y)).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun g => by
        simp only [Pi.mul_apply, gaussianGibbs]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (finiteGibbs_nonneg hw _ x)
          (finiteGibbs_nonneg hw _ y))]
        exact (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x)
          (finiteGibbs_nonneg hw _ y)).trans
            (by simpa only [one_mul] using finiteGibbs_le_one hw _ y))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  change _ = O x y * (finiteGibbs w _ x * finiteGibbs w _ y)
  ring

lemma integrable_gaussian_triple_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H : S → ℝ) (O : S → S → S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsTripleAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsTripleAverage
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  apply integrable_finsetSum
  intro z _
  have hp := (integrable_const (O x y z) : Integrable (fun _ : Fin d → ℝ => O x y z)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1))).mul_bdd
    (((continuous_gaussianGibbs hw H C x).mul (continuous_gaussianGibbs hw H C y)).mul
      (continuous_gaussianGibbs hw H C z)).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun g => by
        simp only [Pi.mul_apply, gaussianGibbs]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (mul_nonneg (finiteGibbs_nonneg hw _ x) (finiteGibbs_nonneg hw _ y))
          (finiteGibbs_nonneg hw _ z))]
        have hxy : finiteGibbs w (fun a => H a + linearGaussian C g a) x *
            finiteGibbs w (fun a => H a + linearGaussian C g a) y ≤ 1 :=
          (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x)
          (finiteGibbs_nonneg hw _ y)).trans
            (by simpa only [one_mul] using finiteGibbs_le_one hw _ y)
        exact (mul_le_mul_of_nonneg_right hxy (finiteGibbs_nonneg hw _ z)).trans
          (by simpa only [one_mul] using finiteGibbs_le_one hw _ z))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext g
  change _ = O x y z * (finiteGibbs w _ x * finiteGibbs w _ y * finiteGibbs w _ z)
  ring

/-- Exact Gaussian covariance-derivative correction for a finite prior.
The first coefficient map is the Hamiltonian derivative and the second
is the Gaussian coefficient in the Gibbs exponent. -/
theorem gaussian_gibbs_covariance_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * linearGaussian A g x) -
      gibbsAverage w (fun x => H x + linearGaussian C g x) O *
        gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O
        (gaussianCross A C)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  rw [integral_sub (integrable_gaussian_gibbs_linear_test hw H O A C)
    (integrable_gaussian_gibbs_linear_product hw H O A C),
    gaussian_gibbs_test_insertion hw H O A C, gaussian_gibbs_normalization_insertion hw H O A C]
  have hsub := integral_sub
    ((integrable_gaussian_gibbs_test hw H (fun x => O x * gaussianCross A C x x) C).sub
      (integrable_gaussian_pair_test hw H (fun x y => O x * gaussianCross A C x y) C))
    ((integrable_gaussian_pair_test hw H (fun x y => O x *
      (gaussianCross A C y x + gaussianCross A C y y)) C).sub
      ((integrable_gaussian_triple_test hw H (fun x y z => O x * gaussianCross A C y z) C).const_mul 2))
  simp only [Pi.sub_apply] at hsub
  rw [← hsub]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by unfold gaussianWardCorrection; ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoefficientDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate-plane derivatives of the actual finite spectral tensor
coefficients, with uniform finite-dimensional bounds for Haar differentiation. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma abs_normalized_spinCoordinate_le_one {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (σ : Spin N) (a : Fin N) :
    |spinCoordinate U σ a / Real.sqrt (N : ℝ)| ≤ 1 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs := Real.sq_sqrt hN'.le
  have ha := spinCoordinate_sq_le U σ a
  have hx : |spinCoordinate U σ a| ≤ Real.sqrt (N : ℝ) := by
    nlinarith [abs_nonneg (spinCoordinate U σ a), Real.sqrt_nonneg (N : ℝ),
      sq_abs (spinCoordinate U σ a)]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.2 hN')).mpr hx

lemma spectralSpinFeature_abs_le_one {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (I : Finset (Fin N)) (σ : Spin N) (a : I) :
    |spectralSpinFeature (matrixRotation U) I σ a| ≤ 1 :=
  abs_normalized_spinCoordinate_le_one hN U σ a

lemma spectralSpinPlaneDerivative_abs_le {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (σ : Spin N) (i j a : Fin N) :
    |spectralSpinPlaneDerivative U σ i j a| ≤ 2 := by
  have hi : |if a = i then spinCoordinate U σ j / Real.sqrt (N : ℝ) else 0| ≤ 1 := by
    split_ifs
    · exact abs_normalized_spinCoordinate_le_one hN U σ j
    · norm_num
  have hj : |if a = j then spinCoordinate U σ i / Real.sqrt (N : ℝ) else 0| ≤ 1 := by
    split_ifs
    · exact abs_normalized_spinCoordinate_le_one hN U σ i
    · norm_num
  exact (abs_sub _ _).trans (by linarith)

lemma hasDerivAt_spectralSpinFeature_plane {N : ℕ} (U : Orthogonal N)
    (I : Finset (Fin N)) (σ : Spin N) (i j : Fin N) (a : I) (t : ℝ) :
    HasDerivAt (fun s => spectralSpinFeature (matrixRotation (planeRotation i j s * U)) I σ a)
      (spectralSpinPlaneDerivative (planeRotation i j t * U) σ i j a) t := by
  have hd := (hasDerivAt_planeRotation_coordinate i j a U (spinVector σ) t).div_const
    (Real.sqrt (N : ℝ))
  refine hd.congr_deriv (Eq.symm ?_)
  · simp only [spectralSpinPlaneDerivative, spinCoordinate, sub_div, ite_div, zero_div]

lemma hasDerivAt_spectralMonomialFeature_plane {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) (t : ℝ) :
    HasDerivAt (fun s => spectralMonomialFeature (matrixRotation (planeRotation i j s * U)) I d σ v)
      (spectralTensorPlaneDerivative (planeRotation i j t * U) I d σ i j v) t := by
  have hi (a : Fin m) := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun k _ => hasDerivAt_spectralSpinFeature_plane U (I a) σ i j (v a k) t)
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun a _ => hi a)
  simpa only [spectralMonomialFeature, tensorFeature, spectralTensorPlaneDerivative,
    smul_eq_mul] using hd

lemma spectralTensorPlaneDerivative_abs_le {N m : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) :
    |spectralTensorPlaneDerivative U I d σ i j v| ≤ 2 * ∑ a, (d a : ℝ) := by
  have hp (a : Fin m) (s : Finset (Fin (d a))) :
      |∏ l ∈ s, spectralSpinFeature (matrixRotation U) (I a) σ (v a l)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun l _ => spectralSpinFeature_abs_le_one hN U (I a) σ (v a l))
  have ht (a : Fin m) :
      |tensorFeature (d a) (spectralSpinFeature (matrixRotation U) (I a) σ) (v a)| ≤ 1 := hp a Finset.univ
  have ho (a : Fin m) :
      |∏ b ∈ Finset.univ.erase a,
        tensorFeature (d b) (spectralSpinFeature (matrixRotation U) (I b) σ) (v b)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun b _ => ht b)
  have hk (a : Fin m) : |∑ k : Fin (d a),
      (∏ l ∈ Finset.univ.erase k, spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
        spectralSpinPlaneDerivative U σ i j (v a k)| ≤ 2 * d a := by
    calc
      _ ≤ ∑ k : Fin (d a), |(∏ l ∈ Finset.univ.erase k,
          spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) *
          spectralSpinPlaneDerivative U σ i j (v a k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (d a), (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (hp a _)
          (spectralSpinPlaneDerivative_abs_le hN U σ i j (v a k)) (abs_nonneg _) zero_le_one
      _ = _ := by simp <;> ring
  unfold spectralTensorPlaneDerivative
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a, 1 * (2 * (d a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (ho a) (hk a) (abs_nonneg _) zero_le_one
    _ = _ := by simp only [one_mul, Finset.mul_sum]

lemma measurable_spectralSpinPlaneDerivative {N : ℕ} (σ : Spin N) (i j a : Fin N) :
    Measurable (fun U : Orthogonal N => spectralSpinPlaneDerivative U σ i j a) := by
  unfold spectralSpinPlaneDerivative
  split_ifs
  · exact ((measurable_spinCoordinate σ j).div_const _).sub ((measurable_spinCoordinate σ i).div_const _)
  · exact ((measurable_spinCoordinate σ j).div_const _).sub measurable_const
  · exact measurable_const.sub ((measurable_spinCoordinate σ i).div_const _)
  · exact measurable_const

lemma measurable_spectralTensorPlaneDerivative {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (σ : Spin N)
    (i j : Fin N) (v : SpectralTensorIndex I d) :
    Measurable (fun U : Orthogonal N => spectralTensorPlaneDerivative U I d σ i j v) := by
  have hf (a : Fin m) (l : Fin (d a)) :
      Measurable (fun U : Orthogonal N => spectralSpinFeature (matrixRotation U) (I a) σ (v a l)) :=
    (measurable_spinCoordinate σ (v a l)).div_const _
  unfold spectralTensorPlaneDerivative tensorFeature
  exact Finset.measurable_sum _ fun a _ =>
    (Finset.measurable_prod _ fun b _ => Finset.measurable_prod _ fun l _ => hf b l).mul
      (Finset.measurable_sum _ fun k _ =>
        (Finset.measurable_prod _ fun l _ => hf a l).mul
          (measurable_spectralSpinPlaneDerivative σ i j (v a k)))

lemma hasDerivAt_spinTensorFeature_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) (t : ℝ) :
    HasDerivAt (fun s => spinTensorFeature (matrixRotation (planeRotation i j s * U)) I degree amplitude σ a)
      (spinTensorPlaneDerivative (planeRotation i j t * U) I degree amplitude σ i j a) t := by
  cases a with
  | inl a => exact hasDerivAt_const t _
  | inr a => exact (hasDerivAt_spectralMonomialFeature_plane U I (degree a.1) σ i j a.2 t).const_mul _

lemma spinTensorPlaneDerivative_abs_le {N m k : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) :
    |spinTensorPlaneDerivative U I degree amplitude σ i j a| ≤
      spinTensorDerivativeCap I degree amplitude a := by
  cases a with
  | inl a => simp only [spinTensorPlaneDerivative, spinTensorDerivativeCap, abs_zero, le_refl]
  | inr a =>
    rw [spinTensorPlaneDerivative, spinTensorDerivativeCap, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (spectralTensorPlaneDerivative_abs_le hN U I (degree a.1) σ i j a.2) (abs_nonneg _)

lemma measurable_spinTensorPlaneDerivative {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (σ : Spin N) (i j : Fin N) (a : SpinTensorIndex I degree) :
    Measurable (fun U : Orthogonal N => spinTensorPlaneDerivative U I degree amplitude σ i j a) := by
  cases a with
  | inl a => exact measurable_const
  | inr a => exact (measurable_spectralTensorPlaneDerivative I (degree a.1) σ i j a.2).const_mul _

lemma hasDerivAt_tensorNamespacedCoefficient_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) (t : ℝ) :
    HasDerivAt (fun s => tensorNamespacedCoefficients (matrixRotation (planeRotation i j s * U))
      I degree amplitude n v x q)
      (tensorNamespacedPlaneCoefficients (planeRotation i j t * U) I degree amplitude n v i j x q) t := by
  simp only [tensorNamespacedCoefficients, tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
  apply HasDerivAt.fun_sum
  intro a _
  split_ifs
  · exact (hasDerivAt_spinTensorFeature_plane U I degree amplitude x.1 i j a.2 t).const_mul _
  · exact hasDerivAt_const t 0

lemma measurable_tensorNamespacedPlaneCoefficient {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) :
    Measurable (fun U : Orthogonal N => tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x q) := by
  simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact (measurable_spinTensorPlaneDerivative I degree amplitude x.1 i j a.2).const_mul _
  · exact measurable_const

lemma tensorNamespacedPlaneCoefficient_abs_le {N m k : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : Spin N × LabeledLeaf n) (q : ℕ) :
    |tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x q| ≤
      tensorNamespacedDerivativeCap I degree amplitude n v := by
  simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply, tensorNamespacedDerivativeCap]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  have hc : 0 ≤ spinTensorDerivativeCap I degree amplitude a.2 := by
    cases a.2 <;> simp only [spinTensorDerivativeCap] <;> positivity
  split_ifs
  · rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (spinTensorPlaneDerivative_abs_le hN U I degree amplitude x.1 i j a.2) (NNReal.coe_nonneg _)
  · simpa only [abs_zero] using mul_nonneg (NNReal.coe_nonneg _) hc

/-- Mixed endpoint covariance is invariant under the injective change of
Gaussian coordinate namespaces, not just at coinciding endpoints. -/
lemma tensorNamespacedCoefficients_mixed_cross_eq {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amplitude n v x)
      (tensorNamespacedCoefficients V I degree amplitude n v y) =
    cylinderCross (tensorLeafCoefficients U I degree amplitude n v x)
      (tensorLeafCoefficients V I degree amplitude n v y) := by
  rw [tensorNamespacedCoefficients, tensorNamespacedCoefficients, tensorLeafCoefficients,
    tensorLeafCoefficients, featureCoefficients_cross, featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have ht : (tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2) =
      tensorNamespaceTag I degree (b.1, (labeledAddress n y.2).take b.1, b.2)) ↔
      treeFeatureTag n x.2 a = treeFeatureTag n y.2 b := by
    exact (tensorNamespaceTag_injective I degree).eq_iff.trans Encodable.encode_injective.eq_iff.symm
  simp only [ht]

/-- Coefficient differentiation commutes with the finite cross covariance. -/
lemma hasDerivAt_tensorNamespaced_cross_plane {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    HasDerivAt (fun s => cylinderCross
      (tensorNamespacedCoefficients (matrixRotation (planeRotation i j s * U)) I degree amplitude n v x)
      (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v y))
      (cylinderCross (tensorNamespacedPlaneCoefficients U I degree amplitude n v i j x)
        (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v y)) 0 := by
  simp only [tensorNamespacedCoefficients, tensorNamespacedPlaneCoefficients, featureCoefficients_cross]
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  by_cases h : tensorNamespaceTag I degree (a.1, (labeledAddress n x.2).take a.1, a.2) =
      tensorNamespaceTag I degree (b.1, (labeledAddress n y.2).take b.1, b.2)
  · simp only [h, ite_true, if_true]
    simpa only [planeRotation_zero, one_mul] using
      ((hasDerivAt_spinTensorFeature_plane U I degree amplitude x.1 i j a.2 0).const_mul
        (NNReal.sqrt (v a.1 a.2) : ℝ)).mul_const
          ((NNReal.sqrt (v b.1 b.2) : ℝ) * spinTensorFeature (matrixRotation U) I degree amplitude y.1 b.2)
  · simp only [h, ite_false, if_false]
    exact hasDerivAt_const 0 0

lemma spinTensorFeature_mixed_rotation_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ a : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial a : ℝ) *
      spinTensorFeature U I degree amplitude σ a * spinTensorFeature V I degree amplitude τ a) =
      (site : ℝ) * (∑ a, spinValue (σ a) * spinValue (τ a)) +
        ∑ r, (monomial r : ℝ) * amplitude r ^ 2 *
          ∏ a, mixedProjectedOverlap U V (I a) σ τ ^ degree r a := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · apply Finset.sum_congr rfl
    intro r _
    calc
      _ = (monomial r : ℝ) * amplitude r ^ 2 *
          ∑ a : SpectralTensorIndex I (degree r), spectralMonomialFeature U I (degree r) σ a *
            spectralMonomialFeature V I (degree r) τ a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [spectralMonomialFeature_mixed_cross]

private lemma tensorPrefix_weighted_sum (q : ℕ → ℝ) (n d : ℕ) (hd : d ≤ n) (c : ℝ) :
    (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i * c else 0) = q d * c := by
  calc
    _ = (∑ i : Fin (n + 1), if i.1 ≤ d then pathIncrement q i else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by rw [pathIncrement_prefix q n d hd]

private lemma tensorPrefix_linear_monomials {k : ℕ} (h : ℕ → ℝ)
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
      rw [Finset.sum_add_distrib, tensorPrefix_weighted_sum h n d hd a, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact tensorPrefix_weighted_sum (q j) n d hd (b j)

/-- The tensor covariance at two different rotations. -/
lemma tensorNamespacedPath_mixed_cross {N m k : ℕ} (U V : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (tensorNamespacedCoefficients V I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) y) =
      h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)) +
        ∑ r, amplitude r ^ 2 * (∏ a, mixedProjectedOverlap U V (I a) x.1 y.1 ^ degree r a) *
          treeOverlap n x.2 y.2 ^ treeDegree r := by
  rw [tensorNamespacedCoefficients_mixed_cross_eq, tensorLeafCoefficients_cross]
  simp_rw [tensorPathProfile, spinTensorFeature_mixed_rotation_cross, varianceIncrement_coe hh h0,
    varianceIncrement_coe (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  have he := tensorPrefix_linear_monomials h (fun r => monomialPath n (treeDegree r)) n
    (labeledCommonDepth n x.2 y.2) (labeledCommonDepth_le n x.2 y.2)
    (∑ a, spinValue (x.1 a) * spinValue (y.1 a))
    (fun r => amplitude r ^ 2 * ∏ a, mixedProjectedOverlap U V (I a) x.1 y.1 ^ degree r a)
  simp_rw [mul_assoc] at he ⊢
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  simp only [monomialPath, treeOverlap]
  ring

/-- The coefficient derivative is exactly the one-endpoint spectral/tree
covariance derivative used in the normalized Ward error estimate. -/
theorem tensorNamespacedPlaneCross_eq {N m k : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (i j : Fin N) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedPlaneCoefficients U I degree amplitude n
      (fun a => tensorPathProfile I degree n treeDegree h a) i j x)
      (tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n
        (fun a => tensorPathProfile I degree n treeDegree h a) y) =
      ∑ r, amplitude r ^ 2 * treeOverlap n x.2 y.2 ^ treeDegree r *
        spectralMonomialEndpointDerivative U I (degree r) i j x.1 y.1 := by
  have hd := hasDerivAt_tensorNamespaced_cross_plane U I degree amplitude n
    (fun a => tensorPathProfile I degree n treeDegree h a) i j x y
  simp_rw [tensorNamespacedPath_mixed_cross _ _ I degree amplitude n treeDegree h hh h0 x y] at hd
  have he := (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ =>
    ((hasDerivAt_spectralMonomial_mixed_plane U I (degree r) i j x.1 y.1).const_mul
      (amplitude r ^ 2)).mul_const (treeOverlap n x.2 y.2 ^ treeDegree r))).const_add
        (h (labeledCommonDepth n x.2 y.2) * (∑ a, spinValue (x.1 a) * spinValue (y.1 a)))
  have hu := hd.unique he
  calc
    _ = ∑ r, amplitude r ^ 2 * spectralMonomialEndpointDerivative U I (degree r) i j x.1 y.1 *
        treeOverlap n x.2 y.2 ^ treeDegree r := hu
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- A finite spin/leaf restriction has one Gaussian coordinate prefix
containing both the actual Hamiltonian coefficients and their plane
derivatives, uniformly in the rotation. -/
lemma finite_tensorNamespaced_support_bound {S : Type*} [Fintype S] {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (i j : Fin N) (x : S → Spin N × LabeledLeaf n) :
    ∃ d : ℕ,
      (∀ U : Orthogonal N, ∀ s q, q ∈ (tensorNamespacedCoefficients (matrixRotation U)
        I degree amplitude n v (x s)).support → q < d + 1) ∧
      (∀ U : Orthogonal N, ∀ s q, q ∈ (tensorNamespacedPlaneCoefficients U
        I degree amplitude n v i j (x s)).support → q < d + 1) := by
  classical
  let tag := fun s (a : Fin (n + 1) × SpinTensorIndex I degree) =>
    tensorNamespaceTag I degree (a.1, (labeledAddress n (x s).2).take a.1, a.2)
  let d := ∑ s : S, ∑ a : Fin (n + 1) × SpinTensorIndex I degree, (tag s a + 1)
  have ht (s : S) (a : Fin (n + 1) × SpinTensorIndex I degree) : tag s a < d + 1 := by
    have ha : tag s a + 1 ≤ ∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag s b + 1) :=
      Finset.single_le_sum (f := fun b : Fin (n + 1) × SpinTensorIndex I degree => tag s b + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have hs : (∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag s b + 1)) ≤ d :=
      Finset.single_le_sum
        (f := fun t : S => ∑ b : Fin (n + 1) × SpinTensorIndex I degree, (tag t b + 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    omega
  have hz (s : S) (q : ℕ) (hq : d + 1 ≤ q) (a : Fin (n + 1) × SpinTensorIndex I degree) :
      tag s a ≠ q := by have := ht s a; omega
  refine ⟨d, ?_, ?_⟩
  · intro U s q hq
    by_contra hn
    have he : tensorNamespacedCoefficients (matrixRotation U) I degree amplitude n v (x s) q = 0 := by
      simp only [tensorNamespacedCoefficients, featureCoefficients_apply]
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (hz s q (Nat.le_of_not_gt hn) a)
    exact Finsupp.mem_support_iff.mp hq he
  · intro U s q hq
    by_contra hn
    have he : tensorNamespacedPlaneCoefficients U I degree amplitude n v i j (x s) q = 0 := by
      simp only [tensorNamespacedPlaneCoefficients, featureCoefficients_apply]
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (hz s q (Nat.le_of_not_gt hn) a)
    exact Finsupp.mem_support_iff.mp hq he

lemma measurable_tensorNamespacedCoefficient {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : Spin N × LabeledLeaf n) (q : ℕ) :
    Measurable (fun U : SpecialOrthogonal N =>
      tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x q) := by
  simp only [tensorNamespacedCoefficients, featureCoefficients_apply]
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact (measurable_spinTensorFeature I degree amplitude x.1 a.2).const_mul _
  · exact measurable_const

/-- The exact covariance appearing after finite Gaussian integration by
parts contracts to the tensor Ward error. -/
theorem tensorNamespacedPlane_contraction_eq {N m : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (n : ℕ) (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (η θ : Spin N) (x y : Spin N × LabeledLeaf n) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, spinCoordinate U η i * spinCoordinate U θ j *
      cylinderCross (tensorNamespacedPlaneCoefficients U I degree (tensorPerturbationAmplitude N u) n
        (fun a => tensorPathProfile I degree n treeDegree h a) i j x)
        (tensorNamespacedCoefficients (matrixRotation U) I degree (tensorPerturbationAmplitude N u) n
          (fun a => tensorPathProfile I degree n treeDegree h a) y) =
      tensorWardPerturbationError U I degree treeDegree n u J K η θ x y := by
  simp_rw [tensorNamespacedPlaneCross_eq U I degree (tensorPerturbationAmplitude N u) n treeDegree h hh h0]
  exact (tensorWardPerturbationError_eq U I degree treeDegree n u J K η θ x y).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorHaarWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian/Haar Ward identities. The Gaussian correction is
proved from integration by parts, while Haar invariance is differentiated
on genuine determinant-one plane rotations. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

lemma measurable_finiteGibbsVariation {Ω : Type*} [MeasurableSpace Ω]
    (w : S → ℝ) (H O dH dO : Ω → S → ℝ)
    (hH : ∀ x, Measurable (fun ω => H ω x))
    (hO : ∀ x, Measurable (fun ω => O ω x))
    (hdH : ∀ x, Measurable (fun ω => dH ω x))
    (hdO : ∀ x, Measurable (fun ω => dO ω x)) :
    Measurable (fun ω => finiteGibbsVariation w (H ω) (O ω) (dH ω) (dO ω)) :=
  ((measurable_gibbsAverage w H dO hH hdO).add
    (measurable_gibbsAverage w H (fun ω x => O ω x * dH ω x) hH
      (fun x => (hO x).mul (hdH x)))).sub
    ((measurable_gibbsAverage w H O hH hO).mul (measurable_gibbsAverage w H dH hH hdH))

lemma finiteGibbsVariation_add_H (w H O A Y dO : S → ℝ) :
    finiteGibbsVariation w H O (fun x => A x + Y x) dO =
      finiteGibbsVariation w H O A dO +
        (gibbsAverage w H (fun x => O x * Y x) -
          gibbsAverage w H O * gibbsAverage w H Y) := by
  simp only [finiteGibbsVariation, gibbsAverage, mul_add, Finset.sum_add_distrib]
  ring

lemma integrable_gaussian_finiteGibbsVariation {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O A dO : S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O A dO)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  simp only [finiteGibbsVariation, gibbsAverage_mul_gibbsAverage]
  exact ((integrable_gaussian_gibbs_test hw H dO C).add
    (integrable_gaussian_gibbs_test hw H (fun x => O x * A x) C)).sub
    (integrable_gaussian_pair_test hw H (fun x y => O x * A y) C)

/-- Pointwise averaging of the normalized Gibbs rotation derivative over
finite Gaussian marks leaves precisely its explicit covariance correction. -/
lemma integral_gaussian_finiteGibbsVariation {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O A dO : S → ℝ) (D C : S → Fin (d + 1) → ℝ) :
    (∫ g, finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O
      (fun x => A x + linearGaussian D g x) dO
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      (∫ g, finiteGibbsVariation w (fun x => H x + linearGaussian C g x) O A dO
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O (gaussianCross D C)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  simp_rw [finiteGibbsVariation_add_H]
  have hadd := integral_add (integrable_gaussian_finiteGibbsVariation hw H O A dO C)
    ((integrable_gaussian_gibbs_linear_test hw H O D C).sub
      (integrable_gaussian_gibbs_linear_product hw H O D C))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, gaussian_gibbs_covariance_insertion hw]

omit [Fintype S] in
lemma abs_linearGaussian_le {d : ℕ} (A : S → Fin d → ℝ) (g : Fin d → ℝ)
    (cap : Fin d → ℝ) (hA : ∀ x a, |A x a| ≤ cap a) (x : S) :
    |linearGaussian A g x| ≤ ∑ a, cap a * |g a| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hA x a) (abs_nonneg _)

/-- A finite-prior Haar Ward identity with Gaussian coefficient tensors.
The assumptions are elementary measurability, derivatives and finite
bounds; the covariance correction is derived, not postulated. -/
theorem integral_special_gaussian_gibbs_rotation_identity {N d : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H O : SpecialOrthogonal N → S → ℝ) (C : SpecialOrthogonal N → S → Fin (d + 1) → ℝ)
    (hHm : ∀ x, Measurable (fun U => H U x))
    (hOm : ∀ x, Measurable (fun U => O U x))
    (hCm : ∀ x a, Measurable (fun U => C U x a))
    (dH dO : ℝ → SpecialOrthogonal N → S → ℝ)
    (dC : ℝ → SpecialOrthogonal N → S → Fin (d + 1) → ℝ)
    (hdHm : ∀ x, Measurable (fun U => dH 0 U x))
    (hdOm : ∀ x, Measurable (fun U => dO 0 U x))
    (hdCm : ∀ x a, Measurable (fun U => dC 0 U x a))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => H (R s * U) x) (dH t U x) t)
    (hOd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x,
      HasDerivAt (fun s => O (R s * U) x) (dO t U x) t)
    (hCd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x a,
      HasDerivAt (fun s => C (R s * U) x a) (dC t U x a) t)
    (K L M : ℝ) (cap : Fin (d + 1) → ℝ) (hK : 0 ≤ K)
    (hOb : ∀ U x, |O U x| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x, |dH t U x| ≤ L)
    (hdOb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x, |dO t U x| ≤ M)
    (hdCb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ x a, |dC t U x a| ≤ cap a) :
    (∫ U, (∫ g, finiteGibbsVariation w (fun x => H U x + linearGaussian (C U) g x)
        (O U) (dH 0 U) (dO 0 U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun x => H U x + linearGaussian (C U) g x)
        (O U) (gaussianCross (dC 0 U) (C U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) ∂μ) = 0 := by
  let γ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  let Lg := fun g : Fin (d + 1) → ℝ => L + ∑ a, cap a * |g a|
  let V := fun (U : SpecialOrthogonal N) (g : Fin (d + 1) → ℝ) =>
    finiteGibbsVariation w (fun x => H U x + linearGaussian (C U) g x) (O U)
      (fun x => dH 0 U x + linearGaussian (dC 0 U) g x) (dO 0 U)
  have hHg (g : Fin (d + 1) → ℝ) (x : S) :
      Measurable (fun U => H U x + linearGaussian (C U) g x) :=
    (hHm x).add (Finset.measurable_sum _ fun a _ => (hCm x a).mul_const _)
  have hdHg (g : Fin (d + 1) → ℝ) (x : S) :
      Measurable (fun U => dH 0 U x + linearGaussian (dC 0 U) g x) :=
    (hdHm x).add (Finset.measurable_sum _ fun a _ => (hdCm x a).mul_const _)
  have hgb (g : Fin (d + 1) → ℝ) (U : SpecialOrthogonal N) (t : ℝ)
      (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (x : S) :
      |dH t U x + linearGaussian (dC t U) g x| ≤ Lg g :=
    (abs_add_le _ _).trans (add_le_add (hdHb U t ht x)
      (abs_linearGaussian_le (dC t U) g cap (hdCb U t ht) x))
  have hz (g : Fin (d + 1) → ℝ) : (∫ U, V U g ∂μ) = 0 := by
    exact integral_special_gibbs_rotation_identity μ R hR hw
      (fun U x => H U x + linearGaussian (C U) g x) O
      (hHg g) hOm (fun t U x => dH t U x + linearGaussian (dC t U) g x) dO
      (hdHg g) hdOm
      (fun U t ht x => (hHd U t ht x).add
        (HasDerivAt.fun_sum fun a _ => (hCd U t ht x a).mul_const (g a)))
      hOd K (Lg g) M hK hOb (fun U t ht x => hgb g U t ht x) hdOb
  have hmV : Measurable (Function.uncurry V) :=
    measurable_finiteGibbsVariation w _ _ _ _
      (fun x => ((hHm x).comp measurable_fst).add
        (Finset.measurable_sum _ fun a _ => ((hCm x a).comp measurable_fst).mul
          ((measurable_pi_apply a).comp measurable_snd)))
      (fun x => (hOm x).comp measurable_fst)
      (fun x => ((hdHm x).comp measurable_fst).add
        (Finset.measurable_sum _ fun a _ => ((hdCm x a).comp measurable_fst).mul
          ((measurable_pi_apply a).comp measurable_snd)))
      (fun x => (hdOm x).comp measurable_fst)
  have hiL : Integrable Lg γ := (integrable_const L).add
    (integrable_finsetSum _ fun a _ =>
      (((measurePreserving_eval (fun _ : Fin (d + 1) => gaussianReal 0 1) a).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).abs.const_mul (cap a)))
  have hiB : Integrable (fun g => M + 2 * K * Lg g) γ :=
    (integrable_const M).add (hiL.const_mul (2 * K))
  have hiV : Integrable (Function.uncurry V) (μ.prod γ) :=
    (hiB.comp_snd μ).mono' hmV.aestronglyMeasurable (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact abs_gibbsVariation_le hw _ _ _ _ hK (hOb p.1)
        (fun x => hgb p.2 p.1 0 (by norm_num) x) (hdOb p.1 0 (by norm_num)))
  have he : (∫ U, ∫ g, V U g ∂γ ∂μ) = 0 := by
    rw [integral_integral_swap hiV]
    simp only [hz, integral_zero]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext U
  exact (integral_gaussian_finiteGibbsVariation hw (H U) (O U) (dH 0 U) (dO 0 U)
    (dC 0 U) (C U)).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spin/leaf pair application of the spectral Haar Ward identity.
The spin test is fixed under rotations and may be any function of total
overlap. Arbitrary finite leaf restrictions and zero prior weights are allowed. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

lemma measurable_gaussianWardCorrection [Fintype S] {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (C : S → Fin d → ℝ) (K : S → S → ℝ) :
    Measurable (fun g => gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O K) := by
  unfold gaussianWardCorrection gibbsAverage gibbsPairAverage gibbsTripleAverage
  change Measurable (fun g =>
    (∑ x, gaussianGibbs w H C g x * (O x * K x x)) -
      (∑ x, ∑ y, gaussianGibbs w H C g x * gaussianGibbs w H C g y * (O x * K x y)) -
      (∑ x, ∑ y, gaussianGibbs w H C g x * gaussianGibbs w H C g y * (O x * (K y x + K y y))) +
      2 * ∑ x, ∑ y, ∑ z, gaussianGibbs w H C g x * gaussianGibbs w H C g y * gaussianGibbs w H C g z * (O x * K y z))
  have hp (x : S) := (continuous_gaussianGibbs hw H C x).measurable
  exact (((Finset.measurable_sum _ fun x _ => (hp x).mul_const _).sub
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      ((hp x).mul (hp y)).mul_const _)).sub
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      ((hp x).mul (hp y)).mul_const _)).add
    ((Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      Finset.measurable_sum _ fun z _ => (((hp x).mul (hp y)).mul (hp z)).mul_const _).const_mul 2)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTruncatedDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-replica diagonal Haar Ward identity for the actual finite
spin/leaf tensor model. The main quadratic coefficient has no extra factor two. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

theorem tensorRestriction_diagonal_ward_prefix [Fintype S] {N m k n d : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) :
    let C := tensorRestrictionPrefix (d := d + 1) I degree amplitude v x
    let D := tensorRestrictionPlanePrefix (d := d + 1) I degree amplitude v x i j
    let H := tensorRestrictionBase eig c x
    let O := tensorRestrictionDiagonalObservable i j x
    (∫ U, (∫ g, finiteGibbsVariation w (fun s => H U s + linearGaussian (C U) g s)
        (O U) (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun s => H U s + linearGaussian (C U) g s)
        (O U) (gaussianCross (D U) (C U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) ∂μ) = 0 := by
  intro C D H O
  let R := specialPlaneRotation i j
  let dH := fun (t : ℝ) (U : SpecialOrthogonal N) (s : S) => (eig i - eig j) * O (R t * U) s
  let dO := fun (t : ℝ) (U : SpecialOrthogonal N) => tensorRestrictionDiagonalVariation i j x (R t * U)
  let dC := fun (t : ℝ) (U : SpecialOrthogonal N) => D (R t * U)
  have hR : R 0 = 1 := specialPlaneRotation_zero i j
  have hOm (s : S) : Measurable (fun U => O U s) :=
    ((measurable_spinCoordinate (x s).1 i).mul (measurable_spinCoordinate (x s).1 j)).comp
      measurable_specialToOrthogonal
  have hHm (s : S) : Measurable (fun U => H U s) :=
    (measurable_orbitHamiltonian eig c (x s).1).comp measurable_specialToOrthogonal
  have hCm (s : S) (a : Fin (d + 1)) : Measurable (fun U => C U s a) :=
    measurable_tensorNamespacedCoefficient I degree amplitude n v (x s) a
  have hdHm (s : S) : Measurable (fun U => dH 0 U s) := by
    simpa only [dH, hR, one_mul] using (hOm s).const_mul (eig i - eig j)
  have hdOm (s : S) : Measurable (fun U => dO 0 U s) := by
    simp only [dO, hR, one_mul, tensorRestrictionDiagonalVariation]
    exact (((measurable_spinCoordinate (x s).1 j).pow_const 2).sub
      ((measurable_spinCoordinate (x s).1 i).pow_const 2)).comp measurable_specialToOrthogonal
  have hdCm (s : S) (a : Fin (d + 1)) : Measurable (fun U => dC 0 U s a) := by
    simp only [dC, hR, one_mul, D, tensorRestrictionPlanePrefix]
    exact (measurable_tensorNamespacedPlaneCoefficient I degree amplitude n v i j (x s) a).comp
      measurable_specialToOrthogonal
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s,
      HasDerivAt (fun r => H (R r * U) s) (dH t U s) t := by
    intro U t _ s
    simpa only [H, tensorRestrictionBase, orbitHamiltonian, dH, O, tensorRestrictionDiagonalObservable,
      R, map_mul, specialToOrthogonal_planeRotation, coordinateProduct, spinCoordinate, mul_assoc] using
      (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig (x s).1 t).add_const (fieldEnergy c (x s).1)
  have hOd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s,
      HasDerivAt (fun r => O (R r * U) s) (dO t U s) t := by
    intro U t _ s
    simpa only [O, tensorRestrictionDiagonalObservable, dO, tensorRestrictionDiagonalVariation,
      R, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_plane_coordinateProduct i j hij (specialToOrthogonal U) (x s).1 t
  have hCd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s a,
      HasDerivAt (fun r => C (R r * U) s a) (dC t U s a) t := by
    intro U t _ s a
    simpa only [C, D, tensorRestrictionPrefix, tensorRestrictionPlanePrefix, dC,
      ← matrixRotation_specialToOrthogonal, R, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_tensorNamespacedCoefficient_plane (specialToOrthogonal U) I degree amplitude n v i j (x s) a t
  have hOb : ∀ U s, |O U s| ≤ N := fun U s => abs_coordinateProduct_le i j _ (x s).1
  have hHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s, |dH t U s| ≤ |eig i - eig j| * N := by
    intro U t _ s
    rw [show dH t U s = (eig i - eig j) * O (R t * U) s from rfl, abs_mul]
    exact mul_le_mul_of_nonneg_left (hOb _ _) (abs_nonneg _)
  have hOdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s, |dO t U s| ≤ N :=
    fun U t _ s => abs_coordinateSquareDifference_le i j _ (x s).1
  have hCdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s a,
      |dC t U s a| ≤ tensorNamespacedDerivativeCap I degree amplitude n v :=
    fun U t _ s a => tensorNamespacedPlaneCoefficient_abs_le hN _ I degree amplitude n v i j (x s) a
  have hwrd := integral_special_gaussian_gibbs_rotation_identity μ R hR hw H O C hHm hOm hCm
    dH dO dC hdHm hdOm hdCm hHd hOd hCd N (|eig i - eig j| * N) N
    (fun _ => tensorNamespacedDerivativeCap I degree amplitude n v) (Nat.cast_nonneg _) hOb hHb hOdB hCdB
  simpa only [dH, dO, dC, hR, one_mul] using hwrd

/-- The one-replica Ward equation for the actual full Gaussian coordinate
law on any finite spin/leaf restriction. -/
theorem tensorRestriction_diagonal_ward [Fintype S] {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) :
    let H := tensorRestrictionHamiltonian eig c I degree amplitude v x
    let O := tensorRestrictionDiagonalObservable i j x
    let K := tensorRestrictionCovarianceDerivative I degree amplitude v x i j
    (∫ U, (∫ g, finiteGibbsVariation w (H U g) (O U)
      (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
      ∂gaussianCoordinates) +
      ∫ g, gaussianWardCorrection w (H U g) (O U) (K U) ∂gaussianCoordinates ∂μ) = 0 := by
  intro H O K
  obtain ⟨d, hC, hD⟩ := finite_tensorNamespaced_support_bound I degree amplitude n v i j x
  let Cp := tensorRestrictionPrefix (d := d + 1) I degree amplitude v x
  let Dp := tensorRestrictionPlanePrefix (d := d + 1) I degree amplitude v x i j
  let Hp := fun U g s => tensorRestrictionBase eig c x U s + linearGaussian (Cp U) g s
  have hfield (U : SpecialOrthogonal N) (g : ℕ → ℝ) (s : S) :
      H U g s = Hp U (fun a : Fin (d + 1) => g a) s := by
    change tensorRestrictionBase eig c x U s +
      cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s)) g = _
    simp only [← matrixRotation_specialToOrthogonal]
    rw [cylinderField_eq_prefix _ (hC (specialToOrthogonal U) s)]
    rfl
  have hkernel (U : SpecialOrthogonal N) (s t : S) :
      K U s t = gaussianCross (Dp U) (Cp U) s t :=
    cylinderCross_prefix _ _ (hD (specialToOrthogonal U) s)
  have hfield_fun (U : SpecialOrthogonal N) (g : ℕ → ℝ) :
      H U g = Hp U (fun a : Fin (d + 1) => g a) := funext (hfield U g)
  have hkernel_fun (U : SpecialOrthogonal N) : K U = gaussianCross (Dp U) (Cp U) :=
    funext fun s => funext fun t => hkernel U s t
  have hmeasH (U : SpecialOrthogonal N) (s : S) : Measurable (fun g => Hp U g s) := by
    unfold Hp linearGaussian
    fun_prop
  have hmean (U : SpecialOrthogonal N) :
      (∫ g, finiteGibbsVariation w (H U g) (O U)
        (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂gaussianCoordinates) =
      ∫ g, finiteGibbsVariation w (Hp U g) (O U)
        (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_finiteGibbsVariation w _ (fun _ => O U)
        (fun _ s => (eig i - eig j) * O U s) (fun _ => tensorRestrictionDiagonalVariation i j x U)
        (hmeasH U) (fun _ => measurable_const) (fun _ => measurable_const)
        (fun _ => measurable_const)).aestronglyMeasurable
  have hmeanK (U : SpecialOrthogonal N) :
      (∫ g, gaussianWardCorrection w (H U g) (O U) (K U) ∂gaussianCoordinates) =
      ∫ g, gaussianWardCorrection w (Hp U g) (O U) (gaussianCross (Dp U) (Cp U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun, hkernel_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_gaussianWardCorrection hw (tensorRestrictionBase eig c x U) (O U)
        (Cp U) (gaussianCross (Dp U) (Cp U))).aestronglyMeasurable
  simp_rw [hmean, hmeanK]
  exact tensorRestriction_diagonal_ward_prefix hN μ hw eig c I degree amplitude v x i j hij

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardCorrectionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds on the complete finite Gaussian Ward correction after
spectral coordinate contraction. Constants do not depend on the leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

lemma gibbsPairAverage_const_mul (w H : S → ℝ) (O : S → S → ℝ) (a : ℝ) :
    gibbsPairAverage w H (fun x y => a * O x y) = a * gibbsPairAverage w H O := by
  simp only [gibbsPairAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma gibbsTripleAverage_const_mul (w H : S → ℝ) (O : S → S → S → ℝ) (a : ℝ) :
    gibbsTripleAverage w H (fun x y z => a * O x y z) = a * gibbsTripleAverage w H O := by
  simp only [gibbsTripleAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma abs_gibbsPairAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (O : S → S → ℝ) {B : ℝ} (hO : ∀ x y, |O x y| ≤ B) :
    |gibbsPairAverage w H O| ≤ B := by
  have he : gibbsPairAverage w H O = gibbsAverage w H (fun x => gibbsAverage w H (O x)) := by
    simp only [gibbsPairAverage, gibbsAverage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  exact abs_gibbsAverage_le hw H _ (fun x => abs_gibbsAverage_le hw H (O x) (hO x))

lemma abs_gibbsTripleAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (O : S → S → S → ℝ) {B : ℝ} (hO : ∀ x y z, |O x y z| ≤ B) :
    |gibbsTripleAverage w H O| ≤ B := by
  have he : gibbsTripleAverage w H O = gibbsAverage w H (fun x => gibbsPairAverage w H (O x)) := by
    simp only [gibbsTripleAverage, gibbsAverage, gibbsPairAverage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  exact abs_gibbsAverage_le hw H _ (fun x => abs_gibbsPairAverage_le hw H (O x) (hO x))

lemma gibbsKernelCorrection_product (w H O : S → ℝ) (K : S → S → ℝ) :
    gibbsKernelCorrection w H (fun s x y => O s * K x y) = gaussianWardCorrection w H O K := by
  simp only [gibbsKernelCorrection, gaussianWardCorrection, mul_add]

lemma gibbsKernelCorrection_finset_sum (w H : S → ℝ) (t : Finset ι) (a : ℝ)
    (C : ι → S → S → S → ℝ) :
    gibbsKernelCorrection w H (fun s x y => ∑ i ∈ t, a * C i s x y) =
      ∑ i ∈ t, a * gibbsKernelCorrection w H (C i) := by
  unfold gibbsKernelCorrection
  have he (s x : S) : (∑ i ∈ t, a * C i s x s) + (∑ i ∈ t, a * C i s x x) =
      ∑ i ∈ t, a * (C i s x s + C i s x x) := by
    simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [he, gibbsAverage_finset_sum, gibbsPairAverage_finset_sum, gibbsTripleAverage_finset_sum,
    gibbsAverage_const_mul, gibbsPairAverage_const_mul, gibbsTripleAverage_const_mul]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, mul_add]
  simp only [mul_left_comm 2 a]

/-- Six times the contraction bound controls the entire Gaussian ratio
correction, including both normalization insertions. -/
lemma gibbsKernelCorrection_abs_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (C : S → S → S → ℝ) {B : ℝ}
    (hC : ∀ s x y, |C s x y| ≤ B) :
    |gibbsKernelCorrection w H C| ≤ 6 * B := by
  have h1 := abs_gibbsAverage_le hw H (fun s => C s s s) (fun s => hC s s s)
  have h2 := abs_gibbsPairAverage_le hw H (fun s x => C s s x) (fun s x => hC s s x)
  have h3 := abs_gibbsPairAverage_le hw H (fun s x => C s x s + C s x x)
    (fun s x => (abs_add_le _ _).trans (add_le_add (hC s x s) (hC s x x)))
  have h4 := abs_gibbsTripleAverage_le hw H C hC
  unfold gibbsKernelCorrection
  calc
    _ ≤ |gibbsAverage w H (fun s => C s s s)| + |gibbsPairAverage w H (fun s x => C s s x)| +
        |gibbsPairAverage w H (fun s x => C s x s + C s x x)| +
        |2 * gibbsTripleAverage w H C| :=
      (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)
    _ ≤ 6 * B := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalWardCorrectionBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized one-replica Gaussian Ward correction is quadratic in
the perturbation scale, uniformly in the finite leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*}

lemma tensorRestrictionDiagonalWardContraction_eq {N m n : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) (s p q : S) :
    tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x s p q =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionDiagonalObservable i j x U s *
          tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U p q := by
  exact (tensorNamespacedPlane_contraction_eq (specialToOrthogonal U) I degree treeDegree n u h hh h0
    J K (x s).1 (x s).1 (x p) (x q)).symm

lemma tensorRestrictionDiagonalWardCorrection_eq [Fintype S] {N m n : ℕ} (U : SpecialOrthogonal N)
    (w H : S → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) :
    gibbsKernelCorrection w H
      (tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        gaussianWardCorrection w H (tensorRestrictionDiagonalObservable i j x U)
          (tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U) := by
  have he : tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x =
      fun s p q => ∑ a ∈ J ×ˢ K, (N : ℝ)⁻¹ ^ 2 *
        (tensorRestrictionDiagonalObservable a.1 a.2 x U s *
          tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x a.1 a.2 U p q) := by
    funext s p q
    rw [tensorRestrictionDiagonalWardContraction_eq U I degree treeDegree u h hh h0 J K x s p q]
    simp only [Finset.sum_product, ← Finset.mul_sum]
  rw [he, gibbsKernelCorrection_finset_sum]
  simp only [gibbsKernelCorrection_product, Finset.sum_product, Finset.mul_sum]

/-- The exact one-replica Gaussian correction, with its single covariance
kernel rather than a doubled Hamiltonian coefficient. -/
theorem tensorRestriction_actualDiagonalWardCorrection_abs_le [Fintype S] {N m n : ℕ}
    (hN : 0 < N) (U : SpecialOrthogonal N) {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) :
    |(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
      gaussianWardCorrection w H (tensorRestrictionDiagonalObservable i j x U)
        (tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
          (fun a => tensorPathProfile I degree n treeDegree h a) x i j U)| ≤
      48 * D * perturbationScale N ^ 2 := by
  rw [← tensorRestrictionDiagonalWardCorrection_eq U w H I degree treeDegree u h hh h0 J K x]
  have hb (s p q : S) :
      |tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x s p q| ≤
        8 * D * perturbationScale N ^ 2 :=
    tensorWardPerturbationError_abs_le hN (specialToOrthogonal U) I degree treeDegree n u hu D hD hdegree
      J K (x s).1 (x s).1 (x p) (x q)
  exact (gibbsKernelCorrection_abs_le hw H _ hb).trans_eq (by ring)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability and bounded integrability of the actual finite
principal Ward term and its Gaussian correction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]

lemma measurable_finiteGibbs (w : S → ℝ) (H : Ω → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s)) (s : S) :
    Measurable (fun ω => finiteGibbs w (H ω) s) := by
  unfold finiteGibbs finitePartition
  exact (measurable_const.mul (hH s).exp).div
    (Finset.measurable_sum _ fun t _ => measurable_const.mul (hH t).exp)

lemma measurable_gibbsPairAverage (w : S → ℝ) (H : Ω → S → ℝ) (O : Ω → S → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s t, Measurable (fun ω => O ω s t)) :
    Measurable (fun ω => gibbsPairAverage w (H ω) (O ω)) := by
  unfold gibbsPairAverage
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun t _ =>
    ((measurable_finiteGibbs w H hH s).mul (measurable_finiteGibbs w H hH t)).mul (hO s t)

lemma measurable_gibbsTripleAverage (w : S → ℝ) (H : Ω → S → ℝ) (O : Ω → S → S → S → ℝ)
    (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s t u, Measurable (fun ω => O ω s t u)) :
    Measurable (fun ω => gibbsTripleAverage w (H ω) (O ω)) := by
  unfold gibbsTripleAverage
  exact Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun t _ =>
    Finset.measurable_sum _ fun u _ =>
      (((measurable_finiteGibbs w H hH s).mul (measurable_finiteGibbs w H hH t)).mul
        (measurable_finiteGibbs w H hH u)).mul (hO s t u)

lemma measurable_gaussianWardCorrection_joint (w : S → ℝ) (H O : Ω → S → ℝ)
    (K : Ω → S → S → ℝ) (hH : ∀ s, Measurable (fun ω => H ω s))
    (hO : ∀ s, Measurable (fun ω => O ω s)) (hK : ∀ s t, Measurable (fun ω => K ω s t)) :
    Measurable (fun ω => gaussianWardCorrection w (H ω) (O ω) (K ω)) := by
  unfold gaussianWardCorrection
  exact (((measurable_gibbsAverage w H _ hH (fun s => (hO s).mul (hK s s))).sub
    (measurable_gibbsPairAverage w H _ hH (fun s t => (hO s).mul (hK s t)))).sub
    (measurable_gibbsPairAverage w H _ hH (fun s t => (hO s).mul ((hK t s).add (hK t t))))).add
    ((measurable_gibbsTripleAverage w H _ hH (fun s t u => (hO s).mul (hK t u))).const_mul 2)

omit [Fintype S] [MeasurableSpace Ω] in
lemma measurable_tensorRestrictionHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n) (s : S) :
    Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2 s) :=
  (((measurable_orbitHamiltonian eig c (x s).1).comp measurable_specialToOrthogonal).comp
    measurable_fst).add (measurable_tensorNamespacedFields_joint I degree amplitude n v (x s))

omit [Fintype S] [MeasurableSpace Ω] in
lemma measurable_tensorNamespacedPlaneCross {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (i j : Fin N)
    (x y : Spin N × LabeledLeaf n) :
    Measurable (fun U : SpecialOrthogonal N => cylinderCross
      (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j x)
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v y)) := by
  simp only [tensorNamespacedPlaneCoefficients, tensorNamespacedCoefficients, featureCoefficients_cross]
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro b _
  split_ifs
  · exact (((measurable_spinTensorPlaneDerivative I degree amplitude x.1 i j a.2).comp
      measurable_specialToOrthogonal).const_mul _).mul
        ((measurable_spinTensorFeature I degree amplitude y.1 b.2).const_mul _)
  · exact measurable_const

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCountableHamiltonian
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential integrability of the actual tensor Hamiltonian for every
countable probability prior, before specializing to random cascade weights. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma tensorCountableHamiltonian_exp_integrable_ae {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : X → Spin N × LabeledLeaf n) :
    ∀ᵐ z ∂μ.prod gaussianCoordinates, Integrable
      (fun s => Real.exp (tensorRestrictionHamiltonian eig c I degree amplitude
        (fun a => tensorPathProfile I degree n treeDegree h a) x z.1 z.2 s)) ν := by
  let A := fun (U : SpecialOrthogonal N) (s : X) =>
    tensorNamespacedCoefficients (specialRotation U) I degree amplitude n
      (fun a => tensorPathProfile I degree n treeDegree h a) (x s)
  have hA : Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      cylinderField (A p.1.1 p.2) p.1.2) :=
    measurable_from_prod_countable_left (fun s =>
      measurable_tensorNamespacedFields_joint I degree amplitude n
        (fun a => tensorPathProfile I degree n treeDegree h a) (x s))
  have hcap (U : SpecialOrthogonal N) (s : X) :
      (A U s).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation U) I degree amplitude n treeDegree h hh h0 (x s)
  have he := randomCoefficient_all_exp_ae (P := μ) (ν := fun _ : SpecialOrthogonal N => ν)
    measurable_const A hA hcap
  filter_upwards [he] with z hz
  have hi : Integrable (fun s => Real.exp (cylinderField (A z.1 s) z.2)) ν := by
    simpa only [one_mul] using hz 1
  let E : Spin N → ℝ := orbitHamiltonian eig c (specialToOrthogonal z.1)
  have hb (s : X) : E (x s).1 ≤ ∑ σ : Spin N, |E σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun σ _ => abs_nonneg (E σ)) (Finset.mem_univ _))
  exact integrable_exp_bounded_add hi (measurable_of_countable (fun s => E (x s).1)) hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCascadeReplicaAverage
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual enriched replica average is a cascade mixture of fixed-prior
spin/leaf averages. The common rotation is retained in the mixture. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma referenceReplicaMean_gibbsProbability {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean (gibbsProbability ν H) (fun _ => 0) D = referenceReplicaMean ν H D := by
  rw [referenceReplicaMean_zero, gibbsProbability_eq_tilted ν H he,
    referenceReplicaMean_eq_tilted ν H he]

lemma tensorCascadeDisorderShuffle_preserving {N n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (b : ℕ → ℝ) :
    MeasurePreserving
      (fun q : LabeledTree n × (SpecialOrthogonal N × (ℕ → ℝ)) => ((q.2.1,q.1),q.2.2))
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (μ.prod gaussianCoordinates))
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  have hp := ((Measure.measurePreserving_swap (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (ν := μ)).prod (MeasurePreserving.id gaussianCoordinates)).comp
      ((measurePreserving_prodAssoc (labeledCascadeLaw n b : Measure (LabeledTree n)) μ
        gaussianCoordinates).symm MeasurableEquiv.prodAssoc)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  rfl

lemma tensorRestrictionHamiltonian_id_eq {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (T : LabeledTree n)
    (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    tensorRestrictionHamiltonian eig c I degree amp
      (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2 =
      tensorNamespacedHamiltonian eig c I degree amp n treeDegree h ((z.1,T),z.2) := rfl

 theorem tensorNamespacedReplicaAverage_cascade_mixture {N m k r : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0)
    (D : SpecialOrthogonal N → (Fin r → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : 0 ≤ B)
    (hDB : ∀ U σ, |D U σ| ≤ B) :
    tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h D =
      ∫ T, ∫ z : SpecialOrthogonal N × (ℕ → ℝ),
        referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
          (tensorRestrictionHamiltonian eig c I degree amp
            (fun a => tensorPathProfile I degree n treeDegree h a) id z.1 z.2) (D z.1)
          ∂μ.prod gaussianCoordinates ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  let F := fun p : TensorFlatDisorder N n =>
    referenceReplicaMean (tensorNamespacedReference eig c I degree amp n treeDegree h p)
      (fun _ => 0) (D p.1.1)
  let S := fun q : LabeledTree n × (SpecialOrthogonal N × (ℕ → ℝ)) => ((q.2.1,q.1),q.2.2)
  have hS := tensorCascadeDisorderShuffle_preserving μ (n := n) b
  have hmF : Measurable F := measurable_tensorNamespacedReplicaMean eig c I degree amp n treeDegree h D hD
  have hiF : Integrable (F ∘ S)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (μ.prod gaussianCoordinates)) := by
    apply integrable_of_measurable_abs_le (hmF.comp hS.measurable)
    intro q
    change |referenceReplicaMean (tensorNamespacedReference eig c I degree amp n treeDegree h (S q))
      (fun _ => 0) (D q.2.1)| ≤ B
    exact referenceReplicaMean_abs_le _ _ _ (measurable_of_countable (D q.2.1)) hB (hDB q.2.1)
  unfold tensorNamespacedReplicaAverage
  change (∫ p, F p ∂_) = _
  calc
    _ = ∫ q, F (S q) ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (μ.prod gaussianCoordinates) := (hS.hasLaw.integral_comp hmF.aestronglyMeasurable).symm
    _ = ∫ T, ∫ z, F (S (T,z)) ∂μ.prod gaussianCoordinates
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := integral_prod _ hiF
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun T => ?_
      have he := tensorCountableHamiltonian_exp_integrable_ae μ
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
        eig c I degree amp treeDegree h hh h0 (id : Spin N × LabeledLeaf n → _)
      apply integral_congr_ae
      filter_upwards [he] with z hz
      dsimp only [F, S]
      unfold tensorNamespacedReference
      rw [← tensorRestrictionHamiltonian_id_eq eig c I degree amp treeDegree h T z]
      exact referenceReplicaMean_gibbsProbability _ _ hz _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorWardReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Ward terms expressed as ordinary reference-replica observables.
These identities prepare countable leaf exhaustion without differentiating
an infinite Gibbs integral. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma referenceReplicaMean_finiteGibbs (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) {r : ℕ} (D : (Fin r → S) → ℝ) :
    referenceReplicaMean ν H D =
      ∑ σ, (∏ i, finiteGibbs (fun s => ν.real {s}) H (σ i)) * D σ := by
  rw [referenceReplicaMean_finite]
  simp only [finiteGibbs, finitePartition, referencePartition_finite]

lemma referenceReplicaMean_one (ν : Measure S) [IsProbabilityMeasure ν]
    (H O : S → ℝ) :
    referenceReplicaMean ν H (fun σ : Fin 1 → S => O (σ 0)) =
      gibbsAverage (fun s => ν.real {s}) H O := by
  rw [referenceReplicaMean_finiteGibbs,
    ← Equiv.sum_comp (Equiv.funUnique (Fin 1) S).symm]
  simp only [Fin.prod_univ_one, Equiv.funUnique_symm_apply, gibbsAverage]
  rfl

lemma referenceReplicaMean_two (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) (O : S → S → ℝ) :
    referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) (σ 1)) =
      gibbsPairAverage (fun s => ν.real {s}) H O := by
  rw [referenceReplicaMean_finiteGibbs,
    ← Equiv.sum_comp (finTwoArrowEquiv S).symm, Fintype.sum_prod_type]
  simp only [Fin.prod_univ_two, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, gibbsPairAverage]

lemma finiteGibbsVariation_reference (ν : Measure S) [IsProbabilityMeasure ν]
    (H O A dO : S → ℝ) :
    finiteGibbsVariation (fun s => ν.real {s}) H O A dO =
      referenceReplicaMean ν H (fun σ : Fin 1 → S => dO (σ 0) + O (σ 0) * A (σ 0)) -
      referenceReplicaMean ν H (fun σ : Fin 2 → S => O (σ 0) * A (σ 1)) := by
  rw [referenceReplicaMean_one ν H (fun s => dO s + O s * A s),
    referenceReplicaMean_two ν H (fun s t => O s * A t)]
  simp only [finiteGibbsVariation, gibbsAverage, gibbsPairAverage,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPrincipalBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite principal Ward observables contract exactly to projected
overlap products when the two row groups have constant eigenvalues. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma off_coordinate_difference_sum {N : ℕ} (J K : Finset (Fin N)) (a b : Fin N → ℝ) (F : ℝ) :
    (∑ i ∈ J, ∑ j ∈ K, (a j * b j - a i * b i) * F) =
      ((J.card : ℝ) * (∑ j ∈ K, a j * b j) - (K.card : ℝ) * (∑ i ∈ J, a i * b i)) * F := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma off_coordinate_fresh_sum {N : ℕ} (J K : Finset (Fin N)) (a b c : Fin N → ℝ) (F : ℝ) :
    (∑ i ∈ J, ∑ j ∈ K, a i * b j * F * (c i * c j)) =
      (∑ i ∈ J, a i * c i) * (∑ j ∈ K, b j * c j) * F := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalPrincipalObservables
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one- and two-replica principal observables for the diagonal Ward
identity, with a generic spin projection for countable leaf passage. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*}

lemma tensorDiagonalDirectCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) :
    0 ≤ tensorDiagonalDirectCap eig J K := by
  unfold tensorDiagonalDirectCap
  positivity

lemma tensorDiagonalFreshCap_nonneg {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) :
    0 ≤ tensorDiagonalFreshCap eig J K := by
  unfold tensorDiagonalFreshCap
  positivity

lemma tensorDiagonalDirect_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) :
    |tensorDiagonalDirect eig J K sp U σ| ≤ tensorDiagonalDirectCap eig J K := by
  unfold tensorDiagonalDirect tensorDiagonalDirectCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (abs_add_le _ _).trans
  apply add_le_add (abs_coordinateSquareDifference_le i j _ _)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (abs_coordinateProduct_le i j _ _)
    (mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _))
    (by positivity) (Nat.cast_nonneg _)

lemma tensorDiagonalFresh_abs_le {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    |tensorDiagonalFresh eig J K sp U σ| ≤ tensorDiagonalFreshCap eig J K := by
  unfold tensorDiagonalFresh tensorDiagonalFreshCap
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_mul]
  exact mul_le_mul (abs_coordinateProduct_le i j _ _)
    (mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _))
    (by positivity) (Nat.cast_nonneg _)

lemma measurable_tensorDiagonalDirect_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (σ : Fin 1 → X) :
    Measurable (fun U => tensorDiagonalDirect eig J K sp U σ) := by
  unfold tensorDiagonalDirect coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((hc (σ 0) j).pow_const 2).sub ((hc (σ 0) i).pow_const 2)).add
      (((hc (σ 0) i).mul (hc (σ 0) j)).mul
        (((hc (σ 0) i).mul (hc (σ 0) j)).const_mul _))).const_mul _

lemma measurable_tensorDiagonalFresh_at {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N))
    (sp : X → Spin N) (σ : Fin 2 → X) :
    Measurable (fun U => tensorDiagonalFresh eig J K sp U σ) := by
  unfold tensorDiagonalFresh coordinateProduct
  have hc (s : X) (a : Fin N) :=
    (measurable_spinCoordinate (sp s) a).comp measurable_specialToOrthogonal
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (((hc (σ 0) i).mul (hc (σ 0) j)).mul
      (((hc (σ 1) i).mul (hc (σ 1) j)).const_mul _))).const_mul _

lemma measurable_tensorDiagonalDirect [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N) :
    Measurable (Function.uncurry (tensorDiagonalDirect eig J K sp)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorDiagonalDirect_at eig J K sp σ)

lemma measurable_tensorDiagonalFresh [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (sp : X → Spin N) :
    Measurable (Function.uncurry (tensorDiagonalFresh eig J K sp)) :=
  measurable_from_prod_countable_left (fun σ => measurable_tensorDiagonalFresh_at eig J K sp σ)

lemma tensorDiagonalDirect_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 1 → X) :
    tensorDiagonalDirect eig J K sp U σ = tensorDiagonalBlockDirect J K (a-b) sp U σ := by
  unfold tensorDiagonalDirect
  have he : (∑ i ∈ J, ∑ j ∈ K,
      (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
        spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
        coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
          ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 0))))) =
      ∑ i ∈ J, ∑ j ∈ K,
        (spinCoordinate (specialToOrthogonal U) (sp (σ 0)) j ^ 2 -
          spinCoordinate (specialToOrthogonal U) (sp (σ 0)) i ^ 2 +
          (a-b) * (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
            coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, coordinateProduct, pow_two]
  have hd := off_coordinate_difference_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0))) 1
  simp only [mul_one] at hd
  have hp := off_coordinate_fresh_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0))) 1
  simp only [mul_one] at hp
  rw [hd, hp]
  simp only [tensorDiagonalBlockDirect, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate, div_eq_mul_inv]
  ring

lemma tensorDiagonalFresh_eq_block {N : ℕ} (eig : Fin N → ℝ) (J K : Finset (Fin N)) (a b : ℝ)
    (hJ : ∀ i ∈ J, eig i = a) (hK : ∀ j ∈ K, eig j = b)
    (sp : X → Spin N) (U : SpecialOrthogonal N) (σ : Fin 2 → X) :
    tensorDiagonalFresh eig J K sp U σ = tensorDiagonalBlockFresh J K (a-b) sp U σ := by
  unfold tensorDiagonalFresh
  have he : (∑ i ∈ J, ∑ j ∈ K,
      coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
        ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal U) (sp (σ 1)))) =
      ∑ i ∈ J, ∑ j ∈ K, (a-b) *
        (coordinateProduct i j (specialToOrthogonal U) (sp (σ 0)) *
          coordinateProduct i j (specialToOrthogonal U) (sp (σ 1))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ i hi, hK j hj]
    ring
  rw [he]
  simp only [← Finset.mul_sum, coordinateProduct]
  have hp := off_coordinate_fresh_sum J K
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 0)))
    (spinCoordinate (specialToOrthogonal U) (sp (σ 1))) 1
  simp only [mul_one] at hp
  rw [hp]
  simp only [tensorDiagonalBlockFresh, ← matrixRotation_specialToOrthogonal, projectedOverlap,
    spinCoordinate]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalWardMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint integrability for the actual finite diagonal Ward identity. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*} [Fintype S]

lemma measurable_tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ} (w : S → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (x : S → Spin N × LabeledLeaf n) (i j : Fin N) :
    Measurable (tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j) := by
  have hc (s : S) (a : Fin N) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      spinCoordinate (specialToOrthogonal z.1) (x s).1 a) :=
    ((measurable_spinCoordinate (x s).1 a).comp measurable_specialToOrthogonal).comp measurable_fst
  apply measurable_finiteGibbsVariation
  · exact measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x
  · intro s
    exact (hc s i).mul (hc s j)
  · intro s
    exact ((hc s i).mul (hc s j)).const_mul _
  · intro s
    exact ((hc s j).pow_const 2).sub ((hc s i).pow_const 2)

lemma integrable_tensorRestrictionDiagonalPrincipalVariation {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Integrable (tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j)
      (μ.prod gaussianCoordinates) := by
  apply integrable_of_measurable_abs_le
    (measurable_tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j)
    (c := N + 2 * (N : ℝ) * (|eig i - eig j| * N))
  intro z
  apply abs_gibbsVariation_le hw _ _ _ _ (Nat.cast_nonneg _)
  · intro s
    exact abs_coordinateProduct_le i j _ _
  · intro s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_coordinateProduct_le i j _ _) (abs_nonneg _)
  · intro s
    exact abs_coordinateSquareDifference_le i j _ _

lemma measurable_tensorRestrictionDiagonalCorrection {N m k n : ℕ} (w : S → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Measurable (tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j) := by
  have hO (s : S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionDiagonalObservable i j x z.1 s) :=
    ((measurable_spinCoordinate (x s).1 i).mul (measurable_spinCoordinate (x s).1 j)).comp
      (measurable_specialToOrthogonal.comp measurable_fst)
  have hK (s t : S) : Measurable (fun z : SpecialOrthogonal N × (ℕ → ℝ) =>
      tensorRestrictionCovarianceDerivative I degree amplitude v x i j z.1 s t) :=
    (measurable_tensorNamespacedPlaneCross I degree amplitude v i j (x s) (x t)).comp measurable_fst
  exact measurable_gaussianWardCorrection_joint _ _ _ _
    (measurable_tensorRestrictionHamiltonian eig c I degree amplitude v x) hO hK

lemma tensorRestrictionDiagonalCorrection_abs_le {N m n : ℕ} (hN : 0 < N)
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    |tensorRestrictionDiagonalCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j z| ≤
      (N : ℝ) ^ 2 * (48 * D * perturbationScale N ^ 2) := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
  have he := tensorRestriction_actualDiagonalWardCorrection_abs_le hN z.1 hw
    (tensorRestrictionHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu D hD hdegree
    h hh h0 {i} {j} x
  simp only [Finset.sum_singleton] at he
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  calc
    _ = (N : ℝ) ^ 2 * |(N : ℝ)⁻¹ ^ 2 * tensorRestrictionDiagonalCorrection w eig c I degree amp v x i j z| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ((N : ℝ)⁻¹))]
      field_simp
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)

lemma integrable_tensorRestrictionDiagonalCorrection {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) :
    Integrable (tensorRestrictionDiagonalCorrection w eig c I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j) (μ.prod gaussianCoordinates) :=
  integrable_of_measurable_abs_le (measurable_tensorRestrictionDiagonalCorrection w eig c I degree
    (tensorPerturbationAmplitude N u) (fun a => tensorPathProfile I degree n treeDegree h a) x i j)
      (tensorRestrictionDiagonalCorrection_abs_le hN hw eig c I degree treeDegree u hu D hD hdegree h hh h0 x i j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorPrincipalWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite normalized principal Ward residual bound. The exact Gaussian
correction is eliminated before countable leaf exhaustion. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S ι : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma referenceReplicaMean_finite_finset_sum (ν : Measure S) [IsProbabilityMeasure ν]
    (H : S → ℝ) {r : ℕ} (t : Finset ι) (D : ι → (Fin r → S) → ℝ) :
    referenceReplicaMean ν H (fun σ => ∑ i ∈ t, D i σ) =
      ∑ i ∈ t, referenceReplicaMean ν H (D i) := by
  simp only [referenceReplicaMean_finiteGibbs, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma integral_normalized_double_sum {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (J K : Finset (Fin N)) (f : Fin N → Fin N → Ω → ℝ)
    (hf : ∀ i j, Integrable (f i j) P) :
    (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, f i j z ∂P) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, ∫ z, f i j z ∂P := by
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum _ (fun j _ => hf i j)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma normalized_integral_sum_eq_neg {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (J K : Finset (Fin N)) (V W : Fin N → Fin N → Ω → ℝ)
    (hiV : ∀ i j, Integrable (V i j) P) (hiW : ∀ i j, Integrable (W i j) P)
    (hz : ∀ i ∈ J, ∀ j ∈ K, (∫ z, V i j z ∂P) = -(∫ z, W i j z ∂P)) :
    (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P) =
      -(∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z ∂P) := by
  rw [integral_normalized_double_sum P J K V hiV, integral_normalized_double_sum P J K W hiW]
  calc
    _ = (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, -(∫ z, W i j z ∂P) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hz i hi j hj
    _ = _ := by simp only [Finset.sum_neg_distrib, mul_neg]

lemma integrable_finite_referenceReplicaMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [IsProbabilityMeasure ν]
    (H : Ω × S → ℝ) (hH : Measurable H) {r : ℕ}
    (D : Ω × (Fin r → S) → ℝ) (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, |D z| ≤ C) :
    Integrable (fun ω => referenceReplicaMean ν (fun s => H (ω,s)) (fun σ => D (ω,σ))) P :=
  integrable_of_measurable_abs_le (measurable_random_referenceReplicaMean measurable_const hH hD)
    (fun ω => referenceReplicaMean_abs_le ν _ _ (measurable_of_countable _) hC (fun σ => hb (ω,σ)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorDiagonalPrincipalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite diagonal principal Ward bound in original-state
one- and two-replica form, uniform in the leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

theorem expectedDiagonalWard_restriction_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => expectedDiagonalWard P (normalizedRestriction ν (S n)) H D₁ D₂) atTop
      (𝓝 (expectedDiagonalWard P ν H D₁ D₂)) :=
  (expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₁ hD₁ hB₁ hb₁ hS hexh hpos).sub
    (expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₂ hD₂ hB₂ hb₂ hS hexh hpos)

theorem expectedDiagonalWard_abs_le_of_restriction {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0)
    {ε : ℝ} (hfinite : ∀ n,
      |expectedDiagonalWard P (normalizedRestriction ν (S n)) H D₁ D₂| ≤ ε) :
    |expectedDiagonalWard P ν H D₁ D₂| ≤ ε :=
  le_of_tendsto (expectedDiagonalWard_restriction_tendsto P ν H hH he D₁ hD₁ D₂ hD₂
    hB₁ hB₂ hb₁ hb₂ hS hexh hpos).abs (Eventually.of_forall hfinite)

lemma expectedDiagonalWard_subtype {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (hpos : ν S ≠ 0)
    (H : Ω × X → ℝ) (D₁ : Ω × (Fin 1 → X) → ℝ) (D₂ : Ω × (Fin 2 → X) → ℝ) :
    expectedDiagonalWard P (subtypeReference ν S)
      (fun z : Ω × S => H (z.1,z.2))
      (fun z => D₁ (z.1, fun i => (z.2 i : X)))
      (fun z => D₂ (z.1, fun i => (z.2 i : X))) =
      expectedDiagonalWard P (normalizedRestriction ν S) H D₁ D₂ := by
  have he {r : ℕ} (z : Ω) (O : (Fin r → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν S) (fun s => H (z,s))
        (fun σ => O (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν S) (fun s => H (z,s)) O :=
    referenceReplicaMean_subtype hS hpos
      (measurable_of_countable (fun s => H (z,s))) (measurable_of_countable O)
  unfold expectedDiagonalWard
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₁ (z,σ))
  · apply integral_congr_ae
    exact ae_of_all _ fun z => he z (fun σ => D₂ (z,σ))

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma tensorRestrictionDiagonalVariation_principal_eq {N m k n : ℕ}
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (z : SpecialOrthogonal N × (ℕ → ℝ)) :
    (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
      tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s}) eig c I degree amplitude v x i j z =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorDiagonalDirect eig J K (fun s => (x s).1) z.1) -
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (tensorDiagonalFresh eig J K (fun s => (x s).1) z.1) := by
  have hcoord (i j : Fin N) : tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s})
      eig c I degree amplitude v x i j z =
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 1 → S =>
          spinCoordinate (specialToOrthogonal z.1) (x (σ 0)).1 j ^ 2 -
            spinCoordinate (specialToOrthogonal z.1) (x (σ 0)).1 i ^ 2 +
            coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1 *
              ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1)) -
      referenceReplicaMean ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
        (fun σ : Fin 2 → S => coordinateProduct i j (specialToOrthogonal z.1) (x (σ 0)).1 *
          ((eig i - eig j) * coordinateProduct i j (specialToOrthogonal z.1) (x (σ 1)).1)) :=
    finiteGibbsVariation_reference ν (tensorRestrictionHamiltonian eig c I degree amplitude v x z.1 z.2)
      (tensorRestrictionDiagonalObservable i j x z.1)
      (fun s => (eig i - eig j) * tensorRestrictionDiagonalObservable i j x z.1 s)
      (tensorRestrictionDiagonalVariation i j x z.1)
  simp_rw [hcoord]
  unfold tensorDiagonalDirect tensorDiagonalFresh
  rw [referenceReplicaMean_const_mul, referenceReplicaMean_const_mul]
  simp_rw [referenceReplicaMean_finite_finset_sum]
  simp only [Finset.sum_sub_distrib]
  ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma tensorRestriction_diagonal_integral_pair {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j)
    (hiW : Integrable (tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j)
      (μ.prod gaussianCoordinates)) :
    (∫ z, tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j z
      ∂μ.prod gaussianCoordinates) =
      -(∫ z, tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j z
        ∂μ.prod gaussianCoordinates) := by
  have hiV := integrable_tensorRestrictionDiagonalPrincipalVariation μ hw eig c I degree amplitude v x i j
  have he := tensorRestriction_diagonal_ward hN μ hw eig c I degree amplitude v x i j hij
  change (∫ U, (∫ g, tensorRestrictionDiagonalPrincipalVariation w eig c I degree amplitude v x i j (U,g)
      ∂gaussianCoordinates) + ∫ g, tensorRestrictionDiagonalCorrection w eig c I degree amplitude v x i j (U,g)
      ∂gaussianCoordinates ∂μ) = 0 at he
  rw [integral_add hiV.integral_prod_left hiW.integral_prod_left,
    ← integral_prod _ hiV, ← integral_prod _ hiW] at he
  linarith

lemma tensorRestrictionDiagonalVariation_principal_integral {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) :
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2) =
      ∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s}) eig c I degree amp v x i j z
        ∂μ.prod gaussianCoordinates := by
  intro H
  let P := μ.prod gaussianCoordinates
  let V := fun i j : Fin N => tensorRestrictionDiagonalPrincipalVariation (fun s => ν.real {s})
    eig c I degree amp v x i j
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → S) =>
    tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → S) =>
    tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hi₁ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₁ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₁ hm₁ (tensorDiagonalDirectCap_nonneg eig J K)
      (fun z => tensorDiagonalDirect_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
  have hi₂ : Integrable (fun z => referenceReplicaMean ν (fun s => H (z,s)) (fun σ => D₂ (z,σ))) P :=
    integrable_finite_referenceReplicaMean P ν H hH D₂ hm₂ (tensorDiagonalFreshCap_nonneg eig J K)
      (fun z => tensorDiagonalFresh_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
  change expectedDiagonalWard P ν H D₁ D₂ = _
  unfold expectedDiagonalWard
  rw [← integral_sub hi₁ hi₂]
  apply integral_congr_ae
  exact ae_of_all _ fun z => (tensorRestrictionDiagonalVariation_principal_eq ν eig c I degree amp v x J K z).symm

/-- The actual finite diagonal Ward residual has a uniform quadratic
perturbation bound, with no limiting Ward assumption. -/
theorem tensorRestriction_diagonal_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure S) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : S → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 := fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × S =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let w := fun s : S => ν.real {s}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  let V := fun i j : Fin N => tensorRestrictionDiagonalPrincipalVariation w eig c I degree amp v x i j
  let W := fun i j : Fin N => tensorRestrictionDiagonalCorrection w eig c I degree amp v x i j
  have hiV (i j : Fin N) : Integrable (V i j) P :=
    integrable_tensorRestrictionDiagonalPrincipalVariation μ hw eig c I degree amp v x i j
  have hiW (i j : Fin N) : Integrable (W i j) P :=
    integrable_tensorRestrictionDiagonalCorrection hN μ hw eig c I degree treeDegree u hu D hD hdegree
      h hh h0 x i j
  have hz (i : Fin N) (hi : i ∈ J) (j : Fin N) (hj : j ∈ K) :
      (∫ z, V i j z ∂P) = -(∫ z, W i j z ∂P) := by
    have hij : i ≠ j := fun he => (Finset.disjoint_left.mp hJK hi) (he.symm ▸ hj)
    exact tensorRestriction_diagonal_integral_pair hN μ hw eig c I degree amp v x i j hij (hiW i j)
  have hzero : (∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, V i j z ∂P) =
      -(∫ z, (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z ∂P) :=
    normalized_integral_sum_eq_neg P J K V W hiV hiW hz
  have hprincipal := tensorRestrictionDiagonalVariation_principal_integral μ ν eig c I degree amp v x J K
  rw [hprincipal, hzero, abs_neg]
  have hb := norm_integral_le_of_norm_le_const (μ := P)
    (ae_of_all P fun z => show ‖(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K, W i j z‖ ≤
      48 * D * perturbationScale N ^ 2 from by
        rw [Real.norm_eq_abs]
        exact tensorRestriction_actualDiagonalWardCorrection_abs_le hN z.1 hw
          (tensorRestrictionHamiltonian eig c I degree amp v x z.1 z.2) I degree treeDegree u hu
          D hD hdegree h hh h0 J K x)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCountableDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual countable spin/leaf diagonal principal Ward bound. The finite
correction is removed before taking the leaf-exhaustion limit. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorFiniteRestriction_diagonal_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K)
    (S : Set X) (hSfin : S.Finite) (hSm : MeasurableSet S) (hpos : ν S ≠ 0) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) (normalizedRestriction ν S) H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let := hSfin.fintype
  let νa := subtypeReference ν S
  have : IsProbabilityMeasure νa := subtypeReference_probability ν hSm hpos
  have hf := tensorRestriction_diagonal_principal_bound hN μ νa eig c I degree treeDegree u hu D hD
    hdegree h hh h0 (fun s : S => x s) J K hJK
  rw [← expectedDiagonalWard_subtype (μ.prod gaussianCoordinates) ν hSm hpos H]
  exact hf

theorem tensorCountable_diagonal_principal_bound {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) (x : X → Spin N × LabeledLeaf n)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    let amp := tensorPerturbationAmplitude N u
    let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
      fun a => tensorPathProfile I degree n treeDegree h a
    let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × X =>
      tensorRestrictionHamiltonian eig c I degree amp v x z.1.1 z.1.2 z.2
    |expectedDiagonalWard (μ.prod gaussianCoordinates) ν H
      (fun z => tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2)
      (fun z => tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2)| ≤
      48 * D * perturbationScale N ^ 2 := by
  classical
  intro amp v H
  let P := μ.prod gaussianCoordinates
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → X) =>
    tensorDiagonalDirect eig J K (fun s => (x s).1) z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → X) =>
    tensorDiagonalFresh eig J K (fun s => (x s).1) z.1.1 z.2
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v x s)
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K (fun s => (x s).1) σ).comp measurable_fst)
  obtain ⟨S, hSfin, hSpos, hSexh⟩ := countable_reference_exhaustion ν
  have hSm (a : ℕ) : MeasurableSet (S a) := (hSfin a).measurableSet
  apply expectedDiagonalWard_abs_le_of_restriction P ν H hH
    (tensorCountableHamiltonian_exp_integrable_ae μ ν eig c I degree amp treeDegree h hh h0 x)
    D₁ hm₁ D₂ hm₂ (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalFreshCap_nonneg eig J K)
    (fun z => tensorDiagonalDirect_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
    (fun z => tensorDiagonalFresh_abs_le eig J K (fun s => (x s).1) z.1.1 z.2)
    hSm hSexh hSpos
  intro a
  exact tensorFiniteRestriction_diagonal_principal_bound hN μ ν eig c I degree treeDegree u hu D hD
    hdegree h hh h0 x J K hJK (S a) (hSfin a) (hSm a) (hSpos a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCascadeDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual enriched diagonal Ward residual, averaged over the cascade,
retains the uniform bound proved for every fixed countable reference. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem expectedDiagonalWard_mixture_abs_le {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ξ : Measure T) [IsProbabilityMeasure ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → Measure X) [∀ t, IsProbabilityMeasure (ν t)] (hν : Measurable ν)
    (H : Ω × X → ℝ) (hH : Measurable H)
    (D₁ : Ω × (Fin 1 → X) → ℝ) (hD₁ : Measurable D₁)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ z, |D₁ z| ≤ B₁) (hb₂ : ∀ z, |D₂ z| ≤ B₂)
    {ε : ℝ} (hward : ∀ t, |expectedDiagonalWard P (ν t) H D₁ D₂| ≤ ε) :
    |(∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₁ (ω,σ)) ∂P) ∂ ξ) -
      (∫ t, (∫ ω, referenceReplicaMean (ν t) (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P) ∂ ξ)| ≤ ε := by
  have hi₁ := integrable_mixtureReplicaMean ξ P ν hν H hH D₁ hD₁ hB₁ hb₁
  have hi₂ := integrable_mixtureReplicaMean ξ P ν hν H hH D₂ hD₂ hB₂ hb₂
  rw [← integral_sub hi₁ hi₂]
  apply abs_integral_le_const_of_bound
    ((measurable_integral_mixtureReplicaMean P ν hν H hH D₁ hD₁).sub
      (measurable_integral_mixtureReplicaMean P ν hν H hH D₂ hD₂))
  exact hward

/-- The diagonal spectral Ward bound for the actual finite tensor-enriched
model, including all cascade, Haar and Gaussian averages. -/
theorem tensorNamespaced_diagonal_principal_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (hJK : Disjoint J K) :
    |tensorNamespacedReplicaAverage μ eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalDirect eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      tensorNamespacedReplicaAverage μ eig c I degree (tensorPerturbationAmplitude N u)
        n b treeDegree h (tensorDiagonalFresh eig J K (Prod.fst : Spin N × LabeledLeaf n → Spin N))| ≤
      48 * D * perturbationScale N ^ 2 := by
  let amp := tensorPerturbationAmplitude N u
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun a => tensorPathProfile I degree n treeDegree h a
  let P := μ.prod gaussianCoordinates
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N))
  let H := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
    tensorRestrictionHamiltonian eig c I degree amp v id z.1.1 z.1.2 z.2
  let D₁ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 1 → Spin N × LabeledLeaf n) =>
    tensorDiagonalDirect eig J K Prod.fst z.1.1 z.2
  let D₂ := fun z : (SpecialOrthogonal N × (ℕ → ℝ)) × (Fin 2 → Spin N × LabeledLeaf n) =>
    tensorDiagonalFresh eig J K Prod.fst z.1.1 z.2
  have hH : Measurable H := measurable_from_prod_countable_left
    (fun s => measurable_tensorRestrictionHamiltonian eig c I degree amp v id s)
  have hm₁ : Measurable D₁ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalDirect_at eig J K Prod.fst σ).comp measurable_fst)
  have hm₂ : Measurable D₂ := measurable_from_prod_countable_left
    (fun σ => (measurable_tensorDiagonalFresh_at eig J K Prod.fst σ).comp measurable_fst)
  have hward (T : LabeledTree n) : |expectedDiagonalWard P (ν T) H D₁ D₂| ≤
      48 * D * perturbationScale N ^ 2 :=
    tensorCountable_diagonal_principal_bound hN μ (ν T) eig c I degree treeDegree u hu D hD
      hdegree h hh h0 id J K hJK
  have hmix := expectedDiagonalWard_mixture_abs_le (labeledCascadeLaw n b : Measure (LabeledTree n)) P
    ν (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))) H hH D₁ hm₁ D₂ hm₂
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalFreshCap_nonneg eig J K)
    (fun z => tensorDiagonalDirect_abs_le eig J K Prod.fst z.1.1 z.2)
    (fun z => tensorDiagonalFresh_abs_le eig J K Prod.fst z.1.1 z.2) hward
  rw [tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalDirect eig J K Prod.fst) (measurable_tensorDiagonalDirect eig J K Prod.fst)
    (tensorDiagonalDirectCap_nonneg eig J K) (tensorDiagonalDirect_abs_le eig J K Prod.fst),
    tensorNamespacedReplicaAverage_cascade_mixture μ eig c I degree amp n b treeDegree h hh h0
    (tensorDiagonalFresh eig J K Prod.fst) (measurable_tensorDiagonalFresh eig J K Prod.fst)
    (tensorDiagonalFreshCap_nonneg eig J K) (tensorDiagonalFresh_abs_le eig J K Prod.fst)]
  exact hmix

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalWardLimits
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak closure of the one-replica diagonal Ward residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma spectralDiagonalWardResidual_weak_limit {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀)) (a b : Fin m) :
    Tendsto (fun n => spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b) atTop
      (𝓝 (spectralDiagonalWardResidual Q ρ₀ eig₀ a b)) := by
  have hI (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
      Tendsto (fun n => ∫ x, F x ∂(L n : Measure (SpectralArray (m + 1)))) atTop
        (𝓝 (∫ x, F x ∂(Q : Measure (SpectralArray (m + 1))))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hIa := hI (fun x => (x (0,0) a.castSucc : ℝ)) (by fun_prop)
  have hIb := hI (fun x => (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hIp := hI (fun x => (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ) -
    (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)) (by fun_prop)
  exact (((tendsto_pi_nhds.mp hρ a).mul hIb).sub
    ((tendsto_pi_nhds.mp hρ b).mul hIa)).add
      (((tendsto_pi_nhds.mp heig a).sub (tendsto_pi_nhds.mp heig b)).mul hIp)

theorem spectralDiagonalWardResidual_zero_of_vanishing_bound {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀)) (a b : Fin m)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n, |spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b| ≤ ε n) :
    spectralDiagonalWardResidual Q ρ₀ eig₀ a b = 0 := by
  have ht := spectralDiagonalWardResidual_weak_limit hL hρ heig a b
  have hz := squeeze_zero (fun n => abs_nonneg (spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b)) hb hε
  exact abs_eq_zero.mp (tendsto_nhds_unique ht.abs hz)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual enriched diagonal Ward bound is exactly the corresponding
spectral-array residual, retaining the common rotation in both replicas. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma continuous_spectralDiagonalWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m) :
    Continuous (spectralDiagonalWardDirect ρ eig a b) := by
  unfold spectralDiagonalWardDirect
  fun_prop

lemma continuous_spectralDiagonalWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m) :
    Continuous (spectralDiagonalWardFresh eig a b) := by
  unfold spectralDiagonalWardFresh
  fun_prop

lemma spectralDiagonalWardResidual_integral {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1))) (ρ eig : Fin m → ℝ) (a b : Fin m) :
    spectralDiagonalWardResidual Q ρ eig a b =
      (∫ x, spectralDiagonalWardDirect ρ eig a b x ∂(Q : Measure (SpectralArray (m + 1)))) -
      ∫ x, spectralDiagonalWardFresh eig a b x ∂(Q : Measure (SpectralArray (m + 1))) := by
  have hI (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
      Integrable F (Q : Measure (SpectralArray (m + 1))) :=
    (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable _
  have ha := hI (fun x => (x (0,0) a.castSucc : ℝ)) (by fun_prop)
  have hb := hI (fun x => (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hself := hI (fun x => (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hoff := hI (fun x => (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)) (by fun_prop)
  unfold spectralDiagonalWardResidual spectralDiagonalWardDirect spectralDiagonalWardFresh
  have hadd := integral_add ((hb.const_mul (ρ a)).sub (ha.const_mul (ρ b)))
    (hself.const_mul (eig a-eig b))
  have hsub := integral_sub (hb.const_mul (ρ a)) (ha.const_mul (ρ b))
  have hprod := integral_sub hself hoff
  simp only [Pi.sub_apply] at hadd hsub hprod
  rw [hadd, hsub, hprod]
  simp only [integral_const_mul]
  ring

lemma tensorNamespacedArrayLaw_diagonalWard_residual {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (κ : Fin m → ℝ) (a d : Fin m)
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    spectralDiagonalWardResidual (tensorNamespacedArrayLaw μ eig c I degree amp n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) -
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
  let ρ := fun j => ((I j).card : ℝ) / N
  let Q := tensorNamespacedArrayLaw μ eig c I degree amp n b treeDegree h
  have hdir : (∫ x, spectralDiagonalWardDirect ρ κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalDirect eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardDirect ρ κ a d) _
      (fun i : Fin 1 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalDirect_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardDirect, tensorDiagonalBlockDirect, spectralJointEntry_spectral, ρ, Fin.val_zero]
    ring
  have hfresh : (∫ x, spectralDiagonalWardFresh κ a d x ∂(Q : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (tensorDiagonalFresh eig (I a) (I d) (Prod.fst : Spin N × LabeledLeaf n → Spin N)) := by
    apply tensorNamespacedArrayLaw_test μ eig c I degree amp n b treeDegree h
      _ (continuous_spectralDiagonalWardFresh κ a d) _
      (fun i : Fin 2 => i.val) Fin.val_injective
    intro U σ
    rw [tensorDiagonalFresh_eq_block eig (I a) (I d) (κ a) (κ d) ha hd]
    simp only [spectralDiagonalWardFresh, tensorDiagonalBlockFresh, spectralJointEntry_spectral, Fin.val_zero, Fin.val_one]
    ring
  rw [spectralDiagonalWardResidual_integral Q ρ κ a d, hdir, hfresh]

/-- Exact finite-volume spectral-array diagonal Ward bound for the actual
tensor-enriched law, before taking any overlap limit. -/
theorem tensorNamespacedArrayLaw_diagonalWard_bound {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ j, (degree r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (κ : Fin m → ℝ) (a d : Fin m) (had : Disjoint (I a) (I d))
    (ha : ∀ i ∈ I a, eig i = κ a) (hd : ∀ i ∈ I d, eig i = κ d) :
    |spectralDiagonalWardResidual
      (tensorNamespacedArrayLaw μ eig c I degree (tensorPerturbationAmplitude N u) n b treeDegree h)
      (fun j => ((I j).card : ℝ) / N) κ a d| ≤ 48 * D * perturbationScale N ^ 2 := by
  rw [tensorNamespacedArrayLaw_diagonalWard_residual μ eig c I degree (tensorPerturbationAmplitude N u)
    b treeDegree h κ a d ha hd]
  exact tensorNamespaced_diagonal_principal_bound hN μ eig c I degree treeDegree u hu D hD hdegree
    b h hh h0 (I a) (I d) had

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGrowingDiagonalWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal Ward equations for growing cascade depth, using the same
depth-independent finite Gaussian/Haar error bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingArrayLaw_diagonalWard_limit
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (m : ℕ) (depth : ℕ → ℕ) (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (degree : (k : ℕ) → Fin (N k) → Fin m → ℕ) (treeDegree : (k : ℕ) → Fin (N k) → ℕ)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ k r, (∑ j, (degree k r j : ℝ)) ≤ D * ((r : ℝ) + 1))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (κ : ℕ → Fin m → ℝ) (ρ₀ κ₀ : Fin m → ℝ)
    (hρ : Tendsto (fun k j => ((I k j).card : ℝ) / N k) atTop (𝓝 ρ₀))
    (hκ : Tendsto κ atTop (𝓝 κ₀)) (a d : Fin m)
    (had : ∀ k, Disjoint (I k a) (I k d))
    (ha : ∀ k i, i ∈ I k a → eig k i = κ k a)
    (hd : ∀ k i, i ∈ I k d → eig k i = κ k d)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorNamespacedArrayLaw (μ k) (eig k) (c k) (I k) (degree k)
      (tensorPerturbationAmplitude (N k) (u k)) (depth k) (b k) (treeDegree k) (h k)) atTop (𝓝 Q)) :
    spectralDiagonalWardResidual Q ρ₀ κ₀ a d = 0 := by
  have hε : Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((perturbationScale_tendsto.comp hNlim).pow 2) :
        Tendsto (fun k => 48 * D * perturbationScale (N k) ^ 2) atTop (𝓝 (48 * D * 0 ^ 2)))
  apply spectralDiagonalWardResidual_zero_of_vanishing_bound hL hρ hκ a d hε
  intro k
  have : (μ k).IsMulLeftInvariant := hμinv k
  exact tensorNamespacedArrayLaw_diagonalWard_bound (hN k) (μ k) (eig k) (c k) (I k) (degree k)
    (treeDegree k) (u k) (hu k) D hD (hdegree k) (b k) (h k) (hh k) (h0 k) (κ k) a d
    (had k) (ha k) (hd k)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPerturbedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual diagonal perturbation preserves spectral blocks and vanishes
in their limiting eigenvalues even when its minimizing coordinates vary. -/

noncomputable section
open MeasureTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma diagonalPerturbedEigenvalues_block {N m : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (v : Fin m → ℝ) (t : ℝ) (lam : Fin m → ℝ)
    (hlam : ∀ a i, i ∈ I a → eig i = lam a) (a : Fin m) (i : Fin N) (hi : i ∈ I a) :
    diagonalPerturbedEigenvalues eig I v t i = t * lam a + 2 * perturbationScale N * v a := by
  classical
  have hs : (∑ b, if i ∈ I b then v b else 0) = v a := by
    rw [Finset.sum_eq_single a]
    · simp only [ite_eq_left hi]
    · intro b _ hba
      have hn : i ∉ I b := fun hib =>
        Finset.disjoint_left.mp (hdis (Set.mem_univ b) (Set.mem_univ a) hba) hib hi
      simp only [ite_eq_right hn]
    · exact fun ha => False.elim (ha (Finset.mem_univ a))
  simp only [diagonalPerturbedEigenvalues, hs, hlam a i hi]

lemma perturbedBlockEigenvalues_tendsto {m : ℕ} (N : ℕ → ℕ)
    (hNlim : Tendsto N atTop atTop) (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) (lam : Fin m → ℝ) :
    Tendsto (fun k a => t k * lam a + 2 * perturbationScale (N k) * v k a) atTop
      (𝓝 (fun a => t₀ * lam a)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hz : Tendsto (fun k => 2 * perturbationScale (N k) * v k a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_)
      (show Tendsto (fun k => 4 * perturbationScale (N k)) atTop (𝓝 0) by
        simpa only [mul_zero, Function.comp_apply] using (perturbationScale_tendsto.comp hNlim).const_mul 4)
    have hp : 0 ≤ perturbationScale (N k) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
    exact (mul_le_mul_of_nonneg_left (hv k a) (by positivity)).trans_eq (by ring)
  simpa only [add_zero] using (ht.mul_const (lam a)).add hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGrowingPerturbedWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both Ward equations for the growing-depth enriched model, with its
actual diagonal perturbation and complete monomial enumeration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorGrowingPerturbedArrayLaw_ward_limits_oai
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop) (m : ℕ) (depth : ℕ → ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k r, |u k r| ≤ 2)
    (v : ℕ → Fin m → ℝ) (hv : ∀ k a, |v k a| ≤ 2)
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀))
    (b : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) (depth k) (b k) (h k)) atTop (𝓝 Q))
    (ρ : Fin m → ℝ)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ r, |Φ r| ≤ B) →
      spectralOffWardResidual Q ρ (fun a => t₀ * lam a) a b₀ Φ = 0) ∧
    (∀ a b₀, spectralDiagonalWardResidual Q ρ (fun a => t₀ * lam a) a b₀ = 0) := by
  let E := fun k => diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)
  let κ := fun k a => t k * lam a + 2 * perturbationScale (N k) * v k a
  have hκ : ∀ k a i, i ∈ I k a → E k i = κ k a := fun k =>
    diagonalPerturbedEigenvalues_block (eig k) (I k) (hdis k) (v k) (t k) lam (hlam k)
  have hκlim : Tendsto κ atTop (𝓝 (fun a => t₀ * lam a)) :=
    perturbedBlockEigenvalues_tendsto N hNlim v hv t ht lam
  have hdegree (k : ℕ) (r : Fin (N k)) :
      (∑ a, (enumeratedSpectralDegree m r a : ℝ)) ≤ 1 * ((r : ℝ) + 1) := by
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m r
  refine ⟨?_, ?_⟩
  · intro a b₀ Φ hΦ B hB hΦB
    exact tensorGrowingArrayLaw_off_ward_limit N hN hNlim m depth μ hμinv E c I hdis hcover
      (fun k r => enumeratedSpectralDegree m r) (fun k r => enumeratedTreeDegree m r)
      u hu 1 zero_le_one hdegree b h hh h0 κ hκ Q hL ρ (fun a => t₀ * lam a)
      hρ hκlim a b₀ Φ hΦ B hB hΦB
  · intro a b₀
    by_cases hab : a = b₀
    · subst b₀
      simp [spectralDiagonalWardResidual]
    exact tensorGrowingArrayLaw_diagonalWard_limit N hN hNlim m depth μ hμinv E c I
      (fun k r => enumeratedSpectralDegree m r) (fun k r => enumeratedTreeDegree m r)
      u hu 1 zero_le_one hdegree b h hh h0 κ ρ (fun a => t₀ * lam a) hρ hκlim a b₀
      (fun k => hdis k (Set.mem_univ a) (Set.mem_univ b₀) hab)
      (fun k => hκ k a) (fun k => hκ k b₀) Q hL

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits_oai := @OAI.InvariantIsing.tensorGrowingPerturbedArrayLaw_ward_limits_oai
