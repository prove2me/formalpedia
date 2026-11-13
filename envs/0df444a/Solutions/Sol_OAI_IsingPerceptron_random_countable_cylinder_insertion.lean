-- Prove2me | solution 1 for OAI.IsingPerceptron.random_countable_cylinder_insertion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:04.26081+00:00
-- url     : https://prove2.me/submissions/dcc57f00-4cc3-4f64-be33-dd415d55c46b

import Mathlib
import Definitions.Def_OAIQ258000
import Definitions.Def_OAIQ258001

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

lemma replicaGibbs_sum {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) :
    ∑ σ : Fin r → S, replicaGibbs w B C g σ = 1 := by
  classical
  unfold replicaGibbs
  rw [← Fintype.prod_sum]
  simp only [gaussianGibbs, finiteGibbs_sum hw, Finset.prod_const_one]

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

end Perturbation

variable {S : Type*} [Fintype S]

lemma replicaMean_abs_le {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) {D : (Fin r → S) → ℝ}
    {K : ℝ} (hD : ∀ σ, |D σ| ≤ K) (g : Fin n → ℝ) :
    |replicaMean w B C D g| ≤ K := by
  calc
    _ ≤ ∑ σ, replicaGibbs w B C g σ*|D σ| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    _ ≤ ∑ σ : Fin r → S, replicaGibbs w B C g σ*K := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hD σ) (replicaGibbs_nonneg hw B C g σ)
    _ = K := by rw [← Finset.sum_mul, replicaGibbs_sum hw, one_mul]

lemma integrable_replicaMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) :
    Integrable (replicaMean w B C D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply Integrable.of_bound
    (continuous_finsetSum _ (fun σ _ => (continuous_replicaGibbs hw B C σ).mul continuous_const)).aestronglyMeasurable
    (∑ σ, |D σ|)
  apply ae_of_all
  intro g
  exact replicaMean_abs_le hw B C (fun σ =>
    Finset.single_le_sum (fun τ _ => abs_nonneg (D τ)) (Finset.mem_univ σ)) g

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

lemma gaussian_replica_test_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, ∑ σ : Fin (r+1) → S,
      D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    ∫ g, ∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C (σ 0) (σ l)-
        ∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  rw [integral_finsetSum _ (fun σ _ => (integrable_linear_mul_replica hw B A C (σ 0) σ).const_mul (D σ)),
    integral_finsetSum _ (fun σ _ => (integrable_replica_covariance hw B A C (σ 0) σ).const_mul (D σ))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_const_mul, gaussian_replica_insertion hw]

end IsingPerceptron

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

section
variable {S : Type*} [Fintype S]

lemma integrable_freshCovarianceMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    Integrable (freshCovarianceMean w B C κ D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (freshCovarianceMean w B C κ D)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (continuous_finsetSum _ (fun σ _ => ((continuous_replicaGibbs hw B C σ).mul continuous_const).mul
      (continuous_finsetSum _ (fun z _ => (continuous_gaussianGibbs hw B C z).mul continuous_const)))).aestronglyMeasurable
  apply Integrable.of_bound hm ((∑ σ, |D σ|)*(∑ p : S × S, |κ p.1 p.2|))
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ σ, |replicaGibbs w B C g σ*D σ*(∑ z, gaussianGibbs w B C g z*κ (σ 0) z)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ σ : Fin (r+1) → S, |D σ| *(∑ p : S × S, |κ p.1 p.2|) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
      have hk := finiteGibbs_average_bound hw (fun x => B x+linearGaussian C g x)
        (κ (σ 0)) (K := ∑ p : S × S, |κ p.1 p.2|) (fun z =>
          Finset.single_le_sum (fun (p : S × S) _ => abs_nonneg (κ p.1 p.2))
            (Finset.mem_univ (σ 0,z)))
      have hprod := mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg (D σ))
      exact mul_le_mul (by simpa only [one_mul] using hprod) hk (abs_nonneg _) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end

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

lemma referenceReplicaMean_eq_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) (g : Fin n → ℝ) :
    referenceReplicaMean ν (fun x => B x+linearGaussian C g x) D =
      replicaMean (fun x => ν.real {x}) B C D g := by
  rw [referenceReplicaMean_finite]
  simp only [referencePartition_finite,replicaMean,replicaGibbs,gaussianGibbs,finiteGibbs,finitePartition]

lemma replicaMean_fresh_eq {S : Type*} [Fintype S] {n r : ℕ}
    (w B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ)
    (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) :
    replicaMean w B C (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) g = freshCovarianceMean w B C κ D g := by
  classical
  have hp (z:S) (σ:Fin (r+1) → S) : replicaGibbs w B C g (Fin.cons z σ) =
      gaussianGibbs w B C g z*replicaGibbs w B C g σ := by
    simp only [replicaGibbs,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  unfold replicaMean
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1+1) => S)),Fintype.sum_prod_type]
  change (∑ z, ∑ σ : Fin (r+1) → S,
    replicaGibbs w B C g (Fin.cons z σ : Fin (r+1+1) → S)*(D σ*κ (σ 0) z)) = _
  simp only [hp]
  rw [Finset.sum_comm]
  unfold freshCovarianceMean
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem finite_gaussian_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => linearGaussian A g (σ 0)*D σ) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i)))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*gaussianCross A C ((Fin.tail τ) 0) (τ 0))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  classical
  let w := fun x => ν.real {x}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  simp_rw [referenceReplicaMean_eq_finite]
  have hi := gaussian_replica_test_insertion hw B A C D
  have he g : (∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ i, (gaussianCross A C (σ 0) (σ i)-∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))) =
      replicaMean w B C (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i))) g -
      (r+1 : ℕ)*freshCovarianceMean w B C (gaussianCross A C) D g := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold replicaMean freshCovarianceMean
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have hleft g : (∑ σ : Fin (r+1) → S, D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)) =
      replicaMean w B C (fun σ => linearGaussian A g (σ 0)*D σ) g := by
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he,hleft] at hi
  rw [integral_sub (integrable_replicaMean hw B C _) ((integrable_freshCovarianceMean hw B C _ D).const_mul _),
    integral_const_mul] at hi
  simpa only [replicaMean_fresh_eq] using hi

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

lemma abs_cylinderCross_le (a b : ℕ →₀ ℝ) :
    |cylinderCross a b| ≤ (a.sum (fun _ c => c^2)+b.sum (fun _ c => c^2))/2 := by
  classical
  let n := a.support.sup id+b.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinder_variance_prefix a ha,cylinder_variance_prefix b hb]
  calc
    _ ≤ ∑ i : Fin n, |a i*b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ((a i)^2+(b i)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [sq_abs (a i),sq_abs (b i),sq_nonneg (|a i|-|b i|)]
    _ = _ := by rw [← Finset.sum_div,Finset.sum_add_distrib]

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

theorem finite_cylinder_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : S → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨n₁,hn₁⟩ := finite_family_support_bound a
  obtain ⟨n₂,hn₂⟩ := finite_family_support_bound b
  let n := n₁+n₂
  let C : S → Fin (n+1) → ℝ := fun x i => a x i
  let B : S → Fin (n+1) → ℝ := fun x i => b x i
  have ha x : ∀ i ∈ (a x).support, i < n+1 := by
    intro i hi
    have := hn₁ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hb x : ∀ i ∈ (b x).support, i < n+1 := by
    intro i hi
    have := hn₂ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hC (g : ℕ → ℝ) x : linearGaussian C (fun i : Fin (n+1) => g i) x = cylinderField (a x) g :=
    (cylinderField_eq_prefix (a x) (ha x) g).symm
  have hB (g : ℕ → ℝ) x : linearGaussian B (fun i : Fin (n+1) => g i) x = cylinderField (b x) g :=
    (cylinderField_eq_prefix (b x) (hb x) g).symm
  have hcov x y : gaussianCross B C x y = cylinderCross (b x) (a y) :=
    (cylinderCross_prefix (b x) (a y) (hb x)).symm
  have hmC : Measurable (fun z : (Fin (n+1) → ℝ) × S => linearGaussian C z.1 z.2) :=
    measurable_from_prod_countable_left (fun x => by unfold linearGaussian; fun_prop)
  have hmL : Measurable (fun z : (Fin (n+1) → ℝ) × (Fin (r+1) → S) =>
      linearGaussian B z.1 (z.2 0)*D z.2) :=
    measurable_from_prod_countable_left (fun σ => by unfold linearGaussian; fun_prop)
  have hp := (gaussian_prefix_measurePreserving (n+1)).hasLaw
  have hL := hp.integral_comp (measurable_referenceReplicaMean ν hmC hmL).aestronglyMeasurable
  have hR₁ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun σ : Fin (r+1) → S =>
      D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) |>.comp measurable_snd)).aestronglyMeasurable
  have hR₂ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))) |>.comp measurable_snd)).aestronglyMeasurable
  have hfinite := finite_gaussian_reference_insertion ν (fun _ => 0) B C D
  simp only [zero_add] at hfinite
  simp_rw [hcov] at hfinite
  simp only [Function.comp_apply,hB,hC] at hL hR₁ hR₂
  rw [hL,hR₁,hR₂]
  exact hfinite

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_PartitionPowLe
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
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

lemma exp_weighted_abs_fourth_bound (h y : ℝ) :
    (Real.exp h*|y|)^4 ≤ Real.exp (8*h)+Real.exp (8*y)+Real.exp (-8*y) := by
  have hy : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
  have hp := pow_le_pow_left₀ (abs_nonneg y) hy 4
  have he : (Real.exp |y|)^4 = Real.exp (4*|y|) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (Real.exp h)^4 by positivity)
  have heh : (Real.exp h)^4 = Real.exp (4*h) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [heh] at hm
  have hs1 : (Real.exp (4*h))^2 = Real.exp (8*h) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hs2 : (Real.exp (4*|y|))^2 = Real.exp (8*|y|) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hay : Real.exp (8*|y|) ≤ Real.exp (8*y)+Real.exp (-8*y) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-8*y)]
    · rw [abs_of_nonpos hy]
      have he : 8*(-y) = -8*y := by ring
      rw [he]; linarith [Real.exp_pos (8*y)]
  rw [mul_pow, heh]
  have hs := sq_nonneg (Real.exp (4*h)-Real.exp (4*|y|))
  have hp0 := mul_nonneg (Real.exp_pos (4*h)).le (Real.exp_pos (4*|y|)).le
  nlinarith

 

lemma gaussian_insertion_numerator_fourth {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
    Integrable (fun z => Real.exp (H z)*|Y z|) (μ.prod ν) ∧
    Integrable (fun ω => A ω^4) μ ∧
    (∫ ω, A ω^4 ∂μ) ≤ Real.exp (32*K)+2*Real.exp (32*L) := by
  let Q := fun z => Real.exp (8*H z)+Real.exp (8*Y z)+Real.exp (-8*Y z)
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  obtain ⟨hiH,hbH⟩ := gaussian_field_exp_integrable (ν := ν) hmH hgH hv 8
  obtain ⟨hiY,hbY⟩ := gaussian_field_exp_integrable (ν := ν) hmY hgY hw 8
  obtain ⟨hinY,hbnY⟩ := gaussian_field_exp_integrable (ν := ν) hmY hgY hw (-8)
  have hiQ : Integrable Q (μ.prod ν) := (hiH.add hiY).add hinY
  have hmA : Measurable A := (hmH.exp.mul hmY.abs).stronglyMeasurable.integral_prod_right'.measurable
  have hnp (z : Ω × X) : 0 ≤ Real.exp (H z)*|Y z| := by positivity
  have hb4 (z : Ω × X) : (Real.exp (H z)*|Y z|)^4 ≤ Q z :=
    exp_weighted_abs_fourth_bound (H z) (Y z)
  have hi4 : Integrable (fun z => (Real.exp (H z)*|Y z|)^4) (μ.prod ν) := by
    apply hiQ.mono' ((hmH.exp.mul hmY.abs).pow_const 4).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_of_nonneg (pow_nonneg (hnp z) _)] using hb4 z
  have hi1 : Integrable (fun z => Real.exp (H z)*|Y z|) (μ.prod ν) := by
    apply ((integrable_const (1:ℝ)).add hiQ).mono' (hmH.exp.mul hmY.abs).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.add_apply, Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (hnp z)]
    have ha := hnp z
    have hp : Real.exp (H z)*|Y z| ≤ 1+(Real.exp (H z)*|Y z|)^4 := by
      nlinarith [sq_nonneg (Real.exp (H z)*|Y z|),
        sq_nonneg ((Real.exp (H z)*|Y z|)^2-1),
        sq_nonneg (Real.exp (H z)*|Y z|-1)]
    linarith [hb4 z]
  have hAle : ∀ᵐ ω ∂μ, A ω^4 ≤ ∫ x, Q (ω,x) ∂ν := by
    filter_upwards [hi1.prod_right_ae, hi4.prod_right_ae, hiQ.prod_right_ae] with ω h1 h4 hQ
    have hJ := (convexOn_pow 4).map_integral_le (continuous_pow 4).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => hnp (ω,x))) h1 h4
    exact hJ.trans (integral_mono h4 hQ (fun x => hb4 (ω,x)))
  have hiA : Integrable (fun ω => A ω^4) μ := by
    apply hiQ.integral_prod_left.mono' (hmA.pow_const 4).aestronglyMeasurable
    filter_upwards [hAle] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A ω^4)]
    exact hω
  refine ⟨hi1, hiA, (integral_mono_ae hiA hiQ.integral_prod_left hAle).trans ?_⟩
  have he : (∫ ω, ∫ x, Q (ω,x) ∂ν ∂μ) =
      (∫ ω, ∫ x, Real.exp (8*H (ω,x)) ∂ν ∂μ) +
      (∫ ω, ∫ x, Real.exp (8*Y (ω,x)) ∂ν ∂μ) +
      (∫ ω, ∫ x, Real.exp (-8*Y (ω,x)) ∂ν ∂μ) := by
    rw [← integral_prod _ hiQ, ← integral_prod _ hiH,
      ← integral_prod _ hiY, ← integral_prod _ hinY]
    exact integral_add (hiH.add hiY) hinY |>.trans
      (congrArg (fun r => r+∫ z, Real.exp (-8*Y z) ∂μ.prod ν) (integral_add hiH hiY))
  rw [he]
  have hK : (8:ℝ)^2*K/2 = 32*K := by ring
  have hL : (8:ℝ)^2*L/2 = 32*L := by ring
  have hnL : (-8:ℝ)^2*L/2 = 32*L := by ring
  rw [hK] at hbH
  rw [hL] at hbY
  rw [hnL] at hbnY
  linarith

lemma square_product_le_fourths (x y : ℝ) : (x*y)^2 ≤ (x^4+y^4)/2 := by
  nlinarith [sq_nonneg (x^2-y^2)]

 

theorem gaussian_gibbs_abs_insertion_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
    Integrable (fun ω => (A ω/Z ω)^2) μ ∧
    (∫ ω, (A ω/Z ω)^2 ∂μ) ≤
      (Real.exp (32*K)+2*Real.exp (32*L)+Real.exp (8*K))/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  obtain ⟨_,hiA,hbA⟩ := gaussian_insertion_numerator_fourth (ν := ν) hmH hmY hgH hgY hv hw
  obtain ⟨_,hiZ,_,hbZ⟩ := gaussian_partition_moments (ν := ν) hmH hgH hv 4
  change Integrable (fun ω => A ω^4) μ at hiA
  change Integrable (fun ω => (Z ω^4)⁻¹) μ at hiZ
  have hmZ : Measurable Z := hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hmA : Measurable A := (hmH.exp.mul hmY.abs).stronglyMeasurable.integral_prod_right'.measurable
  have hb (ω : Ω) : (A ω/Z ω)^2 ≤ (A ω^4+(Z ω^4)⁻¹)/2 := by
    simpa only [div_eq_mul_inv, inv_pow] using square_product_le_fourths (A ω) (Z ω)⁻¹
  have hi : Integrable (fun ω => (A ω/Z ω)^2) μ := by
    apply ((hiA.add hiZ).div_const 2).mono' ((hmA.div hmZ).pow_const 2).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa only [Pi.add_apply, Pi.div_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A ω/Z ω))] using hb ω
  refine ⟨hi, (integral_mono hi ((hiA.add hiZ).div_const 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_div, integral_add hiA hiZ]
  have he : (4:ℝ)^2*K/2 = 8*K := by ring
  simp only [Nat.cast_ofNat] at hbZ
  rw [he] at hbZ
  exact div_le_div_of_nonneg_right (add_le_add hbA hbZ) (by norm_num)



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



lemma gaussian_bounded_insertion_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y D : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    (hmD : Measurable D) {c : ℝ} (_hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    let B := fun ω => ∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν
    Integrable (fun z => Real.exp (H z)*Y z*D z) (μ.prod ν) ∧
    Integrable (fun ω => (B ω/Z ω)^2) μ ∧
    (∫ ω, (B ω/Z ω)^2 ∂μ) ≤
      c^2*((Real.exp (32*K)+2*Real.exp (32*L)+Real.exp (8*K))/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  let B := fun ω => ∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  have hiA := (gaussian_insertion_numerator_fourth (ν := ν) hmH hmY hgH hgY hv hw).1
  have hiB : Integrable (fun z => Real.exp (H z)*Y z*D z) (μ.prod ν) := by
    apply (hiA.const_mul c).mono' (hmH.exp.mul hmY |>.mul hmD).aestronglyMeasurable
    refine Eventually.of_forall fun z => ?_
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left (hD z) (mul_nonneg (Real.exp_pos (H z)).le (abs_nonneg (Y z)))]
  have hBA : ∀ᵐ ω ∂μ, (B ω/Z ω)^2 ≤ c^2*(A ω/Z ω)^2 := by
    filter_upwards [hiA.prod_right_ae,hiB.prod_right_ae] with ω hAω hBω
    have ha : |B ω| ≤ c*A ω := by
      calc
        _ ≤ ∫ x, |Real.exp (H (ω,x))*Y (ω,x)*D (ω,x)| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ x, c*(Real.exp (H (ω,x))*|Y (ω,x)|) ∂ν := by
          apply integral_mono hBω.abs (hAω.const_mul c)
          intro x
          dsimp only
          rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
          nlinarith [mul_le_mul_of_nonneg_left (hD (ω,x))
            (mul_nonneg (Real.exp_pos (H (ω,x))).le (abs_nonneg (Y (ω,x))))]
        _ = c*A ω := integral_const_mul _ _
    have hz : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hb : |B ω/Z ω| ≤ c*A ω/Z ω := by
      rw [abs_div,abs_of_nonneg hz]
      exact div_le_div_of_nonneg_right ha hz
    have hs := pow_le_pow_left₀ (abs_nonneg (B ω/Z ω)) hb 2
    rw [sq_abs] at hs
    simpa only [mul_div_assoc,mul_pow] using hs
  have hi := gaussian_gibbs_abs_insertion_second (ν := ν) hmH hmY hgH hgY hv hw
  have hmB : Measurable B := (hmH.exp.mul hmY |>.mul hmD).stronglyMeasurable.integral_prod_right'.measurable
  have hmZ : Measurable Z := hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiSq : Integrable (fun ω => (B ω/Z ω)^2) μ := by
    apply (hi.1.const_mul (c^2)).mono' ((hmB.div hmZ).pow_const 2).aestronglyMeasurable
    filter_upwards [hBA] with ω hω
    simpa only [Pi.div_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (B ω/Z ω))] using hω
  refine ⟨hiB,hiSq,?_⟩
  calc
    _ ≤ ∫ ω, c^2*(A ω/Z ω)^2 ∂μ := integral_mono_ae hiSq (hi.1.const_mul (c^2)) hBA
    _ = c^2*(∫ ω, (A ω/Z ω)^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.2 (sq_nonneg c)

 

theorem gaussian_insertion_restriction_expectation_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y D : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L)
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ ω, (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x)
      ∂normalizedRestriction ν (A n))/(∫ x, Real.exp (H (ω,x))
      ∂normalizedRestriction ν (A n)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν)/
        (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ)) := by
  let νn := fun n => normalizedRestriction ν (A n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hmB (n) : Measurable (fun ω => (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂νn n)/
      (∫ x, Real.exp (H (ω,x)) ∂νn n)) :=
    (hmH.exp.mul hmY |>.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
      hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hi (n) := gaussian_bounded_insertion_second (ν := νn n) hmH hmY hmD hc hD hgH hgY hv hw
  apply (integral_tendsto_of_second_moment_bound hmB (fun n => (hi n).2.1)
    (fun n => (hi n).2.2) ?_).2
  have he := (gaussian_field_exp_integrable (ν := ν) hmH hgH hv 1).1
  simp only [one_mul] at he
  have hH := gaussian_field_integrable (ν := ν) hmH hgH hv
  have hB := (gaussian_bounded_insertion_second (ν := ν) hmH hmY hmD hc hD hgH hgY hv hw).1
  filter_upwards [he.prod_right_ae,hH.prod_right_ae,hB.prod_right_ae] with ω heω hHω hBω
  have hz : 0 < ∫ x, Real.exp (H (ω,x)) ∂ν :=
    (Real.exp_pos _).trans_le (exp_integral_le_partition hHω heω)
  exact (normalized_restriction_integral_tendsto hAm hA hBω).div
    (normalized_restriction_integral_tendsto hAm hA heω) hz.ne'

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

 

theorem gaussian_bounded_restriction_expectation_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H D : Ω × X → ℝ} (hmH : Measurable H) (hmD : Measurable D)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v : X → NNReal} {K : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K)
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ ω, (∫ x, Real.exp (H (ω,x))*D (ω,x)
      ∂normalizedRestriction ν (A n))/(∫ x, Real.exp (H (ω,x))
      ∂normalizedRestriction ν (A n)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ x, Real.exp (H (ω,x))*D (ω,x) ∂ν)/
        (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ)) := by
  let νn := fun n => normalizedRestriction ν (A n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hmB (n) : Measurable (fun ω => (∫ x, Real.exp (H (ω,x))*D (ω,x) ∂νn n)/
      (∫ x, Real.exp (H (ω,x)) ∂νn n)) :=
    (hmH.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
      hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  apply tendsto_integral_of_dominated_convergence (fun _ => c)
  · exact fun n => (hmB n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    have he := (gaussian_field_exp_integrable (ν := νn n) hmH hgH hv 1).1
    simp only [one_mul] at he
    filter_upwards [he.prod_right_ae] with ω heω
    rw [Real.norm_eq_abs]
    exact abs_bounded_gibbs_test_le heω (hmD.comp (measurable_const.prodMk measurable_id))
      hc (fun x => hD (ω,x))
  · have he := (gaussian_field_exp_integrable (ν := ν) hmH hgH hv 1).1
    simp only [one_mul] at he
    have hH := gaussian_field_integrable (ν := ν) hmH hgH hv
    have hB : Integrable (fun z => Real.exp (H z)*D z) (μ.prod ν) :=
      he.mul_bdd hmD.aestronglyMeasurable
        (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hD z))
    filter_upwards [he.prod_right_ae,hH.prod_right_ae,hB.prod_right_ae] with ω heω hHω hBω
    have hz : 0 < ∫ x, Real.exp (H (ω,x)) ∂ν :=
      (Real.exp_pos _).trans_le (exp_integral_le_partition hHω heω)
    exact (normalized_restriction_integral_tendsto hAm hA hBω).div
      (normalized_restriction_integral_tendsto hAm hA heω) hz.ne'

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NormalizedRestrictionPi
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
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

lemma replica_restriction_mass_ne_zero {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : ν A ≠ 0) :
    (Measure.pi (fun _ : ι => ν)) (Set.univ.pi (fun _ => A)) ≠ 0 := by
  rw [Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hA)

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

lemma cylinder_replica_law {X : Type*} (a : X → ℕ →₀ ℝ) {r : ℕ} (σ : Fin r → X) :
    gaussianCoordinates.map (fun g => ∑ i, cylinderField (a (σ i)) g) =
      gaussianReal 0 (((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal) := by
  have he : (fun g => ∑ i, cylinderField (a (σ i)) g) = cylinderField (∑ i, a (σ i)) := by
    funext g
    exact (cylinderField_finset_sum Finset.univ _ g).symm
  rw [he,cylinderField_law]

lemma cylinder_replica_variance_le {X : Type*} (a : X → ℕ →₀ ℝ) {K : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) {r : ℕ} (σ : Fin r → X) :
    ((((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal : ℝ)) ≤ (r:ℝ)^2*K := by
  have hnonneg : 0 ≤ (∑ i, a (σ i)).sum (fun _ c => c^2) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.coe_toNNReal _ hnonneg]
  simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => a (σ i)) (fun i => ha (σ i))

theorem cylinder_replica_restriction_tendsto {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    {r : ℕ} (D : (Fin r → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g) D ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin r → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have ht := gaussian_bounded_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin r => ν)) hmH (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (cylinder_replica_variance_le a ha)
    (A := fun n => Set.univ.pi (fun _ : Fin r => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,referenceReplicaMean_eq_ratio,← normalizedRestriction_pi (fun _ : Fin r => A _)
    (fun _ => hpos _)] using ht

theorem cylinder_replica_insertion_restriction_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Measure X} [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) (fun σ => cylinderField (b (σ 0)) g*D σ)
      ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
        (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmY : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) => cylinderField (b (z.2 0)) z.1) :=
    (measurable_cylinderFields b).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hv (σ : Fin (r+1) → X) : (((b (σ 0)).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ L := by
    have hnonneg : 0 ≤ (b (σ 0)).sum (fun _ c => c^2) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.coe_toNNReal _ hnonneg]
    exact hb (σ 0)
  have ht := gaussian_insertion_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
    (A := fun n => Set.univ.pi (fun _ : Fin (r+1) => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,mul_assoc,referenceReplicaMean_eq_ratio,
    ← normalizedRestriction_pi (fun _ : Fin (r+1) => A _) (fun _ => hpos _)] using ht

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

lemma finite_restriction_cylinder_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : A.Finite) (hp : ν A ≠ 0)
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  let := hA.fintype
  have hmA : MeasurableSet A := hA.measurableSet
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hmA hp
  have he {q : ℕ} (g : ℕ → ℝ) (F : (Fin q → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν A) (fun x => cylinderField (a x) g)
        (fun σ => F (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g) F :=
    referenceReplicaMean_subtype hmA hp (H := fun x => cylinderField (a x) g)
      (D := F) (measurable_of_countable _) (measurable_of_countable _)
  have hi := finite_cylinder_reference_insertion (subtypeReference ν A)
    (fun x => a x) (fun x => b x) (fun σ => D (fun i => (σ i : X)))
  convert (config := {transparency := .instances, preTransparency := .instances}) hi using 1
  · congr 1
    funext g
    exact (he g (fun σ => cylinderField (b (σ 0)) g*D σ)).symm
  · congr 1
    · congr 1
      funext g
      exact (he g (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))).symm
    · congr 1
      congr 1
      funext g
      exact (he g (fun τ : Fin (r+1+1) → X =>
        D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))).symm

theorem countable_cylinder_reference_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨A,hfin,hpos,hA⟩ := countable_reference_exhaustion ν
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      |cylinderCross (b x) (a y)| ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 :=
        abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B] <;> linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun i _ => hcross _ _)
      _ = (r+1 : ℕ)*B := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]
    exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]
    exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  have hleft := cylinder_replica_insertion_restriction_tendsto a b ha hb D hc hD hA hpos
  have hright₁ := cylinder_replica_restriction_tendsto a ha
    (fun σ : Fin (r+1) → X => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))
    (c := c*((r+1 : ℕ)*B)) (by positivity) hfirst hA hpos
  have hright₂ := cylinder_replica_restriction_tendsto a ha
    (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
    (c := c*B) (mul_nonneg hc hB) hfresh hA hpos
  apply tendsto_nhds_unique hleft
  exact (hright₁.sub (hright₂.const_mul ((r+1 : ℕ) : ℝ))).congr
    (fun n => (finite_restriction_cylinder_insertion (hfin n) (hpos n) a b D).symm)

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

lemma measurable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd))
    ((measurable_of_countable D).comp measurable_snd)

lemma integrable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun ω => ∫ g, referenceReplicaMean (ν ω)
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) P := by
  apply integrable_of_measurable_abs_le
    (measurable_random_cylinder_mean hν a D |>.stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  apply abs_integral_le_const_of_bound
    ((measurable_random_cylinder_mean hν a D).comp measurable_prodMk_left)
  intro g
  exact referenceReplicaMean_abs_le (ν ω) (fun x => cylinderField (a x) g)
    D (measurable_of_countable _) hc hD

theorem random_countable_cylinder_insertion_oai {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates ∂P) =
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates ∂P) -
    (r+1 : ℕ)*(∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates ∂P) := by
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      _ ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 := abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B] <;> linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      _ ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun _ _ => hcross _ _)
      _ = _ := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]; exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]; exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  simp_rw [countable_cylinder_reference_insertion _ a b ha hb D hc hD]
  rw [integral_sub (integrable_random_cylinder_mean hν a _ (by positivity) hfirst)
    ((integrable_random_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh).const_mul _),integral_const_mul]

end IsingPerceptron

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.IsingPerceptron.random_countable_cylinder_insertion_oai.{u_1, u_2} := @OAI.IsingPerceptron.random_countable_cylinder_insertion_oai.{u_1, u_2}
