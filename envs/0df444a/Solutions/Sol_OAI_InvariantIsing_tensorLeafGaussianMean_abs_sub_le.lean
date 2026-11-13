-- Prove2me | solution 1 for OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:46.379272+00:00
-- url     : https://prove2.me/submissions/f71b3bc3-6a43-4faa-87a4-35da2d032066

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

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



theorem gaussian_log_restriction_expectation_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K)
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ ω, Real.log (∫ x, Real.exp (H (ω,x))
      ∂normalizedRestriction ν (A n)) ∂μ) atTop
      (𝓝 (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ)) := by
  let νn := fun n => normalizedRestriction ν (A n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hmZ (n) : Measurable (fun ω => Real.log (∫ x, Real.exp (H (ω,x)) ∂νn n)) :=
    hm.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hi (n) := gaussian_log_partition_second (ν := νn n) hm hg hv
  apply (integral_tendsto_of_second_moment_bound hmZ (fun n => (hi n).1)
    (fun n => (hi n).2) ?_).2
  have he := (gaussian_field_exp_integrable (ν := ν) hm hg hv 1).1
  simp only [one_mul] at he
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  filter_upwards [he.prod_right_ae,hH.prod_right_ae] with ω heω hHω
  have hz : 0 < ∫ x, Real.exp (H (ω,x)) ∂ν :=
    (Real.exp_pos _).trans_le (exp_integral_le_partition hHω heω)
  exact (Real.continuousAt_log hz.ne').tendsto.comp
    (normalized_restriction_integral_tendsto hAm hA heω)



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
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cylinderCross_smul_right (a b : ℕ →₀ ℝ) (t : ℝ) :
    cylinderCross a (t • b) = t*cylinderCross a b := by
  simp only [cylinderCross,Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
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

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureLipschitz
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frobenius continuity of Haar pressure

The Lipschitz constant is independent of dimension and of a deterministic
magnetic field. This is the finite-volume estimate required to apply the
published SO(N) concentration input.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma specialRotation_spin_dist_sq_le {N : ℕ} (U V : SpecialOrthogonal N)
    (σ : Spin N) :
    (∑ i, (specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i) ^ 2) ≤
      (N : ℝ) * frobeniusDistance U V ^ 2 := by
  have he (i : Fin N) : specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i =
      ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j -
        (V : Matrix (Fin N) (Fin N) ℝ) i j) * spinValue (σ j) := by
    simp only [specialRotation_apply, spinVector_apply, sub_mul, Finset.sum_sub_distrib]
  have hrow (i : Fin N) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (U : Matrix (Fin N) (Fin N) ℝ) i j -
      (V : Matrix (Fin N) (Fin N) ℝ) i j) (fun j => spinValue (σ j))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Finset.sum_mul] at hsum
  simp_rw [he]
  rw [frobeniusDistance, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapBounds
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent bounds for projected spectral overlap kernels. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace InvariantIsing

lemma abs_projected_cross_difference_sum_le {N : ℕ}
    (U V W : SpecialOrthogonal N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |∑ i ∈ I, (specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i) *
      specialRotation W (spinVector τ) i| ≤ N * frobeniusDistance U V := by
  let d := frobeniusDistance U V
  let x := fun i => specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i
  let y := fun i => specialRotation W (spinVector τ) i
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hx : (∑ i ∈ I, x i ^ 2) ≤ N * d ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => sq_nonneg _)).trans (specialRotation_spin_dist_sq_le U V σ)
  have hy : (∑ i ∈ I, y i ^ 2) ≤ N := projected_spin_sq_sum_le _ I τ
  have hsq : (∑ i ∈ I, x i * y i) ^ 2 ≤ ((N : ℝ) * d) ^ 2 := by
    calc
      _ ≤ (∑ i ∈ I, x i ^ 2) * ∑ i ∈ I, y i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq I x y
      _ ≤ ((N : ℝ) * d ^ 2) * N := mul_le_mul hx hy
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov
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

lemma abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, |f i| ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, |g i| ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hp : |∏ i ∈ s, f i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hf'
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |(f a - g a) * (∏ i ∈ s, f i) +
          g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by congr 1; ring
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| +
          |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          ((f a - g a) * (∏ i ∈ s, f i))
          (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      _ ≤ |f a - g a| * 1 + 1 * ∑ i ∈ s, |f i - g i| :=
        add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul (hg a (Finset.mem_insert_self a s)) (ih hf' hg')
            (abs_nonneg _) (by norm_num))
      _ = _ := by ring

lemma abs_pow_sub_pow_le_degree {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (d : ℕ) :
    |x ^ d - y ^ d| ≤ d * |x - y| := by
  have hp : max |x| |y| ^ (d - 1) ≤ 1 :=
    pow_le_one₀ (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le hx hy)
  calc
    _ ≤ |x - y| * d * max |x| |y| ^ (d - 1) := abs_pow_sub_pow_le x y d
    _ ≤ |x - y| * d * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_MixedSpectralFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-rotation tensor covariances for Gaussian mean comparison. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma mixedProjectedOverlap_abs_le_one {N : ℕ} (U V : Rotation N)
    (I : Finset (Fin N)) (σ τ : Spin N) : |mixedProjectedOverlap U V I σ τ| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => U (spinVector σ) i) (fun i => V (spinVector τ) i)
  have hs : (∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i) ^ 2 ≤ (N : ℝ) ^ 2 := by
    apply hcs.trans
    simpa only [pow_two] using
      (mul_le_mul (projected_spin_sq_sum_le U I σ) (projected_spin_sq_sum_le V I τ)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  have ha : |∑ i ∈ I, U (spinVector σ) i * V (spinVector τ) i| ≤ N :=
    (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mp (by simpa only [sq_abs] using hs)
  unfold mixedProjectedOverlap
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (inv_mul_cancel₀ hn)

lemma mixedProjectedOverlap_sub_first_le {N : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Finset (Fin N)) (σ τ : Spin N) :
    |mixedProjectedOverlap (specialRotation U) (specialRotation W) I σ τ -
      mixedProjectedOverlap (specialRotation V) (specialRotation W) I σ τ| ≤
        frobeniusDistance U V := by
  have he : mixedProjectedOverlap (specialRotation U) (specialRotation W) I σ τ -
      mixedProjectedOverlap (specialRotation V) (specialRotation W) I σ τ =
      (N : ℝ)⁻¹ * ∑ i ∈ I,
        (specialRotation U (spinVector σ) i - specialRotation V (spinVector σ) i) *
          specialRotation W (spinVector τ) i := by
    simp only [mixedProjectedOverlap, ← mul_sub, ← Finset.sum_sub_distrib, sub_mul]
  rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * (N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left (abs_projected_cross_difference_sum_le U V W I σ τ) (by positivity)
    _ = _ := by field_simp

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

/-- The cross covariance of a tensor increment with any rotated tensor
has a dimension-independent rotation modulus. -/
theorem spectralMonomialFeature_increment_cross_le {N m : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (σ τ : Spin N) :
    |∑ v : SpectralTensorIndex I d,
      (spectralMonomialFeature (specialRotation U) I d σ v -
        spectralMonomialFeature (specialRotation V) I d σ v) *
          spectralMonomialFeature (specialRotation W) I d τ v| ≤
      (∑ a, (d a : ℝ)) * frobeniusDistance U V := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, spectralMonomialFeature_mixed_cross,
    spectralMonomialFeature_mixed_cross]
  have hpow (R : SpecialOrthogonal N) (a : Fin m) :
      |mixedProjectedOverlap (specialRotation R) (specialRotation W) (I a) σ τ ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (mixedProjectedOverlap_abs_le_one _ _ _ _ _)
  calc
    _ ≤ ∑ a, |mixedProjectedOverlap (specialRotation U) (specialRotation W) (I a) σ τ ^ d a -
        mixedProjectedOverlap (specialRotation V) (specialRotation W) (I a) σ τ ^ d a| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hpow U a) (fun a _ => hpow V a)
    _ ≤ ∑ a, (d a : ℝ) * frobeniusDistance U V := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_pow_sub_pow_le_degree (mixedProjectedOverlap_abs_le_one _ _ _ _ _)
        (mixedProjectedOverlap_abs_le_one _ _ _ _ _) (d a)).trans
        (mul_le_mul_of_nonneg_left (mixedProjectedOverlap_sub_first_le hN U V W (I a) σ τ)
          (Nat.cast_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorRotationCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation continuity of the concrete finite tensor perturbation marks. -/

noncomputable section

open scoped BigOperators NNReal

namespace InvariantIsing

lemma spinTensorFeature_increment_covariance {N m k : ℕ}
    (U V W : Rotation N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    (∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      (spinTensorFeature U I degree amplitude σ i - spinTensorFeature V I degree amplitude σ i) *
        spinTensorFeature W I degree amplitude τ i) =
      ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
        ∑ v : SpectralTensorIndex I (degree j),
          (spectralMonomialFeature U I (degree j) σ v -
            spectralMonomialFeature V I (degree j) σ v) *
              spectralMonomialFeature W I (degree j) τ v := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, spinTensorFeature, sub_self, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Linear spin-field marks cancel in the rotation increment. Only the
finite spectral tensor covariance contributes to the rotation modulus. -/
theorem spinTensorFeature_increment_covariance_le {N m k : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : ℝ≥0) (monomial : Fin k → ℝ≥0) (σ τ : Spin N) :
    |∑ i : SpinTensorIndex I degree, (tensorVarianceProfile I degree site monomial i : ℝ) *
      (spinTensorFeature (specialRotation U) I degree amplitude σ i -
        spinTensorFeature (specialRotation V) I degree amplitude σ i) *
          spinTensorFeature (specialRotation W) I degree amplitude τ i| ≤
      (∑ j, (monomial j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ)) *
        frobeniusDistance U V := by
  rw [spinTensorFeature_increment_covariance]
  calc
    _ ≤ ∑ j, |(monomial j : ℝ) * amplitude j ^ 2 *
        ∑ v : SpectralTensorIndex I (degree j),
          (spectralMonomialFeature (specialRotation U) I (degree j) σ v -
            spectralMonomialFeature (specialRotation V) I (degree j) σ v) *
              spectralMonomialFeature (specialRotation W) I (degree j) τ v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (monomial j : ℝ) * amplitude j ^ 2 *
        ((∑ a, (degree j a : ℝ)) * frobeniusDistance U V) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (spectralMonomialFeature_increment_cross_le hN U V W I (degree j) σ τ)
        (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

lemma cylinderCross_sub_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a - b) c = cylinderCross a c - cylinderCross b c := by
  have h := cylinderCross_add_left (a - b) b c
  rw [sub_add_cancel] at h
  linarith

/-- The full root/ancestor tensor increment has a uniform covariance
modulus, independently of the pair of cascade leaves. -/
theorem tensorLeafCoefficients_increment_cross_le {N m k : ℕ} (hN : 0 < N)
    (U V W : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (x y : Spin N × LabeledLeaf n) :
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |cylinderCross (A U x - A V x) (A W y)| ≤
      (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ)) * frobeniusDistance U V := by
  intro A
  let L := fun i : Fin (n + 1) => ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
    ∑ a, (degree j a : ℝ)
  let Q := fun i : Fin (n + 1) => ∑ j : SpinTensorIndex I degree,
    (tensorVarianceProfile I degree (site i) (monomial i) j : ℝ) *
      (spinTensorFeature (specialRotation U) I degree amplitude x.1 j -
        spinTensorFeature (specialRotation V) I degree amplitude x.1 j) *
          spinTensorFeature (specialRotation W) I degree amplitude y.1 j
  have hL (i : Fin (n + 1)) : 0 ≤ L i := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _))
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hQ (i : Fin (n + 1)) : |Q i| ≤ L i * frobeniusDistance U V :=
    spinTensorFeature_increment_covariance_le hN U V W I degree amplitude (site i) (monomial i) x.1 y.1
  have he : cylinderCross (A U x - A V x) (A W y) =
      ∑ i : Fin (n + 1), if i.1 ≤ labeledCommonDepth n x.2 y.2 then Q i else 0 := by
    rw [cylinderCross_sub_left]
    dsimp only [A]
    rw [tensorLeafCoefficients_cross, tensorLeafCoefficients_cross, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 ≤ labeledCommonDepth n x.2 y.2
    · simp only [hi, ite_true, if_true]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [hi, ite_false, if_false, sub_self]
  rw [he]
  calc
    _ ≤ ∑ i : Fin (n + 1), |if i.1 ≤ labeledCommonDepth n x.2 y.2 then Q i else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n + 1), L i * frobeniusDistance U V := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact hQ i
      · simp only [abs_zero]
        exact mul_nonneg (hL i) (show 0 ≤ frobeniusDistance U V from Real.sqrt_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianMeanInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian mean interpolation with arbitrary base energy and weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

omit [Fintype X] in
lemma linearGaussian_affine {d : ℕ} (C A : X → Fin d → ℝ) (s : ℝ)
    (g : Fin d → ℝ) (x : X) :
    linearGaussian (affineGaussianCoefficients C A s) g x =
      linearGaussian C g x + s * linearGaussian A g x := by
  simp only [linearGaussian, affineGaussianCoefficients, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma affineGaussianMean_hasDerivAt {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (affineGaussianMean w H C A) (affineGaussianSlope w H C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g => Real.log (finitePartition w
      (fun x => H x + linearGaussian (affineGaussianCoefficients C A s) g x))) μ := by
    simpa only [one_mul] using
      (continuous_log_finitePartition hw H (affineGaussianCoefficients C A s) 1).aestronglyMeasurable
  have hi : Integrable (fun g => Real.log (finitePartition w
      (fun x => H x + linearGaussian (affineGaussianCoefficients C A t) g x))) μ := by
    simpa only [one_mul] using integrable_log_finitePartition hw H (affineGaussianCoefficients C A t) 1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x, gaussianGibbs w H (affineGaussianCoefficients C A s) g x *
      linearGaussian A g x) (bound := fun g => ∑ x, |linearGaussian A g x|)
    (Filter.univ_mem) (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · exact (continuous_finsetSum _ (fun x _ =>
      (continuous_gaussianGibbs hw H _ x).mul (by unfold linearGaussian; fun_prop))).aestronglyMeasurable
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    exact finiteGibbs_average_bound hw _ _ (fun x =>
      Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
  · exact integrable_finsetSum _ (fun x _ => (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    apply hasDerivAt_log_finitePartition hw
    intro x
    simp_rw [linearGaussian_affine]
    simpa only [one_mul, id_eq] using (((hasDerivAt_id s).mul_const (linearGaussian A g x)).const_add
      (linearGaussian C g x)).const_add (H x)

lemma expectedGaussianEnergy_abs_le {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (A C : X → Fin (d + 1) → ℝ) {K : ℝ}
    (hK : ∀ x y, |gaussianCross A C x y| ≤ K) :
    |∫ g, ∑ x, gaussianGibbs w H C g x * linearGaussian A g x
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)| ≤ 2 * K := by
  have hb (g : Fin (d + 1) → ℝ) (x : X) :
      |gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y| ≤ 2 * K := by
    have hh := finiteGibbs_average_bound hw (fun y => H y + linearGaussian C g y)
      (fun y => gaussianCross A C x y) (hK x)
    exact (abs_sub _ _).trans (by dsimp only [gaussianGibbs] at * <;> linarith [hK x x])
  have hc (x : X) : Integrable (fun g => gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y))
      (Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) := by
    apply Integrable.of_bound
      ((continuous_gaussianGibbs hw H C x).mul
        (continuous_const.sub (continuous_finsetSum _ (fun y _ =>
          (continuous_gaussianGibbs hw H C y).mul continuous_const)))).aestronglyMeasurable (2 * K)
    apply ae_of_all
    intro g
    change ‖gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show 0 ≤ gaussianGibbs w H C g x from finiteGibbs_nonneg hw _ x)]
    exact (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hb g x)
  rw [integral_finsetSum _ (fun x _ => by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x)]
  simp_rw [mul_comm (gaussianGibbs w H C _ _) (linearGaussian A _ _),
    gaussian_gibbs_insertion hw H A C]
  rw [← integral_finsetSum _ (fun x _ => hc x)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1))
      (f := fun g => ∑ x, gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y))
      (C := 2 * K) (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs]
        exact finiteGibbs_average_bound hw (fun x => H x + linearGaussian C g x) _ (hb g))))

/-- A dimension-independent mean comparison. The cross-covariance of the
increment with the interpolated field, rather than the Gaussian coordinate
count, determines the bound. -/
theorem affineGaussianMean_abs_sub_le {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin (d + 1) → ℝ) {K : ℝ}
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |gaussianCross A (affineGaussianCoefficients C A s) x y| ≤ K) :
    |affineGaussianMean w H C A 1 - affineGaussianMean w H C A 0| ≤ 2 * K := by
  have hd (s : ℝ) := affineGaussianMean_hasDerivAt hw H C A s
  have hb (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |affineGaussianSlope w H C A s| ≤ 2 * K :=
    expectedGaussianEnergy_abs_le hw H A (affineGaussianCoefficients C A s) (hK s hs)
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => by simpa only [Real.norm_eq_abs] using hb s (Set.Ico_subset_Icc_self hs))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_CountableGaussianComparison
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean comparison for the actual countable spin/cascade-leaf prior. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma finite_cylinder_mean_increment_le {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (C A : X → ℕ →₀ ℝ) {K : ℝ}
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x + A x) g) ν 1 ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x) g) ν 1 ∂gaussianCoordinates| ≤ 2 * K := by
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
  have hk (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x y : X) :
      |gaussianCross A' (affineGaussianCoefficients C' A' s) x y| ≤ K := by
    have hc := cylinderCross_prefix (A x) (C y + s • A y) (hA x)
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hc
    have hh := hK s hs x y
    rw [hc] at hh
    exact hh
  have he (s : ℝ) (g : ℕ → ℝ) :
      cgf (fun x => cylinderField (C x + s • A x) g) ν 1 =
        Real.log (finitePartition w (fun x => 0 +
          linearGaussian (affineGaussianCoefficients C' A' s)
            (fun i : Fin (n + 1) => g i) x)) := by
    unfold cgf mgf
    rw [integral_fintype Integrable.of_finite]
    simp only [one_mul, zero_add, finitePartition]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [cylinderField_add, cylinderField_smul,
      cylinderField_eq_prefix (C x) (hC x), cylinderField_eq_prefix (A x) (hA x),
      linearGaussian_affine]
    rfl
  have hm (s : ℝ) : (∫ g : ℕ → ℝ,
      cgf (fun x => cylinderField (C x + s • A x) g) ν 1 ∂gaussianCoordinates) =
      affineGaussianMean w (fun _ => 0) C' A' s := by
    simp_rw [he s]
    exact (gaussian_prefix_measurePreserving (n + 1)).hasLaw.integral_comp
      (by simpa only [one_mul] using
        (continuous_log_finitePartition hw (fun _ => 0) (affineGaussianCoefficients C' A' s) 1).aestronglyMeasurable)
  have hc := affineGaussianMean_abs_sub_le hw (fun _ => 0) C' A' hk
  rw [← hm 1, ← hm 0] at hc
  simpa only [one_smul, zero_smul, add_zero] using hc

lemma cylinder_cgf_restriction_mean_tendsto {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g)
      (normalizedRestriction ν (S n)) 1 ∂gaussianCoordinates) atTop
      (𝓝 (∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g) ν 1 ∂gaussianCoordinates)) := by
  have hv (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  simpa only [cgf, mgf, one_mul] using
    gaussian_log_restriction_expectation_tendsto (measurable_cylinderFields A)
      (fun x => cylinderField_law (A x)) hv hS hExh hpos

/-- The finite Gaussian mean estimate passes to countable leaf priors.
The two endpoint variance caps ensure convergence of their actual means. -/
theorem countable_cylinder_mean_increment_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hCA : ∀ x, (C x + A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x + A x) g) ν 1 ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x) g) ν 1 ∂gaussianCoordinates| ≤ 2 * K := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hm₀ := cylinder_cgf_restriction_mean_tendsto ν C hC
    (fun n => (hS n).measurableSet) hExh hpos
  have hm₁ := cylinder_cgf_restriction_mean_tendsto ν (fun x => C x + A x) hCA
    (fun n => (hS n).measurableSet) hExh hpos
  apply le_of_tendsto ((hm₁.sub hm₀).abs)
  apply Filter.Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := finite_cylinder_mean_increment_le (subtypeReference ν (S n))
    (fun x => C x) (fun x => A x) (fun s hs x y => hK s hs x y)
  have he (Q : X → ℕ →₀ ℝ) (g : ℕ → ℝ) :
      cgf (fun x : S n => cylinderField (Q x) g) (subtypeReference ν (S n)) 1 =
        cgf (fun x => cylinderField (Q x) g) (normalizedRestriction ν (S n)) 1 := by
    unfold cgf mgf
    congr 1
    exact (subtypeReference_preserving ν (hS n).measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (1 * cylinderField (Q x) g))).aestronglyMeasurable
  have heplus (g : ℕ → ℝ) :
      cgf (fun x : S n => cylinderField (C x + A x) g) (subtypeReference ν (S n)) 1 =
        cgf (fun x => cylinderField (C x + A x) g) (normalizedRestriction ν (S n)) 1 :=
    he (fun x => C x + A x) g
  simpa only [heplus, he C] using hf

lemma cylinder_log_partition_mean_base {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) = Real.log (∫ x, Real.exp (H x) ∂ν) +
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g) (ν.tilted H) 1 ∂gaussianCoordinates := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have he := cylinder_log_partition_base ν H hH A hA 1
  simp only [one_mul] at he
  rw [integral_congr_ae he, integral_add (integrable_const _)
    ((cylinder_cgf_memLp_two (ν.tilted H) A hA 1).integrable (by norm_num))]
  simp only [integral_const, probReal_univ, one_smul]

/-- The Gaussian mean comparison holds with the actual deterministic base
energy and any countable probability prior, including cascade-leaf weights. -/
theorem countable_cylinder_log_mean_increment_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hCA : ∀ x, (C x + A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x + A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  rw [cylinder_log_partition_mean_base ν H hH (fun x => C x + A x) hCA,
    cylinder_log_partition_mean_base ν H hH C hC, add_sub_add_left_eq_sub]
  exact countable_cylinder_mean_increment_le (ν.tilted H) C A hC hCA hK

lemma cylinderCross_add_right (a b c : ℕ →₀ ℝ) :
    cylinderCross a (b + c) = cylinderCross a b + cylinderCross a c := by
  unfold cylinderCross
  simp only [Finsupp.add_apply, mul_add, Finsupp.sum]
  exact Finset.sum_add_distrib

/-- Endpoint mixed-cross bounds control the whole coefficient segment. -/
lemma cylinderCross_segment_bound {X : Type*} (A C : X → ℕ →₀ ℝ) {L : ℝ}
    (h₀ : ∀ x y, |cylinderCross (A x - C x) (C y)| ≤ L)
    (h₁ : ∀ x y, |cylinderCross (A x - C x) (A y)| ≤ L)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x y : X) :
    |cylinderCross (A x - C x) (C y + s • (A y - C y))| ≤ L := by
  have he : C y + s • (A y - C y) = (1 - s) • C y + s • A y := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [he, cylinderCross_add_right, cylinderCross_smul_right, cylinderCross_smul_right]
  calc
    _ ≤ |(1 - s) * cylinderCross (A x - C x) (C y)| +
        |s * cylinderCross (A x - C x) (A y)| := abs_add_le _ _
    _ = (1 - s) * |cylinderCross (A x - C x) (C y)| +
        s * |cylinderCross (A x - C x) (A y)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - s) * L + s * L := add_le_add
      (mul_le_mul_of_nonneg_left (h₀ x y) (sub_nonneg.mpr hs.2))
      (mul_le_mul_of_nonneg_left (h₁ x y) hs.1)
    _ = L := by ring

/-- The form used for rotation comparison: any two bounded-variance
coefficient families on the actual countable prior can be compared from
mixed cross-covariances of their increment with the two endpoints. -/
theorem countable_cylinder_log_mean_compare {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A C : X → ℕ →₀ ℝ) {B₀ B₁ L : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (h₀ : ∀ x y, |cylinderCross (A x - C x) (C y)| ≤ L)
    (h₁ : ∀ x y, |cylinderCross (A x - C x) (A y)| ≤ L) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * L := by
  have he (x : X) : C x + (A x - C x) = A x := by abel
  have h := countable_cylinder_log_mean_increment_le ν H hH C (fun x => A x - C x)
    hC (fun x => by simpa only [he] using hA x)
    (fun s hs x y => cylinderCross_segment_bound A C h₀ h₁ hs x y)
  simpa only [he] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGaussianMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mean rotation comparison on the concrete countable tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- The Gaussian part of the disorder-averaged leaf partition has a
uniform rotation modulus for every countable probability leaf prior. -/
theorem tensorLeafGaussianMean_abs_sub_le_oai {N m k : ℕ} (hN : 0 < N)
    (U V : SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ) (n : ℕ)
    (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (H : Spin N × LabeledLeaf n → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν) :
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A U x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A V x) g) ∂ν)
        ∂gaussianCoordinates| ≤
      2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ)) * frobeniusDistance U V := by
  intro A
  have h := countable_cylinder_log_mean_compare ν H hH (A U) (A V)
    (tensorLeafCoefficients_variance_le (specialRotation V) I degree amplitude n site monomial)
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial)
    (tensorLeafCoefficients_increment_cross_le hN U V V I degree amplitude n site monomial)
    (tensorLeafCoefficients_increment_cross_le hN U V U I degree amplitude n site monomial)
  simpa only [mul_assoc] using h

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le_oai := @OAI.InvariantIsing.tensorLeafGaussianMean_abs_sub_le_oai
