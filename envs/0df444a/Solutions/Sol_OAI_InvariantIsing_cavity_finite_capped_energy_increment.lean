-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_finite_capped_energy_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:30.808298+00:00
-- url     : https://prove2.me/submissions/c649ac2a-0ea4-4edc-a59f-e9fa319c1515

import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafCoefficients
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPerturbationKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The overlap modulus of the finite Gaussian perturbation covariance.
The geometric weights absorb the enumerated monomial degrees. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_monomial_difference {m : ℕ} (A B : Fin m → ℝ) (d : Fin m → ℕ)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1)
    {δ : ℝ} (hd : ∀ a, |A a - B a| ≤ δ) :
    |(∏ a, A a ^ d a) - ∏ a, B a ^ d a| ≤ (∑ a, (d a : ℝ)) * δ := by
  have hp (a : Fin m) : |A a ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hA a)
  have hq (a : Fin m) : |B a ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hB a)
  calc
    _ ≤ ∑ a, |A a ^ d a - B a ^ d a| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hp a) (fun a _ => hq a)
    _ ≤ ∑ a, (d a : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_pow_sub_pow_le_degree (hA a) (hB a) (d a)).trans
        (mul_le_mul_of_nonneg_left (hd a) (Nat.cast_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The common tree coordinate does not enlarge the overlap error. -/
lemma cavity_spectral_tree_kernel_difference {m : ℕ}
    (A B : Fin m → ℝ) (d : Fin m → ℕ) (r : ℕ) (q : ℝ)
    (hA : ∀ a, |A a| ≤ 1) (hB : ∀ a, |B a| ≤ 1) (hq : |q| ≤ 1)
    {δ : ℝ} (hd : ∀ a, |A a - B a| ≤ δ) :
    |(∏ a, A a ^ d a) * q ^ r - (∏ a, B a ^ d a) * q ^ r| ≤
      (∑ a, (d a : ℝ)) * δ := by
  rw [← sub_mul, abs_mul]
  have hqr : |q ^ r| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hq
  exact (mul_le_mul_of_nonneg_left hqr (abs_nonneg _)).trans
    (by simpa only [mul_one] using cavity_monomial_difference A B d hA hB hd)

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

lemma cavity_weighted_kernel_tail_le (N n : ℕ) (u K : Fin n → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u j ^ 2 * K j| ≤
      4 * (1 / 2 : ℝ) ^ N := by
  have hw (j : Fin n) : perturbationWeight (N + j) =
      (1 / 2 : ℝ) ^ N * perturbationWeight j := by
    unfold perturbationWeight
    rw [← pow_add]
    congr 1
  have he : (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u j ^ 2 * K j) =
      ((1 / 2 : ℝ) ^ N) ^ 2 * (∑ j : Fin n, perturbationWeight j ^ 2 * u j ^ 2 * K j) := by
    simp only [hw, mul_pow, Finset.mul_sum, mul_assoc]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((1 / 2 : ℝ) ^ N) ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left (cavity_weighted_kernel_abs_le u K hu hK) (sq_nonneg _)
    _ ≤ _ := by
      have h0 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N
      have h1 := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := N)
      nlinarith

lemma cavity_covariance_mass_difference {P Q a b δ : ℝ}
    (ha : 0 ≤ a) (hP : |P| ≤ 4) (hPQ : |P - Q| ≤ δ) :
    |b * P - a * Q| ≤ 4 * |b - a| + a * δ := by
  calc
    _ = |(b - a) * P + a * (P - Q)| := by congr 1; ring
    _ ≤ |(b - a) * P| + |a * (P - Q)| := abs_add_le _ _
    _ ≤ |b - a| * 4 + a * δ := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ ha)
    _ = _ := by ring

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

lemma cavityWeightedKernel_split (N n : ℕ) (u K : ℕ → ℝ) :
    cavityWeightedKernel (N + n) u K = cavityWeightedKernel N u K +
      ∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j) := by
  simp only [cavityWeightedKernel, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd]

lemma cavityWeightedKernel_abs_le (N : ℕ) (u K : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) :
    |cavityWeightedKernel N u K| ≤ 4 :=
  cavity_weighted_kernel_abs_le (fun j : Fin N => u j) (fun j : Fin N => K j)
    (fun j => hu j) (fun j => hK j)

lemma cavityWeightedKernel_difference (N : ℕ) (u K L : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) {d : ℝ} (hd : 0 ≤ d)
    (hKL : ∀ j, |K j - L j| ≤ ((j : ℝ) + 1) * d) :
    |cavityWeightedKernel N u K - cavityWeightedKernel N u L| ≤ 4 * d := by
  have hu2 (j : ℕ) : u j ^ 2 ≤ 4 := by
    have hh := abs_le.mp (hu j)
    nlinarith
  rw [cavityWeightedKernel, cavityWeightedKernel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |perturbationWeight j ^ 2 * u j ^ 2 * K j -
        perturbationWeight j ^ 2 * u j ^ 2 * L j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, 4 * d * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      calc
        _ ≤ (perturbationWeight j ^ 2 * 4) * (((j : ℝ) + 1) * d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hu2 j) (sq_nonneg _)) (hKL j)
            (abs_nonneg _) (by positivity)
        _ = (4 * d * perturbationWeight j) * (((j : ℝ) + 1) * perturbationWeight j) := by ring
        _ ≤ (4 * d * perturbationWeight j) * 1 :=
          mul_le_mul_of_nonneg_left (perturbationWeight_linear_le j)
            (mul_nonneg (mul_nonneg (by norm_num) hd) (perturbationWeight_nonneg j))
        _ = _ := mul_one _
    _ = (4 * d) * (1 - (1 / 2 : ℝ) ^ N) := by
      rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ 4 * d := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

theorem cavityWeightedKernel_amplitude_difference (N n : ℕ) (u K L : ℕ → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (hK : ∀ j, |K j| ≤ 1) {d a b : ℝ}
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hKL : ∀ j, |K j - L j| ≤ ((j : ℝ) + 1) * d) :
    |b * cavityWeightedKernel (N + n) u K - a * cavityWeightedKernel N u L| ≤
      4 * |b - a| + 4 * a * d + 4 * b * (1 / 2 : ℝ) ^ N := by
  have hp := cavity_covariance_mass_difference (b := b) ha (cavityWeightedKernel_abs_le N u K hu hK)
    (cavityWeightedKernel_difference N u K L hu hd hKL)
  have ht := cavity_weighted_kernel_tail_le N n
    (fun j : Fin n => u (N + j)) (fun j : Fin n => K (N + j))
    (fun j => hu (N + j)) (fun j => hK (N + j))
  rw [cavityWeightedKernel_split]
  calc
    _ = |(b * cavityWeightedKernel N u K - a * cavityWeightedKernel N u L) +
        b * (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j))| :=
      by congr 1; ring
    _ ≤ |b * cavityWeightedKernel N u K - a * cavityWeightedKernel N u L| +
        |b * (∑ j : Fin n, perturbationWeight (N + j) ^ 2 * u (N + j) ^ 2 * K (N + j))| :=
      abs_add_le _ _
    _ ≤ (4 * |b - a| + a * (4 * d)) + b * (4 * (1 / 2 : ℝ) ^ N) := by
      rw [abs_mul, abs_of_nonneg hb]
      exact add_le_add hp (mul_le_mul_of_nonneg_left ht hb)
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualCovariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
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

lemma cavityPerturbationKernel_difference {N M m depth : ℕ}
    (U : Rotation N) (V : Rotation M)
    (I : Fin m → Finset (Fin N)) (J : Fin m → Finset (Fin M))
    (σ₁ σ₂ : Spin N) (τ₁ τ₂ : Spin M) (α β : LabeledLeaf depth)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ - projectedOverlap V (J a) τ₁ τ₂| ≤ δ)
    (j : ℕ) :
    |cavityPerturbationKernel U I (σ₁, α) (σ₂, β) j -
      cavityPerturbationKernel V J (τ₁, α) (τ₂, β) j| ≤ ((j : ℝ) + 1) * δ := by
  have ht : |treeOverlap depth α β| ≤ 1 := by
    rw [abs_of_nonneg (treeOverlap_mem depth α β).1]
    exact (treeOverlap_mem depth α β).2
  have h := cavity_spectral_tree_kernel_difference
    (fun a => projectedOverlap U (I a) σ₁ σ₂) (fun a => projectedOverlap V (J a) τ₁ τ₂)
    (enumeratedSpectralDegree m j) (enumeratedTreeDegree m j) (treeOverlap depth α β)
    (fun a => projectedOverlap_abs_le_one U (I a) σ₁ σ₂)
    (fun a => projectedOverlap_abs_le_one V (J a) τ₁ τ₂) ht herr
  exact h.trans (mul_le_mul_of_nonneg_right (enumeratedSpectralDegree_real_sum_le m j) hδ)

/-- The actual covariance error, including the additional monomials at
dimension N+n, is controlled by the same vanishing rate. -/
theorem cavity_actual_covariance_error {N n m depth : ℕ}
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (σ₁ σ₂ : Spin (N + n)) (τ₁ τ₂ : Spin N) (α β : LabeledLeaf depth)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ - projectedOverlap V (J a) τ₁ τ₂| ≤ δ) :
    |cylinderCross (cavityPerturbationCoefficients U I u depth (σ₁, α))
        (cavityPerturbationCoefficients U I u depth (σ₂, β)) -
      cylinderCross (cavityPerturbationCoefficients V J u depth (τ₁, α))
        (cavityPerturbationCoefficients V J u depth (τ₂, β))| ≤
      4 * |(N + n) * perturbationScale (N + n) ^ 2 - N * perturbationScale N ^ 2| +
        4 * (N * perturbationScale N ^ 2) * δ +
        4 * ((N + n) * perturbationScale (N + n) ^ 2) * (1 / 2 : ℝ) ^ N := by
  rw [cavityPerturbationCoefficients_cross, cavityPerturbationCoefficients_cross]
  have hh := cavityWeightedKernel_amplitude_difference (d := δ)
    (a := (N : ℝ) * perturbationScale N ^ 2)
    (b := ((N + n : ℕ) : ℝ) * perturbationScale (N + n) ^ 2) N n u
    (cavityPerturbationKernel U I (σ₁, α) (σ₂, β))
    (cavityPerturbationKernel V J (τ₁, α) (τ₂, β)) hu
    (cavityPerturbationKernel_abs_le U I _ _) hδ (by positivity) (by positivity)
    (cavityPerturbationKernel_difference U V I J σ₁ σ₂ τ₁ τ₂ α β hδ herr)
  simpa only [Nat.cast_add] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalPerturbation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic spectral-diagonal perturbation as an exact eigenvalue shift. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- This is the first term of the manuscript's perturbation, including
its coefficient `N e_N`, in the actual rotated Ising Hamiltonian. -/
theorem rotatedEnergy_diagonalPerturbation {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ =
      t * rotatedEnergy eig U σ + N * perturbationScale N * ∑ a, v a * projectedOverlap U (I a) σ σ := by
  classical
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold rotatedEnergy diagonalPerturbedEigenvalues projectedOverlap
  simp_rw [add_mul, Finset.sum_add_distrib]
  have he : (∑ i, (2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0) *
      U (spinVector σ) i ^ 2) =
      2 * perturbationScale N * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    calc
      _ = (2 * perturbationScale N) *
          ∑ i, ∑ a, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = (2 * perturbationScale N) *
          ∑ a, ∑ i, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [he]
  simp_rw [← pow_two]
  have hl : (∑ i, t * eig i * U (spinVector σ) i ^ 2) =
      t * ∑ i, eig i * U (spinVector σ) i ^ 2 := by
    simp only [Finset.mul_sum, mul_assoc]
  have hs : (∑ a, v a * ((N : ℝ)⁻¹ * ∑ i ∈ I a, U (spinVector σ) i ^ 2)) =
      (N : ℝ)⁻¹ * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hl, hs]
  field_simp [hn]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualDiagonal
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The deterministic perturbation error under a fixed cavity-size
jump, stated for the actual spectral-diagonal perturbation energy. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_weighted_overlap_sum_abs {m : ℕ} (v q : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (hq : ∀ a, |q a| ≤ 1) :
    |∑ a, v a * q a| ≤ 2 * m := by
  calc
    _ ≤ ∑ a, |v a * q a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact (mul_le_mul (hv a) (hq a) (abs_nonneg _) (by norm_num)).trans_eq (mul_one 2)
    _ = _ := by simp <;> ring

lemma cavity_weighted_overlap_sum_difference {m : ℕ} (v q r : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) {δ : ℝ} (herr : ∀ a, |q a - r a| ≤ δ) :
    |(∑ a, v a * q a) - ∑ a, v a * r a| ≤ 2 * m * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |v a * q a - v a * r a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin m, 2 * δ := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hv a) (herr a) (abs_nonneg _) (by norm_num)
    _ = _ := by simp <;> ring

theorem cavity_diagonal_perturbation_error {N n m : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (σ : Spin (N + n)) (τ : Spin N)
    {δ : ℝ}
    (herr : ∀ a, |projectedOverlap U (I a) σ σ - projectedOverlap V (J a) τ τ| ≤ δ) :
    |(rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ - t * rotatedEnergy eig U σ) -
      (rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V τ - t * rotatedEnergy eig₀ V τ)| ≤
      2 * m * |(N + n) * perturbationScale (N + n) - N * perturbationScale N| +
        2 * m * (N * perturbationScale N) * δ := by
  rw [rotatedEnergy_diagonalPerturbation (by omega : 0 < N + n),
    rotatedEnergy_diagonalPerturbation hN, add_sub_cancel_left, add_sub_cancel_left]
  let P := ∑ a, v a * projectedOverlap U (I a) σ σ
  let Q := ∑ a, v a * projectedOverlap V (J a) τ τ
  have hP : |P| ≤ 2 * m := cavity_weighted_overlap_sum_abs v _ hv
    (fun a => projectedOverlap_abs_le_one U (I a) σ σ)
  have hPQ : |P - Q| ≤ 2 * m * δ := cavity_weighted_overlap_sum_difference v _ _ hv herr
  have ha : 0 ≤ (N : ℝ) * perturbationScale N := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ = |(((N + n) * perturbationScale (N + n) - N * perturbationScale N) * P) +
        (N * perturbationScale N) * (P - Q)| := by congr 1; dsimp [P, Q]; push_cast; ring
    _ ≤ |((N + n) * perturbationScale (N + n) - N * perturbationScale N) * P| +
        |(N * perturbationScale N) * (P - Q)| := abs_add_le _ _
    _ ≤ |(N + n) * perturbationScale (N + n) - N * perturbationScale N| * (2 * m) +
        (N * perturbationScale N) * (2 * m * δ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ ha)
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityActualErrorRates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite perturbations satisfy the configuration-dependent
cavity error bounds with coefficients tending to zero. -/

noncomputable section
open IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem cavity_actual_covariance_rate {N n m depth : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (σ₁ σ₂ : Spin (N + n)) (τ₁ τ₂ : Spin N) (α β : LabeledLeaf depth)
    {C w : ℝ} (hC : 0 ≤ C) (hw : 1 ≤ w)
    (herr : ∀ a, |projectedOverlap U (I a) σ₁ σ₂ -
      projectedOverlap V (J a) τ₁ τ₂| ≤ C / N * w) :
    |cylinderCross (cavityPerturbationCoefficients U I u depth (σ₁, α))
        (cavityPerturbationCoefficients U I u depth (σ₂, β)) -
      cylinderCross (cavityPerturbationCoefficients V J u depth (τ₁, α))
        (cavityPerturbationCoefficients V J u depth (τ₂, β))| ≤
      cavityCovarianceRate n C N * w := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := cavity_actual_covariance_error U V I J u hu σ₁ σ₂ τ₁ τ₂ α β
    (show 0 ≤ C / N * w by positivity) herr
  have he : 4 * ((N : ℝ) * perturbationScale N ^ 2) * (C / N * w) =
      (4 * C * perturbationScale N ^ 2) * w := by field_simp
  rw [he] at h
  refine h.trans ?_
  unfold cavityCovarianceRate
  have ha : 0 ≤ 4 * |((N : ℝ) + n) * perturbationScale (N + n) ^ 2 -
      N * perturbationScale N ^ 2| := by positivity
  have hb : 0 ≤ 4 * (((N : ℝ) + n) * perturbationScale (N + n) ^ 2) *
      (1 / 2 : ℝ) ^ N := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hw ha
  have h₂ := mul_le_mul_of_nonneg_left hw hb
  nlinarith

theorem cavity_actual_diagonal_rate {N n m : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (σ : Spin (N + n)) (τ : Spin N)
    {C w : ℝ} (hw : 1 ≤ w)
    (herr : ∀ a, |projectedOverlap U (I a) σ σ -
      projectedOverlap V (J a) τ τ| ≤ C / N * w) :
    |(rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ - t * rotatedEnergy eig U σ) -
      (rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V τ - t * rotatedEnergy eig₀ V τ)| ≤
      cavityDeterministicRate n m C N * w := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := cavity_diagonal_perturbation_error hN U V I J eig eig₀ v hv t σ τ herr
  have he : 2 * m * ((N : ℝ) * perturbationScale N) * (C / N * w) =
      (2 * m * C * perturbationScale N) * w := by field_simp
  rw [he] at h
  refine h.trans ?_
  unfold cavityDeterministicRate
  have ha : 0 ≤ 2 * (m : ℝ) * |((N : ℝ) + n) * perturbationScale (N + n) -
      N * perturbationScale N| := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hw ha
  nlinarith

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
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityPerturbationComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic and Gaussian perturbation errors are absorbed by the
same nonuniform cavity penalty on the countable spin/leaf prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_log_mean_mono {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (hJ : Integrable (fun x => Real.exp (J x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B)
    (hle : ∀ x, H x ≤ J x) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hiH := (cylinder_log_partition_memLp_two ν H hH A hA 1).integrable (by norm_num)
  have hiJ := (cylinder_log_partition_memLp_two ν J hJ A hA 1).integrable (by norm_num)
  simp only [one_mul] at hiH hiJ
  apply integral_mono_ae hiH hiJ
  filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA,
    cylinder_partition_exp_integrable_ae ν J hJ A hA] with g hgH hgJ
  have h := logMean_mono ν (b := 1)
    (F := fun x => H x + cylinderField (A x) g)
    (G := fun x => J x + cylinderField (A x) g) (by norm_num)
    (by simpa only [one_mul] using hgH) (by simpa only [one_mul] using hgJ)
    (fun x => add_le_add (hle x) le_rfl)
  simpa only [logMean, div_one, one_mul] using h

lemma cavity_bounded_sub_mul {X : Type*} (H V : X → ℝ) (k : ℝ)
    {M D : ℝ} (hH : ∀ x, |H x| ≤ M) (hV : ∀ x, |V x| ≤ D) :
    ∀ x, |H x - k * V x| ≤ M + |k| * D := by
  intro x
  exact (abs_sub _ _).trans (by
    rw [abs_mul]
    exact add_le_add (hH x) (mul_le_mul_of_nonneg_left (hV x) (abs_nonneg _)))

theorem cavity_countable_perturbation_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H J V : X → ℝ) (c d : ℝ)
    {M₀ M₁ D : ℝ} (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (hV : ∀ x, |V x| ≤ D) (hE : ∀ x, |J x - H x| ≤ d * V x)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log
      (∫ x, Real.exp (H x - (d + 2 * c) * V x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hm := cylinder_log_mean_mono ν (fun x => H x - (d + 2 * c) * V x)
    (fun x => J x - 2 * c * V x)
    (cavity_bounded_base_exp_integrable ν _ (cavity_bounded_sub_mul H V _ hH hV))
    (cavity_bounded_base_exp_integrable ν _ (cavity_bounded_sub_mul J V _ hJ hV))
    C hC (fun x => by linarith [(abs_le.mp (hE x)).1])
  exact hm.trans (countable_cylinder_covariance_penalty_comparison ν J V c hJ hV C A hC hA hK)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityIncrementComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cavity increment after absorbing deterministic and
Gaussian covariance errors. The base Gaussian field stays inside the
Gibbs measure in the factor on the right. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_log_tilt_factor {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (hHW : Integrable (fun x => Real.exp (H x + W x)) ν) :
    Real.log (∫ x, Real.exp (W x) ∂ν.tilted H) =
      Real.log (∫ x, Real.exp (H x + W x) ∂ν) - Real.log (∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  exact Real.log_div (integral_exp_pos hHW).ne' (integral_exp_pos hH).ne' 

lemma cavity_mean_log_tilt_factor {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H W : X → ℝ) {M L : ℝ} (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L)
    (C : X → ℕ →₀ ℝ) {B : ℝ} (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) g)) ∂gaussianCoordinates) =
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + W x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates := by
  have hHW : ∀ x, |H x + W x| ≤ M + L := fun x =>
    (abs_add_le _ _).trans (add_le_add (hH x) (hW x))
  have hiH := cavity_bounded_base_exp_integrable ν H hH
  have hiHW := cavity_bounded_base_exp_integrable ν (fun x => H x + W x) hHW
  have hpH := (cylinder_log_partition_memLp_two ν H hiH C hC 1).integrable (by norm_num)
  have hpHW := (cylinder_log_partition_memLp_two ν (fun x => H x + W x) hiHW C hC 1).integrable
    (by norm_num)
  simp only [one_mul] at hpH hpHW
  rw [← integral_sub hpHW hpH]
  apply integral_congr_ae
  filter_upwards [cylinder_partition_exp_integrable_ae ν H hiH C hC,
    cylinder_partition_exp_integrable_ae ν (fun x => H x + W x) hiHW C hC] with g hg hgW
  have he (x : X) : H x + W x + cylinderField (C x) g =
      (H x + cylinderField (C x) g) + W x := by ring
  simp_rw [he] at hgW ⊢
  exact cavity_log_tilt_factor ν _ W hg hgW

/-- The actual increment estimate used before passing to cavity limits.
All error bounds concern the conditioned finite-size energies and
covariances; no lower-bound conclusion is assumed. -/
theorem cavity_log_increment_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W J V : X → ℝ) (c d : ℝ)
    {M L M₁ D B₀ B₁ : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L) (hJ : ∀ x, |J x| ≤ M₁)
    (hV : ∀ x, |V x| ≤ D) (hE : ∀ x, |J x - (H x + W x)| ≤ d * V x)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (W x - (d + 2 * c) * V x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) g)) ∂gaussianCoordinates) ≤
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates := by
  have hHW : ∀ x, |H x + W x| ≤ M + L := fun x =>
    (abs_add_le _ _).trans (add_le_add (hH x) (hW x))
  rw [cavity_mean_log_tilt_factor ν H (fun x => W x - (d + 2 * c) * V x) hH
    (cavity_bounded_sub_mul W V (d + 2 * c) hW hV) C hC]
  have ht := cavity_countable_perturbation_comparison ν (fun x => H x + W x) J V c d
    hHW hJ hV hE C A hC hA hK
  have he (x : X) : H x + (W x - (d + 2 * c) * V x) = H x + W x - (d + 2 * c) * V x := by ring
  simp_rw [he]
  exact sub_le_sub_right ht _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityVanishingPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic error in the geometric cavity increment disappears
after taking the expected logarithm of a capped partition function. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_abs_min_cap {h T : ℝ} (hT : 0 ≤ T) : |min h T| ≤ |h| := by
  by_cases hh : h ≤ T
  · rw [min_eq_left hh]
  · rw [min_eq_right (le_of_not_ge hh), abs_of_nonneg hT,
      abs_of_nonneg (hT.trans (le_of_not_ge hh))]
    exact le_of_not_ge hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityCappedIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic cap preserves the one-sided finite cavity increment
inequality.  The base Gaussian perturbation remains inside the Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_mean_log_tilt_cap_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H W R : X → ℝ) {M L D T : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L)
    (hR : ∀ x, |R x| ≤ D) (hT : 0 ≤ T) (δ : ℝ)
    (C : X → ℕ →₀ ℝ) {B : ℝ} (hC : ∀ x, (C x).sum (fun _ z => z^2) ≤ B) :
    (∫ z, Real.log (∫ x, Real.exp (min (W x) T - δ * R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates) ≤
    ∫ z, Real.log (∫ x, Real.exp (W x - δ * R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates := by
  have hcap x : |min (W x) T| ≤ L := (cavity_abs_min_cap hT).trans (hW x)
  have hpen := cavity_bounded_sub_mul W R δ hW hR
  have hcp := cavity_bounded_sub_mul (fun x => min (W x) T) R δ hcap hR
  rw [cavity_mean_log_tilt_factor ν H _ hH hcp C hC,
    cavity_mean_log_tilt_factor ν H _ hH hpen C hC]
  apply sub_le_sub_right
  apply cylinder_log_mean_mono ν _ _
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      (abs_add_le _ _).trans (add_le_add (hH x) (hcp x))))
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      (abs_add_le _ _).trans (add_le_add (hH x) (hpen x)))) C hC
  intro x
  linarith [min_le_left (W x) T]

theorem cavity_capped_log_increment_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W J R : X → ℝ) (c d : ℝ)
    {M L M₁ D B₀ B₁ T : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L) (hJ : ∀ x, |J x| ≤ M₁)
    (hR : ∀ x, |R x| ≤ D) (hT : 0 ≤ T)
    (hE : ∀ x, |J x - (H x + W x)| ≤ d * R x)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z^2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z^2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (R x + R y)) :
    (∫ z, Real.log (∫ x, Real.exp (min (W x) T - (d+2*c)*R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates) ≤
    (∫ z, Real.log (∫ x, Real.exp (J x+cylinderField (A x) z) ∂ν)
      ∂gaussianCoordinates) -
      ∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (C x) z) ∂ν)
        ∂gaussianCoordinates := by
  exact (cavity_mean_log_tilt_cap_le ν H W R hH hW hR hT (d+2*c) C hC).trans
    (cavity_log_increment_comparison ν H W J R c d hH hW hJ hR hE C A hC hA hK)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteCappedIncrement
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The capped finite increment for the actual Ising energies and tensor
perturbations, retaining the full base Gaussian Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

/-- Conditional on the coupled spectral geometry, the actual finite
perturbations cost a vanishing coefficient times the special-coordinate
penalty. The Gaussian perturbation stays inside the base Gibbs law. -/
theorem cavity_finite_capped_energy_increment_oai {N n m depth : ℕ} (hN : 0 < N)
    (U : Rotation (N + n)) (V : Rotation N)
    (I : Fin m → Finset (Fin (N + n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N + n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap)
    (ν : Measure ((Spin N × Spin n) × LabeledLeaf depth)) [IsProbabilityMeasure ν]
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y)) :
    let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1.1
    let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
    let F := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.1)
    let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.1, x.2)
    let B := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      cavityPerturbationCoefficients V J u depth (x.1.1, x.2)
    let δ := cavityDeterministicRate n m (2 * C) N + 2 * cavityCovarianceRate n C N
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (min (W x) cap - δ * w x.1)
      ∂ν.tilted (fun x => H x + cylinderField (B x) g)) ∂gaussianCoordinates) ≤
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (F x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (B x) g) ∂ν)
        ∂gaussianCoordinates := by
  dsimp only
  let H₀ := fun x : Spin N × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1
  let W₀ := fun x : Spin N × Spin n =>
    t * (rotatedEnergy eig U (cavityJoinedSpin x) - rotatedEnergy eig₀ V x.1)
  let F₀ := fun x : Spin N × Spin n =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x => |H₀ x|)
  obtain ⟨L, hL⟩ := Finite.exists_le (fun x => |W₀ x|)
  obtain ⟨M₁, hM₁⟩ := Finite.exists_le (fun x => |F₀ x|)
  obtain ⟨D, hD⟩ := Finite.exists_le (fun x => |w x|)
  apply cavity_capped_log_increment_comparison ν
    (fun x => H₀ x.1) (fun x => W₀ x.1) (fun x => F₀ x.1) (fun x => w x.1)
    (cavityCovarianceRate n C N) (cavityDeterministicRate n m (2 * C) N)
    (fun x => hM x.1) (fun x => hL x.1) (fun x => hM₁ x.1) (fun x => hD x.1) hcap
  · intro x
    have hh := cavity_actual_diagonal_rate hN U V I J eig eig₀ v hv t
      (cavityJoinedSpin x.1) x.1.1 (hw x.1) (C := 2 * C) (fun a => by
        have ha := herr x.1 x.1 a
        convert ha using 1; ring)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [H₀, W₀, F₀]; congr 1; ring)
  · intro x
    exact cavityPerturbationCoefficients_sq_le V J u hu (x.1.1, x.2)
  · intro x
    exact cavityPerturbationCoefficients_sq_le U I u hu (cavityJoinedSpin x.1, x.2)
  · intro x y
    exact cavity_actual_covariance_rate hN U V I J u hu
      (cavityJoinedSpin x.1) (cavityJoinedSpin y.1) x.1.1 y.1.1 x.2 y.2 hC
      (by linarith [hw x.1, hw y.1]) (herr x.1 y.1)

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.cavity_finite_capped_energy_increment_oai := @OAI.InvariantIsing.cavity_finite_capped_energy_increment_oai
