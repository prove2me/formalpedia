-- Prove2me | solution 1 for OAI.InvariantIsing.priorNamespacedPerturbation_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:03:33.510727+00:00
-- url     : https://prove2.me/submissions/3d572790-0c57-4cb5-a9bb-29bba5c5395e

import Mathlib
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
/-- d13f23b's `HasLaw.memLp_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.MemLp (f ∘ X) p P := by
  have h : MeasureTheory.MemLp f p (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h
/-- d13f23b's `HasLaw.memLp`: a variable whose law has `id` in `L^p` is in `L^p`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure E} {X : Ω → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hμ : MeasureTheory.MemLp id p μ) :
    MeasureTheory.MemLp X p P := hX.memLp_comp hμ
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

lemma cylinder_variance_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    a.sum (fun _ c => c^2) = ∑ i : Fin n, (a i)^2 := by
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (a i)^2) n).symm

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

theorem variance_of_conditional_center {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : ℝ}
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ C+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply Integrable.of_bound (hd.pow 2).integral_prod_right' C
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    ((integrable_const C).add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hX.integrable_sq,integral_const,
    probReal_univ,one_smul] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

end IsingPerceptron

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
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

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

lemma tensorPerturbationAmplitude_square_sum_le (N : ℕ) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) :
    (∑ j : Fin N, tensorPerturbationAmplitude N u j ^ 2) ≤ 4 * N * perturbationScale N ^ 2 := by
  calc
    _ ≤ ∑ j : Fin N, (4 * N * perturbationScale N ^ 2) * perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hw : perturbationWeight j ^ 2 ≤ perturbationWeight j := by
        nlinarith [perturbationWeight_nonneg j, perturbationWeight_le_one j]
      exact (tensorPerturbationAmplitude_sq_le N u hu j).trans
        (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = (4 * N * perturbationScale N ^ 2) * (1 - (1 / 2 : ℝ) ^ N) := by
      rw [← Finset.mul_sum, perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N])

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Nat.succ_le_of_lt hN)
  · norm_num

lemma perturbationScale_sq_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ^ 2 ≤ 1 := by
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [perturbationScale_le_one hN]

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureLipschitz
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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

lemma abs_rotatedEnergy_sub_rotation_le {N : ℕ} (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (K : ℝ) (hK : 0 ≤ K)
    (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ| ≤
      K * N * frobeniusDistance U V := by
  let x := specialRotation U (spinVector σ)
  let y := specialRotation V (spinVector σ)
  let d := frobeniusDistance U V
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hx : ∑ i, x i ^ 2 = N := rotated_spin_sq_sum _ _
  have hy : ∑ i, y i ^ 2 = N := rotated_spin_sq_sum _ _
  have hm : (∑ i, (x i - y i) ^ 2) ≤ (N : ℝ) * d ^ 2 :=
    specialRotation_spin_dist_sq_le U V σ
  have hp : (∑ i, (x i + y i) ^ 2) ≤ 4 * (N : ℝ) := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (x i + y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2 by
        nlinarith [sq_nonneg (x i - y i)])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy] at hi
    linarith
  have hw : (∑ i, (eig i * (x i - y i)) ^ 2) ≤
      K ^ 2 * ∑ i, (x i - y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    have hb : eig i ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (heig i)
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => eig i * (x i - y i)) (fun i => x i + y i)
  have hs : (∑ i, (eig i * (x i - y i)) * (x i + y i)) ^ 2 ≤
      (2 * K * (N : ℝ) * d) ^ 2 := by
    calc
      _ ≤ (∑ i, (eig i * (x i - y i)) ^ 2) * ∑ i, (x i + y i) ^ 2 := hcs
      _ ≤ (K ^ 2 * ∑ i, (x i - y i) ^ 2) * (4 * (N : ℝ)) :=
        mul_le_mul hw hp (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ ≤ (K ^ 2 * ((N : ℝ) * d ^ 2)) * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
          (by positivity)
      _ = _ := by ring
  have ha : |∑ i, (eig i * (x i - y i)) * (x i + y i)| ≤
      2 * K * (N : ℝ) * d := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  have he : rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ =
      (1 / 2 : ℝ) * ∑ i, (eig i * (x i - y i)) * (x i + y i) := by
    rw [rotatedEnergy, rotatedEnergy, ← mul_sub, ← Finset.sum_sub_distrib]
    change (1 / 2 : ℝ) * (∑ i, (eig i * x i ^ 2 - eig i * y i ^ 2)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_eq (by dsimp [d] <;> ring)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapBounds
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteGaussianVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Gaussian cutoff partition functions in the Euclidean norm. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal InnerProductSpace

namespace InvariantIsing

theorem finiteGaussianLogPartition_lipschitz {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (hA : ∀ x, ‖A x‖ ≤ L) :
    LipschitzWith L (finiteGaussianLogPartition ν H A) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  have hb (x : X) : |(H x + ⟪A x, g⟫_ℝ) - (H x + ⟪A x, h⟫_ℝ)| ≤
      (L : ℝ) * ‖g - h‖ := by
    rw [add_sub_add_left_eq_sub, ← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
  have hcomp := logMean_abs_sub_le ν (by norm_num : (0 : ℝ) < 1)
    (show Integrable (fun x => Real.exp (1 * (H x + ⟪A x, g⟫_ℝ))) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1 * (H x + ⟪A x, h⟫_ℝ))) ν from Integrable.of_finite) hb
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, logMean, one_mul, div_one,
    finiteGaussianLogPartition] using hcomp

/-- The Gaussian Poincaré inequality bounds the finite-cutoff
log partition variance by the coefficient squared norm,
uniformly in the cutoff and base energy. -/
theorem finiteGaussianLogPartition_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (B : ℝ≥0)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ B) :
    variance (finiteGaussianLogPartition ν H A)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ B := by
  have hs : ((NNReal.sqrt B : ℝ≥0) : ℝ) ^ 2 = B := by exact_mod_cast NNReal.sq_sqrt B
  have hnorm (x : X) : ‖A x‖ ≤ ((NNReal.sqrt B : ℝ≥0) : ℝ) := by
    have hn := NNReal.coe_nonneg (NNReal.sqrt B)
    nlinarith [hA x, norm_nonneg (A x)]
  exact (hpub d (NNReal.sqrt B) _
    (finiteGaussianLogPartition_lipschitz ν H A (NNReal.sqrt B) hnorm)).trans_eq hs

/-- Finite-state countable-cylinder restriction. A finite family of finitely supported coefficients uses a common
finite prefix, whose Gaussian law is the standard Euclidean Gaussian. -/
theorem finite_cylinder_cgf_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ t ^ 2 * B := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound A
  have hs (x : X) : ∀ j ∈ (A x).support, j < n + 1 :=
    fun j hj => hn x j (Finsupp.mem_support_iff.mp hj)
  let V : X → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => WithLp.toLp 2 (fun j : Fin (n + 1) => t * A x j)
  let B' : ℝ≥0 := ⟨t ^ 2 * B, mul_nonneg (sq_nonneg t) hB⟩
  have hv (x : X) : ‖V x‖ ^ 2 ≤ B' := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [V, mul_pow, ← Finset.mul_sum,
      ← cylinder_variance_prefix (A x) (hs x)]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)
  let F := finiteGaussianLogPartition ν (fun _ => 0) V
  have hF : Measurable F := by
    have hsqrt : (((NNReal.sqrt B' : ℝ≥0) : ℝ)) ^ 2 = B' :=
      by exact_mod_cast NNReal.sq_sqrt B'
    have hnorm (x : X) : ‖V x‖ ≤ ((NNReal.sqrt B' : ℝ≥0) : ℝ) := by
      have hn' := NNReal.coe_nonneg (NNReal.sqrt B')
      nlinarith [hv x, norm_nonneg (V x)]
    exact (finiteGaussianLogPartition_lipschitz ν (fun _ => 0) V (NNReal.sqrt B') hnorm).continuous.measurable
  have hto : MeasurePreserving
      (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hmp := hto.comp (gaussian_prefix_measurePreserving (n + 1))
  have he : (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t) =
      F ∘ ((WithLp.toLp 2) ∘ (fun g : ℕ → ℝ => fun j : Fin (n + 1) => g j)) := by
    funext g
    have hi (x : X) : ⟪V x, WithLp.toLp 2 (fun j : Fin (n + 1) => g j)⟫_ℝ =
        t * cylinderField (A x) g := by
      rw [cylinderField_eq_prefix (A x) (hs x)]
      simp only [V, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [Function.comp_apply, F, finiteGaussianLogPartition, cgf, mgf, zero_add, hi]
  rw [he]
  change variance (fun g => F ((WithLp.toLp 2 ∘
    (fun g : ℕ → ℝ => fun j : Fin (n + 1) => g j)) g)) gaussianCoordinates ≤ _
  rw [hmp.variance_fun_comp hF.aemeasurable]
  exact finiteGaussianLogPartition_variance_le hpub ν (fun _ => 0) V B' hv

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_VarianceLimit
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the Gaussian variance bound from finite leaf cutoffs to their limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace InvariantIsing

/-- Fatou's lemma for centered squares. This permits finite-leaf Gaussian
variance estimates to pass to the countable cascade prior. -/
theorem variance_le_of_ae_tendsto_of_mean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hm : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)))
    (hv : ∀ n, variance (f n) μ ≤ C) : variance g μ ≤ C := by
  let F := fun n ω => (f n ω - ∫ z, f n z ∂μ) ^ 2
  let G := fun ω => (g ω - ∫ z, g z ∂μ) ^ 2
  have hFi (n : ℕ) : Integrable (F n) μ :=
    ((hf n).sub (memLp_const _)).integrable_sq
  have hGi : Integrable G μ := (hg.sub (memLp_const _)).integrable_sq
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop (𝓝 (ENNReal.ofReal (G ω))) := by
    filter_upwards [ht] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hω.sub hm).pow 2)
  have hfatou : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hω => hω.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun n => (hFi n).aemeasurable.ennreal_ofReal)
  have hpoint (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ fun _ => sq_nonneg _)]
    change ENNReal.ofReal (∫ ω, (f n ω - ∫ z, f n z ∂μ) ^ 2 ∂μ) ≤ _
    rw [← variance_eq_integral (hf n).aemeasurable]
    exact ENNReal.ofReal_le_ofReal (hv n)
  have hb : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hpoint n)
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ fun _ => sq_nonneg _)] at hfatou
  change ENNReal.ofReal (∫ ω, (g ω - ∫ z, g z ∂μ) ^ 2 ∂μ) ≤ _ at hfatou
  rw [← variance_eq_integral hg.aemeasurable] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff ((variance_nonneg (f 0) μ).trans (hv 0))).mp (hfatou.trans hb)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_CountableGaussianVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variance estimate passes from finite positive-mass leaf cutoffs to the
actual countable spin/cascade-leaf prior. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology NNReal

namespace InvariantIsing

theorem cylinder_cgf_variance_le_of_finite_restrictions {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    {B C : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ)
    (hfinite : ∀ S : Set X, S.Finite → ν S ≠ 0 →
      variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g)
        (normalizedRestriction ν S) t) gaussianCoordinates ≤ C) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ C := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  let νn := fun n => normalizedRestriction ν (S n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
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
  let f := fun n g => Real.log (∫ x, Real.exp (H (g, x)) ∂νn n)
  let F := fun g => Real.log (∫ x, Real.exp (H (g, x)) ∂ν)
  have hfm (n : ℕ) : Measurable (f n) :=
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hFm : Measurable F := hH.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hf (n : ℕ) : MemLp (f n) 2 gaussianCoordinates :=
    (memLp_two_iff_integrable_sq (hfm n).aestronglyMeasurable).mpr
      (gaussian_log_partition_second (ν := νn n) hH hLaw hVar).1
  have hF : MemLp F 2 gaussianCoordinates :=
    (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr
      (gaussian_log_partition_second (ν := ν) hH hLaw hVar).1
  have hm : Tendsto (fun n => ∫ g, f n g ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, F g ∂gaussianCoordinates)) :=
    gaussian_log_restriction_expectation_tendsto hH hLaw hVar
      (fun n => (hS n).measurableSet) hExh hpos
  have he := (gaussian_field_exp_integrable (ν := ν) hH hLaw hVar 1).1
  simp only [one_mul] at he
  have ht : ∀ᵐ g ∂gaussianCoordinates, Tendsto (fun n => f n g) atTop (𝓝 (F g)) := by
    filter_upwards [he.prod_right_ae] with g hg
    have hz : 0 < ∫ x, Real.exp (H (g, x)) ∂ν := MeasureTheory.integral_exp_pos hg
    exact (Real.continuousAt_log hz.ne').tendsto.comp
      (normalized_restriction_integral_tendsto (fun n => (hS n).measurableSet) hExh hg)
  have hv (n : ℕ) : variance (f n) gaussianCoordinates ≤ C :=
    hfinite (S n) (hS n) (hpos n)
  exact variance_le_of_ae_tendsto_of_mean_tendsto hf hF ht hm hv

/-- The countable spin/leaf Gaussian log partition inherits the uniform
coefficient variance bound from the finite-dimensional Gaussian
Poincaré inequality. -/
theorem countable_cylinder_cgf_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ t ^ 2 * B := by
  apply cylinder_cgf_variance_le_of_finite_restrictions ν A hA t
  intro S hS hpos
  let := hS.fintype
  have : IsProbabilityMeasure (subtypeReference ν S) :=
    subtypeReference_probability ν hS.measurableSet hpos
  have h := finite_cylinder_cgf_variance_le hpub (subtypeReference ν S)
    (fun x : S => A x) B hB (fun x => hA x) t
  have he (g : ℕ → ℝ) :
      cgf (fun x : S => cylinderField (A x) g) (subtypeReference ν S) t =
        cgf (fun x => cylinderField (A x) g) (normalizedRestriction ν S) t := by
    unfold cgf mgf
    congr 1
    exact (subtypeReference_preserving ν hS.measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (t * cylinderField (A x) g))).aestronglyMeasurable
  simpa only [he] using h

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

/-- The actual countable Gaussian partition with arbitrary integrable base
energy has the same coefficient variance bound. This is conditional only on
the specified published Gaussian Poincaré consequence. -/
theorem countable_cylinder_log_partition_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    variance (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (H x + t * cylinderField (A x) g) ∂ν)) gaussianCoordinates ≤ t ^ 2 * B := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have he := cylinder_log_partition_base ν H hH A hA t
  rw [variance_congr he, variance_const_add (cylinder_cgf_memLp_two (ν.tilted H) A hA t).aestronglyMeasurable]
  exact countable_cylinder_cgf_variance_le hpub (ν.tilted H) A B hB hA t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorProfiles
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

/-- The sum over all tree levels contributes no extra factor of depth
to the Gaussian rotation modulus. -/
lemma tensorPathProfile_rotation_cap {m k : ℕ} (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (n : ℕ) (treeDegree : Fin k → ℕ) :
    (∑ i : Fin (n + 1), ∑ j, (varianceIncrement (monomialPath n (treeDegree j)) i : ℝ) *
      amplitude j ^ 2 * ∑ a, (degree j a : ℝ)) ≤
      ∑ j, amplitude j ^ 2 * ∑ a, (degree j a : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (treeDegree j))
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))).trans_eq (one_mul _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozen
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

/-- Injective Gaussian reindexing identifies the entire countable
spin/leaf field law with the flat tensor model. -/
theorem tensorNamespacedFields_law {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) := by
  let Φ := fun (G : TensorGaussianKey I degree → ℝ) (x : Spin N × LabeledLeaf n) =>
    ∑ i : Fin (n + 1), ∑ a : SpinTensorIndex I degree,
      (NNReal.sqrt (v i a) : ℝ) * spinTensorFeature U I degree amplitude x.1 a *
        G (i, (labeledAddress n x.2).take i, a)
  have hmΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro x
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun a _ =>
      (measurable_pi_apply (i.1, (labeledAddress n x.2).take i, a)).const_mul _
  have he : (fun g x => cylinderField (tensorLeafCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q : TensorGaussianKey I degree => g (Encodable.encode q)) := by
    funext g x
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hn : (fun g x => cylinderField (tensorNamespacedCoefficients U I degree amplitude n v x) g) =
      Φ ∘ (fun g : ℕ → ℝ => fun q => g (tensorNamespaceTag I degree q)) := by
    funext g x
    rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  have hp := gaussian_pullback_measurePreserving
    (Encodable.encode : TensorGaussianKey I degree → ℕ) Encodable.encode_injective
  have hq := gaussian_pullback_measurePreserving
    (tensorNamespaceTag I degree) (tensorNamespaceTag_injective I degree)
  rw [he, hn, ← Measure.map_map hmΦ hp.measurable, ← Measure.map_map hmΦ hq.measurable,
    hp.map_eq, hq.map_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar contribution to the enriched pressure variance. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace InvariantIsing

/-- Integrating the Gaussian tail of a deviation gives its second moment.
The proof applies layer cake to the squared deviation, so only the elementary
exponential integral on the positive half-line is needed. -/
lemma integral_sq_sub_le_of_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    Integrable (fun ω => (f ω - m) ^ 2) μ ∧
      (∫ ω, (f ω - m) ^ 2 ∂μ) ≤ C / a := by
  let g := fun ω => (f ω - m) ^ 2
  have hgm : Measurable g := (hf.sub_const m).pow_const 2
  have hgn : ∀ ω, 0 ≤ g ω := fun ω => sq_nonneg _
  have hk : Integrable (fun t : ℝ => C * Real.exp (-a * t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).const_mul C
  have hkn : ∀ t : ℝ, 0 ≤ C * Real.exp (-a * t) := fun _ => mul_nonneg hC (Real.exp_pos _).le
  have hki : (∫ t : ℝ in Ioi 0, C * Real.exp (-a * t)) = C / a := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -a < 0) 0]
    simp [div_eq_mul_inv]
  have hlin : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (C / a) := by
    calc
      _ = ∫⁻ t : ℝ in Ioi 0, μ {ω | t ≤ g ω} :=
        lintegral_eq_lintegral_meas_le μ (ae_of_all _ hgn) hgm.aemeasurable
      _ ≤ ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (C * Real.exp (-a * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have he : {ω | t ≤ g ω} = {ω | Real.sqrt t ≤ |f ω - m|} := by
          ext ω
          simp only [mem_ofPred_eq, g, Real.sqrt_le_left (abs_nonneg _), sq_abs]
        rw [he, ← ofReal_measureReal]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.sq_sqrt ht.le] using htail (Real.sqrt t) (Real.sqrt_pos.mpr ht)
      _ = ENNReal.ofReal (C / a) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ hkn), hki]
  have hgi : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (ae_of_all _ hgn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hgi, ?_⟩
  have hI : ENNReal.ofReal (∫ ω, g ω ∂μ) ≤ ENNReal.ofReal (C / a) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn)]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C / a)).mp hI

lemma variance_le_of_gaussian_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (m C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (htail : ∀ r : ℝ, 0 < r →
      μ.real {ω | r ≤ |f ω - m|} ≤ C * Real.exp (-a * r ^ 2)) :
    variance f μ ≤ C / a := by
  rw [← variance_sub_const hf.aestronglyMeasurable m]
  exact (variance_le_expectation_sq (hf.sub_const m).aestronglyMeasurable).trans
    (integral_sq_sub_le_of_gaussian_tail μ f hf m C a hC ha htail).2

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGaussianMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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
theorem tensorLeafGaussianMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
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

lemma finite_spin_base_exp_integrable {N n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] (H : Spin N → ℝ) :
    Integrable (fun x : Spin N × LabeledLeaf n => Real.exp (H x.1)) ν := by
  classical
  apply (integrable_const (∑ σ : Spin N, Real.exp (H σ))).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Finset.single_le_sum (fun σ _ => (Real.exp_pos (H σ)).le) (Finset.mem_univ x.1))

/-- Both the deterministic quadratic term and the Gaussian tensor marks
have uniform rotation moduli for the actual countable leaf partition. -/
theorem tensorLeafLogMean_abs_sub_le {N m k : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U V : SpecialOrthogonal N)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (site : Fin (n + 1) → ℝ≥0) (monomial : Fin (n + 1) → Fin k → ℝ≥0)
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] :
    let H := fun R (x : Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation R) x.1 + fieldEnergy c x.1
    let A := fun R => tensorLeafCoefficients (specialRotation R) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i))
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H U x + cylinderField (A U x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H V x + cylinderField (A V x) g) ∂ν)
        ∂gaussianCoordinates| ≤
      (K * N + 2 * (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 *
        ∑ a, (degree j a : ℝ))) * frobeniusDistance U V := by
  intro H A
  have hi (R : SpecialOrthogonal N) : Integrable (fun x => Real.exp (H R x)) ν := by
    exact finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation R) σ + fieldEnergy c σ)
  have hb := countable_cylinder_log_mean_base_compare ν (H U) (H V) (hi U) (hi V)
    (A U) (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial)
    (fun x => by
      simpa only [H, add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig x.1)
  have hg := tensorLeafGaussianMean_abs_sub_le hN U V I degree amplitude n site monomial ν
    (H V) (hi V)
  exact (abs_sub_le _ _ _).trans ((add_le_add hb hg).trans_eq (by ring))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar variance for the Frobenius moduli used by the perturbed model. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace InvariantIsing

lemma haar_frobeniusLipschitz_memLp_two (hpub : HaarConcentrationInput)
    (N : ℕ) (hN : 3 ≤ N) (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (hμinv : μ.IsMulLeftInvariant) (f : SpecialOrthogonal N → ℝ) (hf : Measurable f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) : MemLp f 2 μ := by
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  obtain ⟨m, _, _, ht⟩ := hp N hN μ inferInstance hμinv f hf L hL hLip
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd := (integral_sq_sub_le_of_gaussian_tail μ f hf m C
    (a * N / L ^ 2) hC.le (by positivity) (fun r hr => by
      simpa only [show -a * (N : ℝ) * r ^ 2 / L ^ 2 = -(a * N / L ^ 2) * r ^ 2 by ring]
        using ht r hr)).1
  have hD := (memLp_two_iff_integrable_sq (hf.sub_const m).aestronglyMeasurable).mpr hd
  convert hD.add (memLp_const m) using 1
  all_goals try with_reducible_and_instances rfl
  ext U
  simp only [Pi.add_apply, sub_add_cancel]

/-- The published concentration input bounds every measurable Frobenius
Lipschitz observable, with constants independent of dimension. -/
theorem haar_frobeniusLipschitz_variance (hpub : HaarConcentrationInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
    ∀ L : ℝ, 0 < L →
      (∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) →
      variance f μ ≤ C * L ^ 2 / N := by
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  refine ⟨C / a, by positivity, ?_⟩
  intro N hN μ hμ hμinv f hf L hL hLip
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m, _, _, ht⟩ := hp N hN μ hμ hμinv f hf L hL hLip
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := variance_le_of_gaussian_median_tail μ f hf m C
    (a * N / L ^ 2) hC.le (by positivity) (fun r hr => by
      simpa only [show -a * (N : ℝ) * r ^ 2 / L ^ 2 = -(a * N / L ^ 2) * r ^ 2 by ring]
        using ht r hr)
  refine hb.trans_eq ?_
  field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalPerturbation
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

lemma diagonalPerturbedEigenvalues_abs_le {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (ht : |t| ≤ 1)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (i : Fin N) :
    |diagonalPerturbedEigenvalues eig I v t i| ≤ K + 4 * m := by
  have hs : |∑ a, if i ∈ I a then v a else 0| ≤ 2 * m := by
    calc
      _ ≤ ∑ a, |if i ∈ I a then v a else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, (2 : ℝ) := Finset.sum_le_sum fun a _ => by
        split_ifs
        · exact hv a
        · norm_num
      _ = _ := by simp <;> ring
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htE : |t * eig i| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul ht (heig i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hshift : |2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0| ≤ 4 * m := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
    calc
      _ ≤ (2 * perturbationScale N) * (2 * m) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 2 * (2 * m) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (perturbationScale_le_one hN)
              (show (0 : ℝ) ≤ 2 by norm_num))) (show 0 ≤ 2 * (m : ℝ) by positivity)
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add htE hshift)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorPressure
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tensor perturbation with a fixed spin/leaf prior.
The prior may be a normalized spin constraint; it is independent of the rotation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma measurable_priorTensorLog {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorTensorLog ν eig c I degree amplitude v) := by
  have hm : Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1 + fieldEnergy c p.2.1 +
      cylinderField (tensorLeafCoefficients (specialRotation p.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hbase : Measurable (fun U : SpecialOrthogonal N =>
        rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1) := by
      exact ((Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul
          (eig i)).const_mul (1/2 : ℝ)).add_const _
    apply (hbase.comp measurable_fst).add
    simp only [tensorLeafCoefficients, cylinderField_feature]
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_spinTensorFeature I degree amplitude x.1 i.2).comp
      measurable_fst).const_mul _).mul
      ((measurable_pi_apply (treeFeatureTag n x.2 i)).comp measurable_snd)
  exact hm.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma priorTensorLog_gaussian_memLp {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0)
    (U : SpecialOrthogonal N) :
    MemLp (fun z => priorTensorLog ν eig c I degree amplitude
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) (U,z)) 2 gaussianCoordinates := by
  have hi := cylinder_log_partition_memLp_two ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1)
    (finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ))
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial) 1
  simpa only [one_mul,priorTensorLog] using hi

lemma priorTensorLog_gaussian_variance (hgauss : GaussianLipschitzVarianceInput)
    {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (site : Fin (n+1) → ℝ≥0) (monomial : Fin (n+1) → Fin k → ℝ≥0)
    (U : SpecialOrthogonal N) :
    variance (fun z => priorTensorLog ν eig c I degree amplitude
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)) (U,z)) gaussianCoordinates ≤
      ∑ i, ((site i : ℝ)*N + ∑ j, (monomial i j : ℝ)*amplitude j^2) := by
  have hv := countable_cylinder_log_partition_variance_le hgauss ν
    (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1)
    (finite_spin_base_exp_integrable ν
      (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ))
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n
      (fun i => tensorVarianceProfile I degree (site i) (monomial i)))
    _ (by positivity)
    (tensorLeafCoefficients_variance_le (specialRotation U) I degree amplitude n site monomial) 1
  simpa only [one_pow, one_mul,priorTensorLog] using hv

/-- The variance constant is independent of the mass and cardinality of
an imposed spin constraint. -/
theorem priorTensorLog_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), IsProbabilityMeasure ν →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ site : Fin (n+1) → ℝ≥0,
    ∀ monomial : Fin (n+1) → Fin k → ℝ≥0,
      let F := priorTensorLog ν eig c I degree amplitude
        (fun i => tensorVarianceProfile I degree (site i) (monomial i))
      let L := K*N + 2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amplitude j^2*
        ∑ a, (degree j a : ℝ))
      MemLp F 2 (μ.prod gaussianCoordinates) ∧
        variance F (μ.prod gaussianCoordinates) ≤
          (∑ i, ((site i : ℝ)*N + ∑ j, (monomial i j : ℝ)*amplitude j^2)) + C*L^2/N := by
  obtain ⟨C,hC,hvar⟩ := haar_frobeniusLipschitz_variance hhaar
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m k n ν hν eig c K hK heig I degree amplitude site monomial F L
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let M := fun U => ∫ z, F (U,z) ∂gaussianCoordinates
  have hm : Measurable M := (measurable_priorTensorLog ν eig c I degree amplitude _).stronglyMeasurable
    |>.integral_prod_right' |>.measurable
  have hL : 0<L := by
    dsimp only [L]
    exact add_pos_of_pos_of_nonneg (mul_pos hK (by exact_mod_cast (show 0<N by omega))) (by positivity)
  have hLip : ∀ U V, |M U-M V|≤L*frobeniusDistance U V := fun U V =>
    tensorLeafLogMean_abs_sub_le (by omega) eig c U V K hK.le heig I degree amplitude n site monomial ν
  have hM := haar_frobeniusLipschitz_memLp_two hhaar N hN μ hμinv M hm L hL hLip
  have hlocal U := priorTensorLog_gaussian_memLp ν eig c I degree amplitude site monomial U
  have hlocalVar U := priorTensorLog_gaussian_variance hgauss ν eig c I degree amplitude site monomial U
  have hresult := variance_of_conditional_center μ gaussianCoordinates
    (measurable_priorTensorLog ν eig c I degree amplitude _) hM
    (fun U => ((hlocal U).sub (memLp_const (M U))).integrable_sq) (fun _ => rfl)
    (fun U => by
      rw [← variance_eq_integral (hlocal U).aestronglyMeasurable.aemeasurable]
      exact hlocalVar U)
  exact ⟨hresult.1,hresult.2.trans (add_le_add le_rfl
    (hvar N hN μ hμ hμinv M hm L hL hLip))⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorPerturbationVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform concentration of the actual finite perturbation for a fixed
constrained prior. No full-cube symmetry is used in this estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem priorPerturbation_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), IsProbabilityMeasure ν →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j|≤2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a|≤2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let F := fun p => (N : ℝ)⁻¹ * priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
        (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i) p
      MemLp F 2 (μ.prod gaussianCoordinates) ∧
        variance F (μ.prod gaussianCoordinates) ≤ (H+4+C*(K+4*m+8)^2)/N := by
  obtain ⟨C,hC,hvar⟩ := priorTensorLog_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH d r F
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  have hNp : 0<N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast hNp
  let a := tensorPerturbationAmplitude N u
  let L := (K+4*m)*N + 2*(∑ i : Fin (n+1), ∑ j : Fin N,
    (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2*∑ b, (d j b : ℝ))
  have hp := hvar N hN μ hμ hμinv m N n ν hν
    (diagonalPerturbedEigenvalues eig I v t) c (K+4*m) (by positivity)
    (diagonalPerturbedEigenvalues_abs_le hNp eig I v hv t ht K heig) I d a
    (fun i => varianceIncrement h i) (fun i j => varianceIncrement (monomialPath n (r j)) i)
  have hsum := tensorPerturbationAmplitude_square_sum_le N u hu
  have hsmall := perturbationScale_sq_le_one hNp
  have hsum' : (∑ j : Fin N, a j^2) ≤ 4*N :=
    hsum.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤4*(N : ℝ))).trans_eq (mul_one _))
  have hG : (∑ i : Fin (n+1), ((varianceIncrement h i : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2)) ≤ (H+4)*N := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,varianceIncrement_sum hh h0,Finset.sum_comm]
    have hm : (∑ j : Fin N, ∑ i : Fin (n+1),
        (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2) ≤ ∑ j : Fin N, a j^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_sum_le n (r j))
        (sq_nonneg _)).trans_eq (one_mul _)
    have hhN := mul_le_mul_of_nonneg_right hH hNr.le
    linarith
  have hdeg : ∀ j : Fin N, (∑ b, (d j b : ℝ)) ≤ 1*((j : ℝ)+1) := by
    intro j
    simpa only [one_mul] using enumeratedSpectralDegree_real_sum_le m j
  have hrot := (tensorPathProfile_rotation_cap d a n r).trans
    (tensorPerturbationAmplitude_degree_sum_le u hu d 1 zero_le_one hdeg)
  have hrot' : (∑ i : Fin (n+1), ∑ j : Fin N,
      (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2*∑ b, (d j b : ℝ)) ≤ 4*N := by
    apply hrot.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤4*(N : ℝ))
  have hL0 : 0≤L := by dsimp only [L] <;> positivity
  have hL : L≤N*(K+4*m+8) := by dsimp only [L] <;> linarith
  have hLsq := pow_le_pow_left₀ hL0 hL 2
  have hvbound := hp.2.trans (add_le_add hG
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq hC.le) hNr.le))
  refine ⟨hp.1.const_mul _,?_⟩
  rw [variance_const_mul]
  have he := mul_le_mul_of_nonneg_left hvbound (sq_nonneg (N : ℝ)⁻¹)
  apply he.trans_eq
  field_simp [hNr.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorTensorNamespace
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian namespaces for the actual fixed-prior model.
Changing Gaussian coordinates preserves its entire pressure law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma measurable_priorNamespacedLog {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (priorNamespacedLog ν eig c I degree amplitude v) :=
  (measurable_priorNamespacedHamiltonian eig c I degree amplitude v).exp.stronglyMeasurable
    |>.integral_prod_right' |>.measurable.log

lemma priorNamespacedLog_conditional_law {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    gaussianCoordinates.map (fun z => priorTensorLog ν eig c I degree amplitude v (U,z)) =
      gaussianCoordinates.map (fun z => priorNamespacedLog ν eig c I degree amplitude v (U,z)) := by
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig (specialRotation U) x.1+fieldEnergy c x.1
  let K := fun F : Spin N × LabeledLeaf n → ℝ => Real.log (∫ x, Real.exp (H x+F x) ∂ν)
  have hK : Measurable K := by
    have he : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) ×
        (Spin N × LabeledLeaf n) => H p.2+p.1 p.2) :=
      measurable_from_prod_countable_left fun x => by
        change Measurable (fun F : Spin N × LabeledLeaf n → ℝ => H x+F x)
        exact measurable_const.add (measurable_pi_apply x)
    exact he.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hl : Measurable (fun z x => cylinderField
      (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) z) :=
    Measurable.of_eval fun _ => measurable_cylinderField _
  have hr : Measurable (fun z x => cylinderField
      (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) z) :=
    Measurable.of_eval fun _ => measurable_cylinderField _
  change gaussianCoordinates.map (K ∘ (fun z x => cylinderField
    (tensorLeafCoefficients (specialRotation U) I degree amplitude n v x) z)) =
      gaussianCoordinates.map (K ∘ (fun z x => cylinderField
        (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v x) z))
  rw [← Measure.map_map hK hl,← Measure.map_map hK hr,tensorNamespacedFields_law]

theorem priorNamespacedLog_law {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0) :
    HasLaw (priorNamespacedLog ν eig c I degree amplitude v)
      ((μ.prod gaussianCoordinates).map (priorTensorLog ν eig c I degree amplitude v))
      (μ.prod gaussianCoordinates) := by
  have hl := measurable_priorTensorLog ν eig c I degree amplitude v
  have hr := measurable_priorNamespacedLog ν eig c I degree amplitude v
  refine ⟨hr.aemeasurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hr hs,Measure.map_apply hl hs,Measure.prod_apply (hr hs),Measure.prod_apply (hl hs)]
  apply lintegral_congr_ae
  apply ae_of_all
  intro U
  have he := congrArg (fun Q : Measure ℝ => Q s)
    (priorNamespacedLog_conditional_law ν eig c U I degree amplitude v)
  have hlU : Measurable (fun z : ℕ → ℝ => priorTensorLog ν eig c I degree amplitude v (U,z)) :=
    hl.comp (measurable_const.prodMk measurable_id)
  have hrU : Measurable (fun z : ℕ → ℝ => priorNamespacedLog ν eig c I degree amplitude v (U,z)) :=
    hr.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hlU hs,Measure.map_apply hrU hs] at he
  exact he.symm

theorem priorNamespacedLog_moments {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (v : Fin (n+1) → SpinTensorIndex I degree → ℝ≥0)
    (hF : MemLp (priorTensorLog ν eig c I degree amplitude v) 2 (μ.prod gaussianCoordinates)) :
    MemLp (priorNamespacedLog ν eig c I degree amplitude v) 2 (μ.prod gaussianCoordinates) ∧
    variance (priorNamespacedLog ν eig c I degree amplitude v) (μ.prod gaussianCoordinates) =
      variance (priorTensorLog ν eig c I degree amplitude v) (μ.prod gaussianCoordinates) ∧
    (∫ p, priorNamespacedLog ν eig c I degree amplitude v p ∂μ.prod gaussianCoordinates) =
      ∫ p, priorTensorLog ν eig c I degree amplitude v p ∂μ.prod gaussianCoordinates := by
  have hlaw := priorNamespacedLog_law μ ν eig c I degree amplitude v
  have hid : MemLp id 2 ((μ.prod gaussianCoordinates).map (priorTensorLog ν eig c I degree amplitude v)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hF.aemeasurable).mpr hF
  exact ⟨hlaw.memLp hid,hlaw.variance_eq.trans (variance_id_map hF.aemeasurable),
    hlaw.integral_eq.trans (integral_map hF.aemeasurable aestronglyMeasurable_id)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorNamespacedVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same uniform bound for the raw, independently namespaced log partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem priorNamespacedPerturbation_variance_oai (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ ν : Measure (Spin N × LabeledLeaf n), IsProbabilityMeasure ν →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j|≤2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a|≤2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let F := priorNamespacedLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
        (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
      MemLp F 2 (μ.prod gaussianCoordinates) ∧
        variance F (μ.prod gaussianCoordinates) ≤ N*(H+4+C*(K+4*m+8)^2) := by
  obtain ⟨C,hC,hvar⟩ := priorPerturbation_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH d r F
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let G := priorTensorLog ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled := hvar N hN μ hμ hμinv m n ν hν eig c K hK heig I u hu v hv t ht h hh h0 H hH
  have heq : (fun p => (N : ℝ)*((N : ℝ)⁻¹*G p))=G := by
    funext p
    simp only [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  have hg : MemLp G 2 (μ.prod gaussianCoordinates) := by
    rw [← heq]
    exact hscaled.1.const_mul N
  have hvg : variance G (μ.prod gaussianCoordinates)≤N*(H+4+C*(K+4*m+8)^2) := by
    calc
      _ = (N : ℝ)^2 * variance (fun p => (N : ℝ)⁻¹*G p) (μ.prod gaussianCoordinates) := by
        conv_lhs => rw [← heq]
        exact variance_const_mul N _ _
      _ ≤ (N : ℝ)^2*((H+4+C*(K+4*m+8)^2)/N) :=
        mul_le_mul_of_nonneg_left hscaled.2 (sq_nonneg _)
      _ = _ := by field_simp
  have hm := priorNamespacedLog_moments μ ν (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i) hg
  exact ⟨hm.1,hm.2.1.trans_le hvg⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.priorNamespacedPerturbation_variance_oai := @OAI.InvariantIsing.priorNamespacedPerturbation_variance_oai
