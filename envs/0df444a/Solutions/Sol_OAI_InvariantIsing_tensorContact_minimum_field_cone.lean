-- Prove2me | solution 1 for OAI.InvariantIsing.tensorContact_minimum_field_cone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:11:27.561693+00:00
-- url     : https://prove2.me/submissions/7ef89608-503b-436f-bf0f-4cd4f15d7c19

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ChildLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

end IsingPerceptron

end

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
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
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

theorem random_countable_cylinder_insertion {Ω X : Type*}
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

lemma joint_integrable_square_of_uniform_conditionals {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] {P : Measure Ω} {Q : Measure Γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {F : Ω × Γ → ℝ}
    (hm : Measurable F) {C : ℝ}
    (hi : ∀ ω, Integrable (fun g => F (ω,g)^2) Q)
    (hb : ∀ ω, (∫ g, F (ω,g)^2 ∂Q) ≤ C) :
    Integrable (fun z => F z^2) (P.prod Q) := by
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  apply integrable_of_measurable_abs_le
    ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact hb ω

lemma measurable_random_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmD : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Fin (r+1) → X) =>
      cylinderField (b (p.2 0)) p.1.2*D p.2) :=
    ((measurable_cylinderFields b).comp
      (measurable_fst.snd.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
        ((measurable_of_countable D).comp measurable_snd)
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)) hmD

lemma cylinder_replica_insertion_second {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    let F := fun g => referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ)
    Integrable (fun g => F g^2) gaussianCoordinates ∧
      (∫ g, F g^2 ∂gaussianCoordinates) ≤
        c^2*((Real.exp (32*((r+1:ℕ):ℝ)^2*K)+2*Real.exp (32*L)+Real.exp (8*((r+1:ℕ):ℝ)^2*K))/2) := by
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
  have ht := gaussian_bounded_insertion_second
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
  simpa only [referenceReplicaMean_eq_ratio,mul_assoc,Function.comp_apply] using ht.2

theorem integrable_joint_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_insertion hν a b D
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).1)
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

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

lemma random_cylinder_all_exp_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1,hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t*cylinderField (a p.2) p.1.2)) :=
      ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t |>.exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((a x).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields a)
      (fun x => cylinderField_law (a x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n:ℝ)*cylinderField (a x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n:ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

lemma measurable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    (((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t)).log

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

lemma cylinder_cgf_second {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun g => (cgf (fun x => cylinderField (a x) g) ν t)^2) gaussianCoordinates ∧
      (∫ g, (cgf (fun x => cylinderField (a x) g) ν t)^2 ∂gaussianCoordinates) ≤
        4*Real.exp (2*(t^2*K)) := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (a z.2) z.1) :=
    (measurable_cylinderFields a).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((a x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((a x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
  exact gaussian_log_partition_second (ν := ν) hm (fun x => cylinder_scaled_law a x t) hv

lemma integrable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t)
      (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_cgf hν a t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).1)
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

lemma integrable_joint_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) (P.prod gaussianCoordinates) := by
  exact integrable_of_measurable_abs_le (measurable_random_cylinder_mean hν a D)
    (fun z => referenceReplicaMean_abs_le (ν z.1) _ D (measurable_of_countable _) hc hD)

theorem joint_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ) ∂P.prod gaussianCoordinates) =
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂P.prod gaussianCoordinates) -
    (r+1 : ℕ)*(∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂P.prod gaussianCoordinates) := by
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
  rw [integral_prod _ (integrable_joint_cylinder_insertion hν a b ha hb D hc hD),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (by positivity) hfirst),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh)]
  exact random_countable_cylinder_insertion hν a b ha hb D hc hD

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

open ProbabilityTheory Filter

lemma mem_interior_integrableExpSet_of_all {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν)
    (t : ℝ) : t ∈ interior (integrableExpSet Y ν) := by
  have h : integrableExpSet Y ν = univ := Set.eq_univ_of_forall he
  simp [h]

lemma contDiff_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ContDiff ℝ 2 (cgf Y ν) :=
  contDiff_iff_contDiffAt.mpr (fun t =>
    (analyticAt_cgf (mem_interior_integrableExpSet_of_all he t)).contDiffAt)

lemma convexOn_cgf_of_all_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y x)) ν) :
    ConvexOn ℝ univ (cgf Y ν) := by
  have hd := contDiff_cgf_of_all_exp he
  apply convexOn_univ_of_deriv2_nonneg (hd.differentiable (by norm_num)) hd.differentiable_deriv_two
  intro t
  have hv := variance_nonneg Y (ν.tilted (t*Y ·))
  rw [variance_tilted_mul (mem_interior_integrableExpSet_of_all he t)] at hv
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, Function.iterate_succ_apply'] using hv

end IsingPerceptron

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

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cylinder_norm_smul (a : ℕ →₀ ℝ) (t : ℝ) :
    (t • a).sum (fun _ c => c^2) = t^2*a.sum (fun _ c => c^2) := by
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [mul_pow,Finsupp.sum]
  rw [Finset.mul_sum]

lemma cylinderCross_smul_right (a b : ℕ →₀ ℝ) (t : ℝ) :
    cylinderCross a (t • b) = t*cylinderCross a b := by
  simp only [cylinderCross,Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma referenceReplicaMean_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) (c : ℝ) :
    referenceReplicaMean ν H (fun σ => c*D σ) = c*referenceReplicaMean ν H D := by
  unfold referenceReplicaMean
  rw [show (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*(c*D σ)) =
    (fun σ => c*(Real.exp (∑ i, H (σ i))*D σ)) from by funext σ; ring,
    integral_const_mul]
  ring

lemma referenceReplicaMean_const {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) (c : ℝ) :
    referenceReplicaMean ν H (fun _ : Fin r → X => c) = c := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he]
  simp

lemma referenceReplicaMean_add_bounded {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (D E : (Fin r → X) → ℝ) {c d : ℝ}
    (hD : ∀ σ, |D σ| ≤ c) (hE : ∀ σ, |E σ| ≤ d) :
    referenceReplicaMean ν H (fun σ => D σ+E σ) =
      referenceReplicaMean ν H D+referenceReplicaMean ν H E := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he,referenceReplicaMean_eq_tilted ν H he,
    referenceReplicaMean_eq_tilted ν H he]
  exact integral_add (integrable_of_measurable_abs_le (measurable_of_countable _) hD)
    (integrable_of_measurable_abs_le (measurable_of_countable _) hE)

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

lemma cylinderCross_bound {X : Type*} (A : X → ℕ →₀ ℝ) {B : ℝ}
    (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B) (x y : X) :
    |cylinderCross (A x) (A y)| ≤ |B| := by
  calc
    _ ≤ ((A x).sum (fun _ c => c^2)+(A y).sum (fun _ c => c^2))/2 := abs_cylinderCross_le _ _
    _ ≤ |B| := by linarith [hA x,hA y,le_abs_self B]

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

lemma integrable_random_scaled_mean [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => t*cylinderField (A x) z.2) D) (P.prod gaussianCoordinates) := by
  simpa only [cylinderField_smul] using
    integrable_joint_cylinder_mean (P := P) hν (fun x => t • A x) D hc hD

lemma randomReplicaAverage_const [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (t : ℝ) (r : ℕ) (c : ℝ) : randomReplicaAverage P ν A t (fun _ : Fin r → X => c) = c := by
  unfold randomReplicaAverage
  calc
    _ = ∫ _z : Ω × (ℕ → ℝ), c ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
      exact referenceReplicaMean_const _ _ (hz t) r c
    _ = c := by simp

theorem randomReplicaEnergy_identity [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B d : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (hdiag : ∀ x, cylinderCross (A x) (A x) = d) (t : ℝ)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    randomReplicaEnergy P ν A t D = t*(d*randomReplicaAverage P ν A t D +
      randomReplicaAverage P ν A t (fun σ => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))) -
      (r+1 : ℕ)*randomReplicaAverage P ν A t
        (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
  let μ := P.prod gaussianCoordinates
  let H := fun z : Ω × (ℕ → ℝ) => fun x => t*cylinderField (A x) z.2
  let E := fun σ : Fin (r+1) → X => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))
  have hE (σ : Fin (r+1) → X) : |E σ| ≤ c*((r:ℝ)*|B|) := by
    dsimp [E]
    rw [abs_mul]
    apply mul_le_mul (hD σ) _ (abs_nonneg _) hc
    calc
      _ ≤ ∑ l : Fin r, |cylinderCross (A (σ 0)) (A (σ l.succ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, |B| := Finset.sum_le_sum (fun _ _ => cylinderCross_bound A hA _ _)
      _ = _ := by simp
  have hV := integrable_random_scaled_mean (P := P) hν A t D hc hD
  have hW := integrable_random_scaled_mean (P := P) hν A t E (by positivity) hE
  have first : (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (H z)
      (fun σ => D σ*(∑ i : Fin (r+1), t*cylinderCross (A (σ 0)) (A (σ i)))) ∂μ) =
      t*(d*randomReplicaAverage P ν A t D+randomReplicaAverage P ν A t E) := by
    calc
      _ = ∫ z : Ω × (ℕ → ℝ), t*(d*referenceReplicaMean (ν z.1) (H z) D+
          referenceReplicaMean (ν z.1) (H z) E) ∂μ := by
        apply integral_congr_ae
        filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
        have heq : (fun σ : Fin (r+1) → X => D σ*(∑ i, t*cylinderCross (A (σ 0)) (A (σ i)))) =
            (fun σ => t*(d*D σ+E σ)) := by
          funext σ
          rw [Fin.sum_univ_succ,hdiag,← Finset.mul_sum]
          dsimp [E]
          ring
        rw [heq,referenceReplicaMean_const_mul,
          referenceReplicaMean_add_bounded _ _ (hz t) _ _
            (fun σ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD σ) (abs_nonneg d)) hE,
          referenceReplicaMean_const_mul]
      _ = _ := by
        rw [integral_const_mul,integral_add (hV.const_mul d) hW,integral_const_mul]
        rfl
  have h := joint_countable_cylinder_insertion (P := P) hν (fun x => t • A x) A
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)) hA D hc hD
  simp only [cylinderField_smul,cylinderCross_smul_right] at h
  have hfresh : (fun (z : Ω × (ℕ → ℝ)) => referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))))) =
    (fun z : Ω × (ℕ → ℝ) => t*referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
    funext z
    rw [show (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) =
      (fun τ => t*(D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) from by funext τ; ring,
      referenceReplicaMean_const_mul]
  change randomReplicaEnergy P ν A t D = _ at h
  change (∫ z, referenceReplicaMean (ν z.1) (H z) _ ∂μ) = _ at first
  rw [first,hfresh,integral_const_mul] at h
  rw [h]
  dsimp [E,randomReplicaAverage,μ,H]
  ring

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

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true, if_true] <;> ring
  · simp only [h,ite_false, if_false,zero_mul]

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

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

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

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

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma cylinderCross_tagged_sum {m : ℕ} (a b : Fin m → ℕ →₀ ℝ) :
    cylinderCross (∑ i : Fin m, tagCoefficients i (a i)) (∑ i : Fin m, tagCoefficients i (b i)) =
      ∑ i, cylinderCross (a i) (b i) := by
  classical
  rw [cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_sum_right]
  simp only [cylinderCross_tag,Fin.val_inj]
  simp

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
-- module Solutions.OAIQ258_II.IsingPerceptron_NamespaceSplit
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
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
namespace IsingPerceptron

lemma measurable_gaussianNamespaceSplit (j : ℕ) : Measurable (gaussianNamespaceSplit j) := by
  unfold gaussianNamespaceSplit
  fun_prop

lemma gaussianNamespaceSplit_law (j : ℕ) :
    gaussianCoordinates.map (gaussianNamespaceSplit j) =
      gaussianCoordinates.prod (otherNamespacesLaw j) := by
  let e := Equiv.optionSubtypeNe j
  let t : Option {k : ℕ // k ≠ j} × ℕ → ℕ := fun p => Nat.pair (e p.1) p.2
  have ht : Function.Injective t := by
    intro p q h
    have he := Nat.pair_eq_pair.mp h
    exact Prod.ext (e.injective he.1) he.2
  have hp := gaussian_pullback_measurePreserving t ht
  let F : (ℕ → ℝ) → Option {k : ℕ // k ≠ j} → ℕ → ℝ := fun g k i => g (t (k,i))
  have hmF : Measurable F := by unfold F; fun_prop
  have hF : gaussianCoordinates.map F = Measure.infinitePi
      (fun _ : Option {k : ℕ // k ≠ j} => gaussianCoordinates) := by
    change gaussianCoordinates.map
      ((MeasurableEquiv.curry (Option {k : ℕ // k ≠ j}) ℕ ℝ) ∘
        (fun g => fun p => g (t p))) = _
    rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
      Measure.infinitePi_map_curry (fun (_ : Option {k : ℕ // k ≠ j}) (_ : ℕ) => gaussianReal 0 1)]
    rfl
  have hs := infinitePi_option_split gaussianCoordinates
    (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)
  have hc : (fun i : Option {k : ℕ // k ≠ j} =>
      i.elim gaussianCoordinates (fun _ => gaussianCoordinates)) = (fun _ => gaussianCoordinates) := by
    funext i; cases i <;> rfl
  rw [hc] at hs
  have he : gaussianNamespaceSplit j =
      (fun q : Option {k : ℕ // k ≠ j} → ℕ → ℝ => (q none,fun k => q (some k))) ∘ F := by
    rfl
  rw [he,← Measure.map_map (by fun_prop) hmF,hF]
  exact hs

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma cgf_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H Y : X → ℝ) (t : ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (het : Integrable (fun x => Real.exp (H x+t*Y x)) ν) :
    cgf Y (gibbsProbability ν H) t =
      Real.log (referencePartition ν (fun x => H x+t*Y x)) - Real.log (referencePartition ν H) := by
  rw [gibbsProbability_eq_tilted _ _ he]
  unfold cgf mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (ne_of_gt (_root_.MeasureTheory.integral_exp_pos het))
    (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))]
  rfl

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedCGF
attribute [-instance] _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

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

lemma cylinder_weighted_variant_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j))
    (c : ι → ℝ) :
    (∑ i, c i • a i).sum (fun _ v => v^2) = (∑ i, c i • b i).sum (fun _ v => v^2) := by
  classical
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,hc]

lemma dual_cylinderField {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    L (fun i => cylinderField (a i) g) =
      cylinderField (∑ i, L (Pi.single i 1) • a i) g := by
  have hv : (fun i => cylinderField (a i) g) =
      ∑ i, cylinderField (a i) g • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv,map_sum,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,cylinderField_smul,smul_eq_mul,mul_comm]

 

lemma cylinder_finite_law_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j)) :
    gaussianCoordinates.map (fun g i => cylinderField (a i) g) =
      gaussianCoordinates.map (fun g i => cylinderField (b i) g) := by
  classical
  have ha : Measurable (fun g i => cylinderField (a i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))
  have hb : Measurable (fun g i => cylinderField (b i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,integral_map ha.aemeasurable (by fun_prop),
    integral_map hb.aemeasurable (by fun_prop)]
  simp only [dual_cylinderField]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    ← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law,cylinderField_law,cylinder_weighted_variant_eq a b hc]

 

theorem cylinder_fields_law_eq {X : Type*}
    (a b : X → ℕ →₀ ℝ) (hc : ∀ x y, cylinderCross (a x) (a y) = cylinderCross (b x) (b y)) :
    gaussianCoordinates.map (fun g x => cylinderField (a x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (b x) g) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))).aemeasurable
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))).aemeasurable).mpr
  intro I
  exact cylinder_finite_law_eq (fun i : I => a i) (fun i : I => b i) (fun i j => hc i j)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianPair_preserving : MeasurePreserving gaussianPair gaussianCoordinates
    (gaussianCoordinates.prod gaussianCoordinates) := by
  have hs : MeasurePreserving (gaussianNamespaceSplit 0) gaussianCoordinates
      (gaussianCoordinates.prod (otherNamespacesLaw 0)) :=
    ⟨measurable_gaussianNamespaceSplit 0,gaussianNamespaceSplit_law 0⟩
  have he := measurePreserving_eval_infinitePi
    (fun _ : {k : ℕ // k ≠ 0} => gaussianCoordinates) ⟨1,by decide⟩
  exact ((MeasurePreserving.id gaussianCoordinates).prod he).comp hs

lemma gaussianSumCoefficients_field {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) (g : ℕ → ℝ) :
    cylinderField (gaussianSumCoefficients a b t x) g =
      cylinderField (a x) (gaussianPair g).1 + t*cylinderField (b x) (gaussianPair g).2 := by
  unfold gaussianSumCoefficients
  rw [cylinderField_finset_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderField_tag,cylinderField_smul,gaussianPair]

lemma gaussianSumCoefficients_cross {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x y : X) :
    cylinderCross (gaussianSumCoefficients a b t x) (gaussianSumCoefficients a b t y) =
      cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y) := by
  unfold gaussianSumCoefficients
  rw [cylinderCross_tagged_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderCross_smul,pow_two]

 

theorem cylinder_independent_sum_law {X : Type*} (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    (gaussianCoordinates.prod gaussianCoordinates).map
      (fun g x => cylinderField (a x) g.1+t*cylinderField (b x) g.2) =
      gaussianCoordinates.map (fun g x => cylinderField (c x) g) := by
  rw [← gaussianPair_preserving.map_eq,Measure.map_map (by
    apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)) gaussianPair_preserving.measurable]
  have he : (fun g x => cylinderField (a x) (gaussianPair g).1+t*cylinderField (b x) (gaussianPair g).2) =
      (fun g x => cylinderField (gaussianSumCoefficients a b t x) g) := by
    funext g x; exact (gaussianSumCoefficients_field a b t x g).symm
  change gaussianCoordinates.map (fun g x => cylinderField (a x) (gaussianPair g).1+
    t*cylinderField (b x) (gaussianPair g).2) = _
  rw [he]
  exact cylinder_fields_law_eq _ _ (fun x y => (gaussianSumCoefficients_cross a b t x y).trans (hc x y).symm)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma hasDerivAt_mean_cgf {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} (ν : Ω → Measure X) (Y : Ω → X → ℝ)
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) P)
    (hd : ∀ t, Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)) P)
    (v : ℝ) :
    HasDerivAt (fun t => ∫ ω, cgf (Y ω) (ν ω) t ∂P)
      (∫ ω, ∫ x, Y ω x ∂(ν ω).tilted (fun x => v*Y ω x) ∂P) v := by
  let D : ℝ → Ω → ℝ := fun t ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t*Y ω x)
  let B : Ω → ℝ := fun ω => |D (v-1) ω|+|D (v+1) ω|
  have hderiv : ∀ᵐ ω ∂P, ∀ t : ℝ, HasDerivAt (cgf (Y ω) (ν ω)) (D t ω) t := by
    filter_upwards [he] with ω hω
    intro t
    dsimp [D]
    rw [integral_tilted_mul_self (mem_interior_integrableExpSet_of_all hω t)]
    exact (analyticAt_cgf (mem_interior_integrableExpSet_of_all hω t)).differentiableAt.hasDerivAt
  have hB : Integrable B P := (hd (v-1)).abs.add (hd (v+1)).abs
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (v-1) (v+1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) (hi v)
    (hd v).aestronglyMeasurable (bound := B) ?_ hB ?_).2
  · filter_upwards [he,hderiv] with ω hω hdω
    intro t ht
    have hmono := (convexOn_cgf_of_all_exp hω).monotoneOn_deriv
      (fun x _ => (hdω x).differentiableAt)
    have hlo := hmono (mem_univ _) (mem_univ _) ht.1.le
    have hhi := hmono (mem_univ _) (mem_univ _) ht.2.le
    rw [(hdω (v-1)).deriv,(hdω t).deriv] at hlo
    rw [(hdω t).deriv,(hdω (v+1)).deriv] at hhi
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by dsimp [B] <;> linarith [neg_abs_le (D (v-1) ω),abs_nonneg (D (v+1) ω)],
      by dsimp [B] <;> linarith [le_abs_self (D (v+1) ω),abs_nonneg (D (v-1) ω)]⟩
  · filter_upwards [hderiv] with ω hω
    exact fun t _ => hω t

lemma integral_tilted_eq_single_replica {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} {t : ℝ} (he : Integrable (fun x => Real.exp (t*Y x)) ν)
    (hi : Integrable Y (ν.tilted (fun x => t*Y x))) :
    (∫ x, Y x ∂ν.tilted (fun x => t*Y x)) =
      referenceReplicaMean ν (fun x => t*Y x) (fun σ : Fin 1 → X => Y (σ 0)) := by
  rw [referenceReplicaMean_eq_tilted ν _ he]
  let : IsProbabilityMeasure (ν.tilted (fun x => t*Y x)) := isProbabilityMeasure_tilted he
  exact (integral_comp_eval (μ := fun _ : Fin 1 => ν.tilted (fun x => t*Y x)) (i := 0) hi.aestronglyMeasurable).symm

lemma integrable_random_cylinder_tilted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x, cylinderField (a x) z.2
      ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2)) (P.prod gaussianCoordinates) := by
  have hh := integrable_joint_cylinder_insertion (P := P) hν (fun x => t • a x) a
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg t))
    ha (fun _ : Fin 1 → X => (1:ℝ)) (c := 1) (by norm_num) (by intro; norm_num)
  simp only [mul_one,cylinderField_smul] at hh
  apply hh.congr
  filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
  exact (integral_tilted_eq_single_replica (ν z.1) (hz t)
    ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1:ℝ≥0)).integrable (by norm_num))).symm

 

theorem hasDerivAt_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    HasDerivAt (fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates)
      (∫ z : Ω × (ℕ → ℝ), ∫ x, cylinderField (a x) z.2
        ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2) ∂P.prod gaussianCoordinates) t := by
  apply hasDerivAt_mean_cgf (P := P.prod gaussianCoordinates)
    (fun z : Ω × (ℕ → ℝ) => ν z.1) (fun z x => cylinderField (a x) z.2)
  · exact random_cylinder_all_exp_ae (P := P) hν a ha
  · exact integrable_random_cylinder_cgf (P := P) hν a ha
  · exact integrable_random_cylinder_tilted_mean (P := P) hν a ha

lemma cylinder_tilted_mean_eq_energy {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    (∫ z : Ω × (ℕ → ℝ), ∫ x, cylinderField (a x) z.2
      ∂(ν z.1).tilted (fun x => t*cylinderField (a x) z.2) ∂P.prod gaussianCoordinates) =
      randomReplicaEnergy P ν a t (fun _ : Fin 1 → X => 1) := by
  unfold randomReplicaEnergy
  apply integral_congr_ae
  filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
  simpa only [mul_one] using integral_tilted_eq_single_replica (ν z.1) (hz t)
    ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hz t) (1:ℝ≥0)).integrable (by norm_num))

 

theorem hasDerivAt_random_cylinder_covariance {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K d : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hdiag : ∀ x, cylinderCross (a x) (a x) = d) (t : ℝ) :
    HasDerivAt (fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates)
      (t*(d-randomReplicaAverage P ν a t (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))) t := by
  have hd := hasDerivAt_random_cylinder_cgf (P := P) hν a ha t
  rw [cylinder_tilted_mean_eq_energy hν a ha t,
    randomReplicaEnergy_identity hν a ha hdiag t (fun _ : Fin 1 → X => (1:ℝ)) (c := 1)
      (by norm_num) (by intro; norm_num)] at hd
  simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero,one_mul,Nat.reduceAdd,Nat.cast_one,
    Fin.tail,Fin.succ_zero_eq_one] at hd
  rw [randomReplicaAverage_const hν a ha,randomReplicaAverage_const hν a ha] at hd
  simpa only [mul_one,add_zero,Nat.reduceAdd,Nat.cast_one,one_mul,Fin.tail,Fin.succ_zero_eq_one] using hd

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exp_mul_le_endpoints {v t y : ℝ} (ht : t ∈ Icc (v-1) (v+1)) :
    Real.exp (t*y) ≤ Real.exp ((v-1)*y)+Real.exp ((v+1)*y) := by
  by_cases hy : 0 ≤ y
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2 hy)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ht.1 (le_of_not_ge hy))).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

lemma continuous_bounded_exponential_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {Y D : X → ℝ} (hY : Measurable Y) (hD : Measurable D)
    (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν)
    {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ x, |D x| ≤ C) :
    Continuous (fun t : ℝ => ∫ x, Real.exp (t*Y x)*D x ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated (bound := fun x =>
    (Real.exp ((v-1)*Y x)+Real.exp ((v+1)*Y x))*C)
  · exact Eventually.of_forall (fun t => ((hY.const_mul t).exp.mul hD).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhds (show v-1 < v by linarith) (show v < v+1 by linarith)] with t ht
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (exp_mul_le_endpoints ⟨ht.1.le,ht.2.le⟩) (hb x) (abs_nonneg _) (by positivity)
  · exact ((he (v-1)).add (he (v+1))).mul_const C
  · exact ae_of_all _ (fun x => by fun_prop)

lemma replica_all_exp {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν) (r : ℕ) (t : ℝ) :
    Integrable (fun σ : Fin r → X => Real.exp (t*∑ i, Y (σ i))) (Measure.pi (fun _ => ν)) := by
  simpa only [Finset.mul_sum,Real.exp_sum] using
    Integrable.fintype_prod (μ := fun _ : Fin r => ν) (fun _ : Fin r => he t)

lemma continuous_referenceReplicaMean {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} (he : ∀ t, Integrable (fun x => Real.exp (t*Y x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hD : ∀ σ, |D σ| ≤ C) :
    Continuous (fun t : ℝ => referenceReplicaMean ν (fun x => t*Y x) D) := by
  have hnum := continuous_bounded_exponential_integral (Measure.pi (fun _ : Fin r => ν))
    (measurable_of_countable (fun σ : Fin r → X => ∑ i, Y (σ i))) (measurable_of_countable D)
    (replica_all_exp ν he r) hC hD
  have hden : Continuous (fun t : ℝ => ∫ x, Real.exp (t*Y x) ∂ν) := by
    simpa only [mul_one] using continuous_bounded_exponential_integral ν
      (measurable_of_countable Y) (measurable_const : Measurable (fun _ : X => (1:ℝ)))
      he (C := 1) (by norm_num) (by intro; norm_num)
  convert hnum.div (hden.pow r) (fun t => pow_ne_zero r (MeasureTheory.integral_exp_pos (he t)).ne') using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  simp [referenceReplicaMean,referencePartition,Finset.mul_sum]

 

lemma continuous_randomReplicaAverage {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hC : 0 ≤ C) (hD : ∀ σ, |D σ| ≤ C) :
    Continuous (fun t : ℝ => randomReplicaAverage P ν a t D) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply continuousAt_of_dominated (bound := fun _ : Ω × (ℕ → ℝ) => C)
  · filter_upwards [] with t
    exact (integrable_random_scaled_mean (P := P) hν a t D hC hD).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using referenceReplicaMean_abs_le (ν z.1) _ D
        (measurable_of_countable D) hC hD))
  · exact integrable_const _
  · filter_upwards [random_cylinder_all_exp_ae (P := P) hν a ha] with z hz
    exact (continuous_referenceReplicaMean (ν z.1) hz D hC hD).continuousAt

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma hasDerivWithinAt_sqrt_comp_zero {H A : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (t*A t) t) (hA : ContinuousAt A 0) :
    HasDerivWithinAt (fun a => H (Real.sqrt a)) (A 0 / 2) (Ici 0) 0 := by
  have hquot : Tendsto (fun t => (H t-H 0)/t^2) (𝓝[>] (0:ℝ)) (𝓝 (A 0/2)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun t => t*A t) (g' := fun t => 2*t)
    · exact Eventually.of_forall (fun t => (hH t).sub_const (H 0))
    · exact Eventually.of_forall (fun t => by simpa using (hasDerivAt_id t).fun_pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (by norm_num) (ne_of_gt ht)
    · simpa using ((hH 0).continuousAt.fun_sub (continuousAt_const (y := H 0))).tendsto.mono_left nhdsWithin_le_nhds
    · simpa using ((continuousAt_id : ContinuousAt (fun t : ℝ => t) 0).fun_pow 2).tendsto.mono_left nhdsWithin_le_nhds
    · have h : Tendsto (fun t => A t/2) (𝓝[>] (0:ℝ)) (𝓝 (A 0/2)) :=
        (hA.div_const 2).tendsto.mono_left nhdsWithin_le_nhds
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      field_simp [ht0.ne']
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr ht
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)]
  apply (hquot.comp hsqrt).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [slope_def_field,Real.sq_sqrt (le_of_lt ht)]

lemma hasDerivWithinAt_sqrt_comp {H A : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (t*A t) t) (hA : Continuous A)
    {a : ℝ} (ha : 0 ≤ a) :
    HasDerivWithinAt (fun a => H (Real.sqrt a)) (A (Real.sqrt a)/2) (Ici 0) a := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hasDerivWithinAt_sqrt_comp_zero hH hA.continuousAt
  · have h := (hH (Real.sqrt a)).comp a (Real.hasDerivAt_sqrt (ne_of_gt ha))
    have hd : Real.sqrt a * A (Real.sqrt a) * (1 / (2*Real.sqrt a)) = A (Real.sqrt a)/2 := by
      field_simp [(Real.sqrt_pos.mpr ha).ne']
    simpa only [Function.comp_def,hd] using h.hasDerivWithinAt (s := Ici 0)

 

theorem hasDerivWithinAt_random_cylinder_variance {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K d : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hdiag : ∀ x, cylinderCross (a x) (a x) = d) {v : ℝ} (hv : 0 ≤ v) :
    HasDerivWithinAt (fun v => ∫ z : Ω × (ℕ → ℝ),
        cgf (fun x => cylinderField (a x) z.2) (ν z.1) (Real.sqrt v)
        ∂P.prod gaussianCoordinates)
      ((d-randomReplicaAverage P ν a (Real.sqrt v)
        (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))/2) (Ici 0) v := by
  apply hasDerivWithinAt_sqrt_comp
    (H := fun t => ∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (a x) z.2) (ν z.1) t ∂P.prod gaussianCoordinates)
    (A := fun t => d-randomReplicaAverage P ν a t (fun σ : Fin 2 → X => cylinderCross (a (σ 1)) (a (σ 0))))
  · exact hasDerivAt_random_cylinder_covariance hν a ha hdiag
  · apply Continuous.fun_sub continuous_const
    apply continuous_randomReplicaAverage hν a ha (C := max K 0)
    · exact le_max_right _ _
    · intro σ
      have h := abs_cylinderCross_le (a (σ 1)) (a (σ 0))
      have h1 := ha (σ 1)
      have h0 := ha (σ 0)
      exact (by linarith : |cylinderCross (a (σ 1)) (a (σ 0))| ≤ K).trans (le_max_left _ _)
  · exact hv

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma random_cgf_insertion_eq {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (b : X → ℕ →₀ ℝ) {K : ℝ} (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    ∀ᵐ z ∂P.prod gaussianCoordinates,
      cgf (fun x => cylinderField (b x) z.2) (gibbsProbability (ν z.1) (fun x => H (z.1,x))) t =
        Real.log (∫ x, Real.exp (H (z.1,x)+t*cylinderField (b x) z.2) ∂ν z.1)-
          Real.log (∫ x, Real.exp (H (z.1,x)) ∂ν z.1) := by
  have hη := measurable_gibbsProbability hν hH
  have ht := random_cylinder_all_exp_ae (P := P) hη b hb
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  filter_upwards [ht,he'] with z ht he
  have hi := ht t
  rw [gibbsProbability_eq_tilted _ _ he,integrable_tilted_iff he] at hi
  have hisum : Integrable (fun x => Real.exp (H (z.1,x)+t*cylinderField (b x) z.2)) (ν z.1) := by
    simpa only [smul_eq_mul,← Real.exp_add] using hi
  exact cgf_fold _ _ _ _ he hisum

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma monotone_field_add {h l : ℕ → ℝ} (hh : Monotone h) (hl : Monotone l)
    {a : ℝ} (ha : 0 ≤ a) : Monotone (fun i => h i+a*l i) := by
  intro i j hij
  exact add_le_add (hh hij) (mul_le_mul_of_nonneg_left (hl hij) ha)

lemma field_add_nonneg {h l : ℕ → ℝ} (h0 : 0 ≤ h 0) (l0 : 0 ≤ l 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ h 0+a*l 0 := add_nonneg h0 (mul_nonneg ha l0)

end IsingPerceptron

 

 

 

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
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_add {n : ℕ} (a c : Fin (n+1) → ℝ) :
    finiteFieldPath (fun i => a i+c i) = fun i => finiteFieldPath a i+finiteFieldPath c i := by
  funext i
  simp only [finiteFieldPath,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TimeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time Increment. -/

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
namespace IsingPerceptron

lemma right_derivative_nonneg_of_min {F : ℝ → ℝ} {D : ℝ}
    (hD : HasDerivWithinAt F D (Ici 0) 0)
    (hmin : ∀ᶠ a in 𝓝[>] (0:ℝ), F 0 ≤ F a) : 0 ≤ D := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp
    (hD.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto ht
  filter_upwards [hmin,self_mem_nhdsWithin] with a ha ha'
  simpa only [slope_def_field,sub_zero] using div_nonneg (sub_nonneg.mpr ha) ha'.le

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteFieldPath_const_mul {n : ℕ} (a : Fin (n+1) → ℝ) (t : ℝ) :
    finiteFieldPath (fun i => t*a i) = fun i => t*finiteFieldPath a i := by
  ext i
  simp only [finiteFieldPath,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma logPartition_eq {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    logPartition H = Real.log (∑ x, Real.exp (H x)) - Real.log (Fintype.card X) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, Real.log_mul (inv_ne_zero hc) (sum_exp_pos H).ne', Real.log_inv]
  ring

lemma logPartition_add_const {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (c : ℝ) :
    logPartition (fun x => H x + c) = logPartition H + c := by
  rw [logPartition_eq, logPartition_eq]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul (sum_exp_pos H).ne' (Real.exp_ne_zero c),
    Real.log_exp]
  ring

lemma logPartition_le_add {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, H x ≤ K x + c) :
    logPartition H ≤ logPartition K + c := by
  have hs : (∑ x, Real.exp (H x)) ≤ ∑ x, Real.exp (K x + c) :=
    Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (h x)
  have hl : logPartition H ≤ logPartition (fun x => K x + c) := by
    rw [logPartition_eq, logPartition_eq]
    exact sub_le_sub_right (Real.log_le_log (sum_exp_pos H) hs) _
  simpa only [logPartition_add_const] using hl

lemma abs_logPartition_sub_le {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, |H x - K x| ≤ c) :
    |logPartition H - logPartition K| ≤ c := by
  have h₁ := logPartition_le_add H K c fun x => by
    have := (abs_le.mp (h x)).2
    linarith
  have h₂ := logPartition_le_add K H c fun x => by
    have := (abs_le.mp (h x)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_Rotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ising pressure on an orthogonal spectral orbit

The interaction is defined using a real linear isometry, so orthogonality
is part of its type. The bounds hold pointwise in the rotation; no Haar
or independence assumption is needed for these finite-volume estimates.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

@[simp] lemma logPartition_zero {X : Type*} [Fintype X] [Nonempty X] :
    logPartition (fun _ : X => (0 : ℝ)) = 0 := by
  rw [logPartition_eq]
  simp

/-- Pointwise operator comparison in spectral coordinates. -/
lemma abs_rotatedEnergy_sub_le {N : ℕ} (eig κ : Fin N → ℝ) (U : Rotation N)
    (δ : ℝ) (hδ : ∀ i, |eig i - κ i| ≤ δ) (σ : Spin N) :
    |rotatedEnergy eig U σ - rotatedEnergy κ U σ| ≤ δ * N / 2 := by
  have he : rotatedEnergy eig U σ - rotatedEnergy κ U σ =
      (1 / 2 : ℝ) * ∑ i, (eig i - κ i) * (U (spinVector σ) i) ^ 2 := by
    simp only [rotatedEnergy, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ i, |(eig i - κ i) * (U (spinVector σ) i) ^ 2| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, |eig i - κ i| * (U (spinVector σ) i) ^ 2 := by
      simp only [abs_mul, abs_sq]
    _ ≤ (1 / 2 : ℝ) * ∑ i, δ * (U (spinVector σ) i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hδ i) (sq_nonneg _)
    _ = δ * N / 2 := by rw [← Finset.mul_sum, rotated_spin_sq_sum]; ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite spectral tensor model on the countable spin/leaf state space.
The Gaussian energy marks are the actual pushforward of the coordinate
marks, and the tilted ancestor-prefix marginal has its cascade value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

lemma finiteLogIntegral_uniformSpinPrior {N : ℕ} (H : Spin N → ℝ) :
    IsingPerceptron.finiteLogIntegral (uniformSpinPrior N : Measure (Spin N)) H = logPartition H := by
  unfold IsingPerceptron.finiteLogIntegral logPartition
  congr 1
  change (∫ σ, Real.exp (H σ) ∂(PMF.uniformOfFintype (Spin N)).toMeasure) = _
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]

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

lemma varianceIncrement_sum {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (n : ℕ) :
    (∑ i : Fin (n + 1), (varianceIncrement q i : ℝ)) = q n := by
  simp_rw [varianceIncrement_coe hq h0]
  rw [Fin.sum_univ_eq_sum_range, pathIncrement_sum]

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

omit [Countable X] [MeasurableSingletonClass X] in
lemma measurable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hA.const_mul t)).log

/-- The external-disorder-dependent log partition is integrable, by the
uniform pointwise Gaussian second-moment estimate. -/
lemma integrable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) (P.prod gaussianCoordinates) := by
  have hm := measurable_randomCoefficient_cgf hν A hA t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).1)
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

private lemma measurable_tensorBaseEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (Spin N × LabeledLeaf n) =>
      rotatedEnergy eig (specialRotation p.1.1) p.2.1 + fieldEnergy c p.2.1) := by
  apply measurable_from_prod_countable_left
  intro x
  have hrot : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  exact (hrot.comp measurable_fst).add_const (fieldEnergy c x.1)

private lemma tensorBase_exp_integrable {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Integrable (fun x : Spin N × LabeledLeaf n =>
      Real.exp (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1))
      (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) :=
  (Integrable.of_finite : Integrable
    (fun σ : Spin N => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (uniformSpinPrior N : Measure (Spin N))).comp_fst (labeledLeafLaw n ω.2)

private lemma measurable_namespacedPathField {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : ((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hm : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hm
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  rfl

/-- Exponentials of the tensor Hamiltonian are integrable for
almost every joint rotation/tree/Gaussian disorder. No concentration or
limiting-pressure hypothesis is used. -/
theorem tensorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) := tensorBase_exp_integrable eig c n ω
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorBaseEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_namespacedPathField I degree amplitude n treeDegree h
  have hA (ω : Ω) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amplitude n treeDegree h hh h0 x
  have he := randomCoefficient_all_exp_ae
    (P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) htilt A hAm hA
  filter_upwards [he] with p hp
  have hi := hp 1
  rw [integrable_tilted_iff (hbase p.1)] at hi
  simpa only [H, A, ν, one_mul, smul_eq_mul, ← Real.exp_add] using hi

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorGaussianMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

lemma finite_spin_base_exp_integrable {N n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν] (H : Spin N → ℝ) :
    Integrable (fun x : Spin N × LabeledLeaf n => Real.exp (H x.1)) ν := by
  classical
  apply (integrable_const (∑ σ : Spin N, Real.exp (H σ))).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Finset.single_le_sum (fun σ _ => (Real.exp_pos (H σ)).le) (Finset.mem_univ x.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorFrozenFluctuation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the actual three-disorder pressure moments to one frozen Gaussian CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal ENNReal

namespace InvariantIsing

private lemma measurable_tensorJointLog {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ)
    (Y : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) × (Spin N × LabeledLeaf n)) → ℝ)
    (hY : Measurable Y) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
      Real.log (∫ x : Spin N × LabeledLeaf n,
        Real.exp (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 + Y (p, x))
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)) := by
  have hbase : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) => rotatedEnergy eig (specialRotation p.1.1.1) p.2.1 + fieldEnergy c p.2.1) := by
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
      unfold rotatedEnergy
      exact (Finset.measurable_sum _ fun i _ =>
        ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
    exact (hr.comp measurable_fst.fst).add_const (fieldEnergy c x.1)
  let ν := fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact (measurable_random_referencePartition (ν := ν)
    ((measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd)
    (hbase.add hY)).log

lemma measurable_tensorNamespacedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (tensorNamespacedLog eig c I degree amplitude n treeDegree h) := by
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hY : Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amplitude n v p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hp : Measurable (fun p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ) =>
        (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
    convert (measurable_tensorNamespacedFields_joint I degree amplitude n v x).comp hp using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact measurable_tensorJointLog eig c n _ hY

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCoefficientDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine compact parameter region for the finite upper comparison.
Field covariance increments are nonnegative and their sum is capped. -/

noncomputable section
open Set
open scoped BigOperators

namespace InvariantIsing

lemma tensorContactRegion_bounds {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (hp : p ∈ tensorContactRegion N m n H) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ (∀ j, 0 ≤ p.2.1 j) ∧ (∑ j, p.2.1 j) ≤ H ∧
      (∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2) ∧ (∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) := by
  exact ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.1.1.2.1, hp.2,
    fun j => ⟨hp.1.1.2.2.1 j, hp.1.2.2.2.1 j⟩,
    fun a => ⟨hp.1.1.2.2.2 a, hp.1.2.2.2.2 a⟩⟩

lemma tensorContactRegion_mem {N m n : ℕ} {H : ℝ}
    {p : TensorContactParameter N m n} (ht : p.1 ∈ Icc (0 : ℝ) 1)
    (ha : ∀ j, 0 ≤ p.2.1 j) (hcap : (∑ j, p.2.1 j) ≤ H)
    (hu : ∀ j, p.2.2.1 j ∈ Icc (1 : ℝ) 2)
    (hv : ∀ a, p.2.2.2 a ∈ Icc (1 : ℝ) 2) : p ∈ tensorContactRegion N m n H := by
  refine ⟨⟨⟨ht.1, ha, (fun j => (hu j).1), (fun a => (hv a).1)⟩,
    ht.2, ?_, (fun j => (hu j).2), (fun a => (hv a).2)⟩, hcap⟩
  intro j
  exact (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)).trans hcap

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right derivative of an independent linear-field insertion in the
tensor model. The variance-zero endpoint is included. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma randomReplicaAverage_zero_reference {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (A : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    randomReplicaAverage P ν A 0 D =
      ∫ ω, referenceReplicaMean (ν ω) (fun _ => 0) D ∂P := by
  unfold randomReplicaAverage
  simp only [zero_mul]
  rw [integral_fun_fst (fun ω => referenceReplicaMean (ν ω) (fun _ => 0) D)]
  simp only [probReal_univ, one_smul]

lemma tensorLinearCoefficients_cross {N : ℕ} (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorLinearCoefficients n g x) (tensorLinearCoefficients n g y) =
      g (labeledCommonDepth n x.2 y.2) * ∑ i, spinValue (x.1 i) * spinValue (y.1 i) :=
  treeField_path_cross n x.2 y.2 hg g0 _ _

lemma tensorLinearCoefficients_variance {N : ℕ} (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0) (x : Spin N × LabeledLeaf n) :
    (tensorLinearCoefficients n g x).sum (fun _ c => c ^ 2) = N * g n := by
  rw [← cylinderCross_self, tensorLinearCoefficients_cross n g hg g0, labeledCommonDepth_self]
  simp only [← pow_two, spinValue_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- The Gaussian covariance derivative is exactly the actual spin
overlap times the field direction at the common ancestor level. -/
lemma tensorLinearCoefficients_cross_normalized {N : ℕ} (hN : 0 < N) (n : ℕ)
    (g : ℕ → ℝ) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (σ : Fin 2 → Spin N × LabeledLeaf n) :
    cylinderCross (tensorLinearCoefficients n g (σ 1))
      (tensorLinearCoefficients n g (σ 0)) = N * tensorFieldPairObservable g σ := by
  rw [tensorLinearCoefficients_cross n g hg g0]
  unfold tensorFieldPairObservable
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem tensorFieldCGFMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (tensorFieldCGFMean μ eig c I degree amp n b treeDegree h g)
      ((N * g n - N * tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g)) / 2) (Ici 0) 0 := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let ν := tensorNamespacedReference eig c I degree amp n treeDegree h
  have hν : Measurable ν := measurable_tensorNamespacedReference eig c I degree amp n treeDegree h
  have hd := hasDerivWithinAt_random_cylinder_variance (P := Q) hν
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (d := N * g n) (fun x => by rw [cylinderCross_self, tensorLinearCoefficients_variance n g hg g0])
    (v := 0) (by norm_num)
  have hc : (fun σ : Fin 2 → Spin N × LabeledLeaf n =>
      cylinderCross (tensorLinearCoefficients n g (σ 1)) (tensorLinearCoefficients n g (σ 0))) =
      (fun σ => N * tensorFieldPairObservable g σ) :=
    funext (tensorLinearCoefficients_cross_normalized hN n g hg g0)
  rw [Real.sqrt_zero, hc, randomReplicaAverage_zero_reference] at hd
  simp only [referenceReplicaMean_const_mul, integral_const_mul] at hd
  exact hd

/-- The diagonal Gaussian term is canceled by the actual `-h(top)/2`
normalization. This is the contact derivative, including zero and tied
field increments, before identifying the inserted field with `h+a*g`. -/
theorem tensorFieldInsertionMean_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt (tensorFieldInsertionMean μ eig c I degree amp n b treeDegree h g)
      (-tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  have hd := tensorFieldCGFMean_right_derivative hN μ eig c I degree amp n b treeDegree h g hg g0
  have hm := ((hd.div_const (N : ℝ)).const_add
    (tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree h)).fun_sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (g n)).div_const 2).hasDerivWithinAt
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N * g n - N * tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
      (fun _ => tensorFieldPairObservable g)) / 2 / N - 1 * g n / 2 =
      -tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2 := by
    field_simp
    ring
  rw [he] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  rfl


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the tensor pressure before varying its
linear field. Gaussian CGF bounds suffice; no concentration input is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma randomCoefficient_log_partition_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω → X → ℝ) (hH : Measurable (Function.uncurry H))
    (he : ∀ ω, Integrable (fun x => Real.exp (H ω x)) (ν ω))
    (hi : Integrable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) P)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hcap : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) :
    Integrable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1))
      (P.prod gaussianCoordinates) := by
  let η := fun ω => (ν ω).tilted (H ω)
  have : ∀ ω, IsProbabilityMeasure (η ω) := fun ω => isProbabilityMeasure_tilted (he ω)
  have hη : Measurable η := measurable_random_tilted_measure
    (ν := ν) (H := Function.uncurry H) hν hH
  let G := fun p : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A p.1 x) p.2) (η p.1) 1
  have hmG : Measurable G := measurable_randomCoefficient_cgf hη A hA 1
  have hiG : Integrable G (P.prod gaussianCoordinates) := integrable_randomCoefficient_cgf hη A hA hcap 1
  have hmC : Measurable (fun ω => Real.log (∫ x, Real.exp (H ω x) ∂ν ω)) :=
    (measurable_random_referencePartition hν hH).log
  have : ∀ p : Ω × (ℕ → ℝ), IsProbabilityMeasure ((ν ∘ Prod.fst) p) := fun p => by
    change IsProbabilityMeasure (ν p.1)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hHm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => H p.1.1 p.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hmF : Measurable (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) :=
    (measurable_random_referencePartition (hν.comp measurable_fst) (hHm.add hA)).log
  have hfold : (fun p : Ω × (ℕ → ℝ) => Real.log
      (∫ x, Real.exp (H p.1 x + cylinderField (A p.1 x) p.2) ∂ν p.1)) =ᵐ[P.prod gaussianCoordinates]
      (fun p => Real.log (∫ x, Real.exp (H p.1 x) ∂ν p.1) + G p) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmF ((hmC.comp measurable_fst).add hmG))).mpr
    exact ae_of_all _ fun ω => by
      have ht := cylinder_log_partition_base (ν ω) (H ω) (he ω) (A ω) (hcap ω) 1
      filter_upwards [ht] with z hz
      simpa only [one_mul, G, η, Pi.add_apply, Function.comp_apply] using hz
  exact ((hi.comp_fst gaussianCoordinates).add hiG).congr hfold.symm

lemma tensorDeterministicLog_eq {N n : ℕ} (eig c : Fin N → ℝ)
    (ω : SpecialOrthogonal N × LabeledTree n) :
    Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
      (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
      ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2) =
      logPartition (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ) := by
  unfold labeledSpinReference
  rw [integral_fun_fst (μ := (uniformSpinPrior N : Measure (Spin N)))
    (ν := labeledLeafLaw n ω.2) (fun σ => Real.exp (rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))]
  simp only [probReal_univ, one_smul]
  exact finiteLogIntegral_uniformSpinPrior _

lemma tensorDeterministicLog_abs_le {N : ℕ} (eig c : Fin N → ℝ)
    (U : Rotation N) :
    |logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)| ≤
      (∑ i, |eig i|) * N / 2 + ∑ i, |c i| := by
  have he (σ : Spin N) : |rotatedEnergy eig U σ| ≤ (∑ i, |eig i|) * N / 2 := by
    have ht := abs_rotatedEnergy_sub_le eig (fun _ => 0) U (∑ i, |eig i|)
      (fun i => by simpa only [sub_zero] using
        (Finset.single_le_sum (fun j _ => abs_nonneg (eig j)) (Finset.mem_univ i))) σ
    simpa only [rotatedEnergy, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero] using ht
  have hf (σ : Spin N) : |fieldEnergy c σ| ≤ ∑ i, |c i| := by
    simpa only [fieldEnergy, zero_mul, Finset.sum_const_zero, sub_zero] using
      abs_fieldEnergy_sub_le c (fun _ => 0) σ
  have ht := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ) (fun _ : Spin N => 0)
    ((∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    (fun σ => by simpa only [sub_zero] using (abs_add_le _ _).trans (add_le_add (he σ) (hf σ)))
  simpa only [logPartition_zero, sub_zero] using ht

lemma measurable_tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (Function.uncurry (tensorDeterministicEnergy eig c n)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add_const (fieldEnergy c x.1)

lemma tensorDeterministicLog_integrable {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (n : ℕ) (b : ℕ → ℝ) :
    Integrable (fun ω : SpecialOrthogonal N × LabeledTree n => Real.log
      (∫ x, Real.exp (tensorDeterministicEnergy eig c n ω x)
        ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2))
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  apply integrable_of_measurable_abs_le (c := (∑ i, |eig i|) * N / 2 + ∑ i, |c i|)
    ((measurable_random_referencePartition (ν := ν)
      (H := Function.uncurry (tensorDeterministicEnergy eig c n)) hν
        (measurable_tensorDeterministicEnergy eig c n)).log)
  intro ω
  change |Real.log (∫ x : Spin N × LabeledLeaf n, Real.exp
    (rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1)
    ∂labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)| ≤ _
  rw [tensorDeterministicLog_eq]
  exact tensorDeterministicLog_abs_le eig c (specialRotation ω.1)

lemma measurable_tensorNamespacedPathFields {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) :
    Measurable (fun p : (((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
        (Spin N × LabeledLeaf n)) =>
      cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1.1) I degree amp n
        (fun a => tensorPathProfile I degree n treeDegree h a) p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  let v : Fin (n + 1) → SpinTensorIndex I degree → NNReal :=
    fun a => tensorPathProfile I degree n treeDegree h a
  have hm : Measurable (fun p : TensorFlatDisorder N n => (p.1.1, p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hf := (measurable_tensorNamespacedFields_joint I degree amp n v x).comp hm
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem tensorNamespacedLog_integrable {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) :
    Integrable (tensorNamespacedLog eig c I degree amp n treeDegree h)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let ν := fun ω : SpecialOrthogonal N × LabeledTree n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_snd
  exact randomCoefficient_log_partition_integrable hν (tensorDeterministicEnergy eig c n)
    (measurable_tensorDeterministicEnergy eig c n)
    (fun ω => finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ + fieldEnergy c σ))
    (tensorDeterministicLog_integrable μ eig c n b)
    (fun ω => tensorNamespacedCoefficients (specialRotation ω.1) I degree amp n
      (fun a => tensorPathProfile I degree n treeDegree h a))
    (measurable_tensorNamespacedPathFields I degree amp n treeDegree h)
    (fun ω x => tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amp n treeDegree h hh h0 x)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing the linear field in a nonnegative monotone direction is
exactly an independent Gaussian insertion in the actual tensor model. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorNamespacedPath_field_add_cross {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (tensorNamespacedCoefficients U I degree amp n
      (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i) x)
      (tensorNamespacedCoefficients U I degree amp n
        (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i) y) =
      cylinderCross (tensorNamespacedCoefficients U I degree amp n
        (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (tensorNamespacedCoefficients U I degree amp n
          (fun i => tensorPathProfile I degree n treeDegree h i) y) +
        a * cylinderCross (tensorLinearCoefficients n g x) (tensorLinearCoefficients n g y) := by
  simp_rw [tensorNamespacedCoefficients_mixed_cross_eq]
  rw [tensorPathProfile_covariance U I degree amp n treeDegree _
      (monotone_field_add hh hg ha) (field_add_nonneg h0 g0 ha),
    tensorPathProfile_covariance U I degree amp n treeDegree h hh h0,
    tensorLinearCoefficients_cross n g hg g0]
  ring

lemma measurable_tensorFieldInsertedHamiltonian {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) :
    Measurable (Function.uncurry (tensorFieldInsertedHamiltonian eig c I degree amp n treeDegree h g a)) := by
  have hm : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      (p.1.1,p.2)) := measurable_fst.fst.prodMk measurable_snd
  have hM := (measurable_tensorNamespacedHamiltonian eig c I degree amp n treeDegree h).comp hm
  have hH : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      tensorNamespacedHamiltonian eig c I degree amp n treeDegree h p.1.1 p.2) := by
    convert hM using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hG : Measurable (fun p : (TensorFlatDisorder N n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      Real.sqrt a * cylinderField (tensorLinearCoefficients n g p.2) p.1.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hx : Measurable (fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
        cylinderField (tensorLinearCoefficients n g x) p.2) :=
      (measurable_cylinderField (tensorLinearCoefficients n g x)).comp measurable_snd
    exact hx.const_mul _
  exact hH.add hG

lemma measurable_tensorFieldInsertedLog {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ) (a : ℝ) :
    Measurable (tensorFieldInsertedLog eig c I degree amp n treeDegree h g a) := by
  let ν := fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.fst.snd
  have hm := (measurable_random_referencePartition hν
    (measurable_tensorFieldInsertedHamiltonian eig c I degree amp n treeDegree h g a)).log
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma tensorFieldInsertedLog_conditional_law {N m k n : ℕ} (eig c : Fin N → ℝ)
    (U : SpecialOrthogonal N) (T : LabeledTree n)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    (gaussianCoordinates.prod gaussianCoordinates).map (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a (((U,T),z.1),z.2)) =
      gaussianCoordinates.map (fun z => tensorNamespacedLog eig c I degree amp n treeDegree
        (fun i => h i + a * g i) ((U,T),z)) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n =>
    rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1
  let K := fun F : (Spin N × LabeledLeaf n → ℝ) => Real.log (∫ x, Real.exp (H x + F x) ∂ν)
  have : ∀ F : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) F) :=
    fun _ => by change IsProbabilityMeasure ν; infer_instance
  have hE : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) =>
      H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    have hx : Measurable (fun _ : Spin N × LabeledLeaf n → ℝ => H x) := measurable_const
    exact hx.add (measurable_pi_apply x)
  have hK : Measurable K := (measurable_random_referencePartition
    (ν := fun _ : Spin N × LabeledLeaf n → ℝ => ν) measurable_const hE).log
  let A : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorNamespacedCoefficients (specialRotation U) I degree amp n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  let B : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorLinearCoefficients n g
  let C : Spin N × LabeledLeaf n → ℕ →₀ ℝ := tensorNamespacedCoefficients (specialRotation U) I degree amp n
    (fun i => tensorPathProfile I degree n treeDegree (fun j => h j + a * g j) i)
  have hf : Measurable (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      fun x => cylinderField (A x) z.1 + Real.sqrt a * cylinderField (B x) z.2) :=
    Measurable.of_eval (fun x => ((measurable_cylinderField (A x)).comp measurable_fst).add
      (((measurable_cylinderField (B x)).comp measurable_snd).const_mul _))
  have hc : Measurable (fun z => fun x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  have he := cylinder_independent_sum_law A B C (Real.sqrt a) (fun x y => by
    rw [Real.sq_sqrt ha]
    exact tensorNamespacedPath_field_add_cross (specialRotation U) I degree amp n treeDegree h g hh h0 hg g0 a ha x y)
  have hl : (fun z : (ℕ → ℝ) × (ℕ → ℝ) =>
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a (((U,T),z.1),z.2)) =
      K ∘ (fun z => fun x => cylinderField (A x) z.1 + Real.sqrt a * cylinderField (B x) z.2) := by
    funext z
    apply congrArg Real.log
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    apply congrArg Real.exp
    dsimp [tensorNamespacedHamiltonian, H, A, B]
    ring
  change _ = gaussianCoordinates.map (K ∘ (fun z => fun x => cylinderField (C x) z))
  rw [hl, ← Measure.map_map hK hf, ← Measure.map_map hK hc, he]

private lemma tensorField_joint_map_eq_p0 {Ω A B E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure A) (R : Measure B) [SFinite Q] [SFinite R]
    (f : Ω × A → E) (g : Ω × B → E) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ ω, Q.map (fun z => f (ω,z)) = R.map (fun z => g (ω,z))) :
    (P.prod Q).map f = (P.prod R).map g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hg hs,
    Measure.prod_apply (hf hs), Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  refine ae_of_all _ fun ω => ?_
  have h := congrArg (fun ν : Measure E => ν s) (he ω)
  have hfω : Measurable (fun z => f (ω,z)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgω : Measurable (fun z => g (ω,z)) := hg.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hfω hs, Measure.map_apply hgω hs] at h
  exact h

theorem tensorFieldInsertedLog_identDistrib {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    IdentDistrib (tensorFieldInsertedLog eig c I degree amp n treeDegree h g a)
      (tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i))
      (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod gaussianCoordinates)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) := by
  let P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := fun p : (SpecialOrthogonal N × LabeledTree n) × ((ℕ → ℝ) × (ℕ → ℝ)) =>
    tensorFieldInsertedLog eig c I degree amp n treeDegree h g a ((p.1,p.2.1),p.2.2)
  let G := tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i)
  have hf : Measurable F := (measurable_tensorFieldInsertedLog eig c I degree amp n treeDegree h g a).comp
    MeasurableEquiv.prodAssoc.symm.measurable
  have hg' : Measurable G := measurable_tensorNamespacedLog eig c I degree amp n treeDegree _
  have he := tensorField_joint_map_eq_p0 P (gaussianCoordinates.prod gaussianCoordinates) gaussianCoordinates
    F G hf hg' (fun ω => tensorFieldInsertedLog_conditional_law eig c ω.1 ω.2 I degree amp treeDegree h g hh h0 hg g0 a ha)
  have hs := measurePreserving_prodAssoc P gaussianCoordinates gaussianCoordinates
  refine ⟨(measurable_tensorFieldInsertedLog eig c I degree amp n treeDegree h g a).aemeasurable,
    hg'.aemeasurable, ?_⟩
  change ((P.prod gaussianCoordinates).prod gaussianCoordinates).map
    (F ∘ (MeasurableEquiv.prodAssoc : ((SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)) ×
      (ℕ → ℝ) → (SpecialOrthogonal N × LabeledTree n) × ((ℕ → ℝ) × (ℕ → ℝ)))) =
      (P.prod gaussianCoordinates).map G
  rw [← Measure.map_map hf hs.measurable, hs.map_eq]
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual field-direction derivative used by the upper contact
argument. All Gaussian insertions and actual model means are identified. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorFieldInsertedLog_cgf_fold {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) (a : ℝ) :
    ∀ᵐ p : TensorFlatDisorder N n × (ℕ → ℝ)
      ∂(((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates).prod gaussianCoordinates),
      tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p =
        tensorNamespacedLog eig c I degree amp n treeDegree h p.1 +
          cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
            (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a) := by
  let ν := fun p : TensorFlatDisorder N n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p => by
    change IsProbabilityMeasure (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd
  have he := random_cgf_insertion_eq hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n treeDegree h)
    (tensorNamespaced_exp_integrable_ae μ eig c I degree amp n b treeDegree h hh h0)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le)
    (Real.sqrt a)
  filter_upwards [he] with p hp
  change cgf _ (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a) =
    tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p -
      tensorNamespacedLog eig c I degree amp n treeDegree h p.1 at hp
  linarith

theorem tensorNamespacedMeanPressure_field_insert {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0)
    (a : ℝ) (ha : 0 ≤ a) :
    tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree (fun i => h i + a * g i) =
      tensorFieldInsertionMean μ eig c I degree amp n b treeDegree h g a := by
  let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
  let F := tensorNamespacedLog eig c I degree amp n treeDegree h
  let C := fun p : TensorFlatDisorder N n × (ℕ → ℝ) =>
    cgf (fun x => cylinderField (tensorLinearCoefficients n g x) p.2)
      (tensorNamespacedReference eig c I degree amp n treeDegree h p.1) (Real.sqrt a)
  have hiF : Integrable F Q := tensorNamespacedLog_integrable μ eig c I degree amp n b treeDegree h hh h0
  have hiC : Integrable C (Q.prod gaussianCoordinates) := integrable_random_cylinder_cgf
    (measurable_tensorNamespacedReference eig c I degree amp n treeDegree h)
    (tensorLinearCoefficients n g) (fun x => (tensorLinearCoefficients_variance n g hg g0 x).le) (Real.sqrt a)
  have hmean : (∫ p, tensorNamespacedLog eig c I degree amp n treeDegree (fun i => h i + a * g i) p ∂Q) =
      (∫ p, F p ∂Q) + ∫ p, C p ∂Q.prod gaussianCoordinates := by
    calc
      _ = ∫ p, tensorFieldInsertedLog eig c I degree amp n treeDegree h g a p
          ∂Q.prod gaussianCoordinates :=
        (tensorFieldInsertedLog_identDistrib μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha).integral_eq.symm
      _ = ∫ p, F p.1 + C p ∂Q.prod gaussianCoordinates :=
        integral_congr_ae (tensorFieldInsertedLog_cgf_fold μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a)
      _ = (∫ p, F p.1 ∂Q.prod gaussianCoordinates) + ∫ p, C p ∂Q.prod gaussianCoordinates :=
        integral_add (hiF.comp_fst gaussianCoordinates) hiC
      _ = _ := by rw [integral_fun_fst F, probReal_univ, one_smul]
  unfold tensorFieldInsertionMean tensorNamespacedMeanPressure tensorNamespacedPressure tensorFieldCGFMean
  simp_rw [integral_const_mul]
  rw [hmean]
  change (N : ℝ)⁻¹ * ((∫ p, F p ∂Q) + ∫ p, C p ∂Q.prod gaussianCoordinates) -
      (h n + a * g n) / 2 =
    ((N : ℝ)⁻¹ * (∫ p, F p ∂Q) - h n / 2) +
      (∫ p, C p ∂Q.prod gaussianCoordinates) / N - a * g n / 2
  rw [div_eq_mul_inv (∫ p, C p ∂Q.prod gaussianCoordinates) (N : ℝ)]
  ring

/-- A nonnegative monotone field direction is feasible even when base
increments vanish or tie. The actual centered pressure has the stated
right derivative, with no concentration or path-law input. -/
theorem tensorNamespacedMeanPressure_field_right_derivative {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => tensorNamespacedMeanPressure μ eig c I degree amp n b treeDegree (fun i => h i + a * g i))
      (-tensorNamespacedReplicaAverage μ eig c I degree amp n b treeDegree h
        (fun _ => tensorFieldPairObservable g) / 2) (Ici 0) 0 := by
  apply (tensorFieldInsertionMean_right_derivative hN μ eig c I degree amp n b treeDegree h g hg g0).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact tensorNamespacedMeanPressure_field_insert μ eig c I degree amp n b treeDegree h g hh h0 hg g0 a ha
  · exact tensorNamespacedMeanPressure_field_insert μ eig c I degree amp n b treeDegree h g hh h0 hg g0 0 le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactField
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field-coordinate inequality at the actual joint minimum. Tied and
zero covariance levels are allowed; only the upper cap must be inactive. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContactFieldObjective_right_derivative {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ)
    (t : ℝ) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ) (h g : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hg : Monotone g) (g0 : 0 ≤ g 0) :
    HasDerivWithinAt
      (fun a => tensorContactFieldObjective μ eig c I u v t b w (fun i => h i + a * g i))
      (tensorNamespacedReplicaAverage μ (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        n b (fun j => enumeratedTreeDegree m j) h
        (fun _ => tensorFieldPairObservable g) / 2 - (∑ i, w i * g i) / 2) (Ici 0) 0 := by
  have hd := tensorNamespacedMeanPressure_field_right_derivative hN μ
    (diagonalPerturbedEigenvalues eig I v t) c I (fun j => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N u) n b (fun j => enumeratedTreeDegree m j) h g hh h0 hg g0
  have hs : HasDerivAt (fun a : ℝ => ∑ i : Fin (n + 1), w i * (h i + a * g i))
      (∑ i, w i * g i) 0 := by
    simpa only [one_mul, id_eq] using HasDerivAt.fun_sum
      (fun (i : Fin (n + 1)) (_ : i ∈ Finset.univ) =>
        (((hasDerivAt_id (0 : ℝ)).mul_const (g i)).const_add (h i)).const_mul (w i))
  convert! hd.fun_neg.fun_sub (hs.div_const 2).hasDerivWithinAt using 1
  all_goals try with_reducible_and_instances rfl
  simp only [neg_div, neg_neg]

theorem tensorContact_minimum_field_cone_oai {N m n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (b : ℕ → ℝ) (w : Fin (n + 1) → ℝ)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ) (p : TensorContactParameter N m n)
    (hp : p ∈ tensorContactRegion N m n H)
    (hmin : ∀ q ∈ tensorContactRegion N m n H,
      tensorContactObjective μ eig c I b w S V p ≤ tensorContactObjective μ eig c I b w S V q)
    (hcap : (∑ i, p.2.1 i) < H) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, w i * finiteFieldPath d i) ≤
      tensorNamespacedReplicaAverage μ (diagonalPerturbedEigenvalues eig I p.2.2.2 p.1) c I
        (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N p.2.2.1)
        n b (fun j => enumeratedTreeDegree m j) (finiteFieldPath p.2.1)
        (fun _ => tensorFieldPairObservable (finiteFieldPath d)) := by
  obtain ⟨ht, ha, hsum, hu, hv⟩ := tensorContactRegion_bounds hp
  have hder := tensorContactFieldObjective_right_derivative hN μ eig c I p.2.2.1 p.2.2.2
    p.1 b w (finiteFieldPath p.2.1) (finiteFieldPath d)
    (monotone_finiteFieldPath ha) (finiteFieldPath_nonneg ha 0)
    (monotone_finiteFieldPath hd) (finiteFieldPath_nonneg hd 0)
  have hfeas : ∀ᶠ a in 𝓝[>] (0 : ℝ), (∑ i, p.2.1 i) + a * (∑ i, d i) < H := by
    have hc : ContinuousAt (fun a : ℝ => (∑ i, p.2.1 i) + a * (∑ i, d i)) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa only [zero_mul, add_zero] using hcap))).filter_mono
      nhdsWithin_le_nhds
  have hnon := right_derivative_nonneg_of_min hder (by
    filter_upwards [hfeas, self_mem_nhdsWithin] with a hafeas ha0
    have hnew : (p.1, (fun i => p.2.1 i + a * d i), p.2.2.1, p.2.2.2) ∈
        tensorContactRegion N m n H := tensorContactRegion_mem ht
      (fun i => add_nonneg (ha i) (mul_nonneg ha0.le (hd i)))
      (by simpa only [Finset.sum_add_distrib, Finset.mul_sum] using hafeas.le) hu hv
    have hm := hmin _ hnew
    simp only [tensorContactObjective, tensorContactPressure, finiteFieldPath_add,
      finiteFieldPath_const_mul] at hm
    simp only [tensorContactFieldObjective, zero_mul, add_zero]
    linarith)
  linarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensorContact_minimum_field_cone_oai := @OAI.InvariantIsing.tensorContact_minimum_field_cone_oai
