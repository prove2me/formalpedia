-- Prove2me | solution 1 for OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:58:43.042192+00:00
-- url     : https://prove2.me/submissions/4a03ca07-507f-4e27-aee5-807ddb724690

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_IsingPerceptron_cascadeCoordinate_exp_integrable
import Theorems.Thm_OAI_IsingPerceptron_cascadeCoordinate_log_integral
import Theorems.Thm_OAI_IsingPerceptron_random_countable_cylinder_insertion

section
-- module Solutions.OAIQ258_II.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

end IsingPerceptron

end

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

lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

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

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

lemma finiteLogIntegral_add_const (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) (c : ℝ) :
    finiteLogIntegral ν (fun x => c+H x) = c+finiteLogIntegral ν H := by
  simp_rw [finiteLogIntegral_eq_logMean]
  exact logMean_const_add ν one_ne_zero (by simpa only [one_mul] using
    (Integrable.of_finite : Integrable (fun x => Real.exp (H x)) ν)) c

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

lemma energyRecursion_linearGrowth (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) : HasLinearGrowth (energyRecursion n b μ ν) :=
  cascadeRecursion_linearGrowth n b μ hμ (measurable_finiteLogIntegral ν)
    (finiteLogIntegral_linearGrowth ν) hb

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma labeledEnergyLog_eq_leaf (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (H : I → ℝ) (p : LabeledTree n × MarkForest (I → ℝ) n) :
    labeledEnergyLog n ν H p = Real.log (∫ γ,
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)) ∂labeledLeafLaw n p.1) := by
  have hE : Measurable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1)) :=
    measurable_of_countable _
  have hF : Measurable (fun γ : LabeledLeaf n => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H))) :=
    measurable_of_countable _
  unfold labeledEnergyLog labeledSpinReference
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hE.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hF.aestronglyMeasurable]
  congr 1
  rw [lintegral_prod _ hE.ennreal_ofReal.aemeasurable,
    lintegral_lintegral_swap hE.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro γ
  rw [finiteLogIntegral, Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)]
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm

end IsingPerceptron

namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_labeledEnergyLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] :
    Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
      labeledEnergyLog n ν p.1 p.2) := by
  let κ : Kernel ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) (LabeledLeaf n) :=
    ⟨fun p => labeledLeafLaw n p.2.1,(measurable_labeledLeafLaw n).comp (by fun_prop)⟩
  have : IsMarkovKernel κ := ⟨fun _ => labeledLeafLaw_probability _ _⟩
  have hm : Measurable (fun p : ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) × LabeledLeaf n =>
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.1.2.2 p.2 p.1.1))) := by
    apply measurable_swap_iff.mp
    apply measurable_from_prod_countable_right
    intro γ
    exact ((measurable_finiteLogIntegral ν).comp
      ((measurable_labeledEnergy n γ).comp
        (show Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
          (p.2.2,p.1)) from by fun_prop))).exp
  simpa only [labeledEnergyLog_eq_leaf, κ, Kernel.coe_mk] using
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.log

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma energyRecursion_add_const (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H : I → ℝ) (c : ℝ) :
    energyRecursion n b μ ν (fun x => c+H x) = c+energyRecursion n b μ ν H := by
  induction n generalizing b μ H with
  | zero => exact finiteLogIntegral_add_const ν H c
  | succ n ih =>
    change logMean (b 0) (μ 0 : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) ν
        ((fun x => c+H x)+a)) = c+logMean (b 0) (μ 0 : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) ν (H+a))
    have he (a : I → ℝ) : ((fun x => c+H x)+a) = fun x => c+(H+a) x := by
      ext x; simp only [Pi.add_apply] <;> ring
    simp_rw [he,ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))]
    apply logMean_const_add _ (hb 0 (by omega)).ne'
    exact integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
      ((measurable_energyRecursion n _ _ ν).comp (measurable_const.add measurable_id))
      ((energyRecursion_linearGrowth n _ _ ν (fun i hi => hμ (i+1) (by omega))
        (fun i hi => hb (i+1) (by omega))).add_left H) _


omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarShiftLaw_exponentialNormMoments (μ : ProbabilityMeasure (I → ℝ))
    (hμ : ExponentialNormMoments (μ : Measure (I → ℝ))) (v : ℝ≥0) :
    ExponentialNormMoments (scalarShiftLaw μ v : Measure (I → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  have hi := (hμ |a|).mul_prod (gaussianReal_exponentialNormMoments 0 v |a|)
  have hm : Measurable (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2) := by fun_prop
  apply hi.mono' ((hm.norm.const_mul a).exp.aestronglyMeasurable)
  apply ae_of_all
  rintro ⟨H,g⟩
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    a*‖fun x => H x+g‖ ≤ |a| *‖fun x => H x+g‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |a| *(‖H‖+‖g‖) := by
      gcongr
      exact (norm_add_le H (fun _ : I => g)).trans (add_le_add le_rfl ((pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr (fun _ => le_rfl)))
    _ = _ := by rw [Real.norm_eq_abs]; ring

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma logMean_scalarShift (μ : ProbabilityMeasure (I → ℝ)) (v : ℝ≥0)
    (r : ℝ) {F : (I → ℝ) → ℝ} (hFm : Measurable F)
    (hFi : Integrable (fun H => Real.exp (r*F H)) (μ : Measure (I → ℝ)))
    (hFc : ∀ H c, F (fun x => c+H x) = c+F H) (hr : r ≠ 0) :
    logMean r (scalarShiftLaw μ v : Measure (I → ℝ)) F =
      (v:ℝ)*r/2+logMean r (μ : Measure (I → ℝ)) F := by
  change Real.log (∫ p, Real.exp (r*F p) ∂((μ : Measure (I → ℝ)).prod (gaussianReal 0 v)).map
    (fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2))/r = _
  unfold logMean
  rw [integral_map (by fun_prop) ((hFm.const_mul r).exp).aestronglyMeasurable]
  have he (p : (I → ℝ) × ℝ) : Real.exp (r*F (fun x => p.1 x+p.2)) =
      Real.exp (r*F p.1)*Real.exp (r*p.2) := by
    rw [show (fun x => p.1 x+p.2) = (fun x => p.2+p.1 x) by ext x; ring,hFc]
    rw [mul_add,Real.exp_add,mul_comm]
  simp_rw [he]
  rw [integral_prod_mul (fun H : I → ℝ => Real.exp (r*F H)) (fun g : ℝ => Real.exp (r*g))]
  have hg : (∫ g : ℝ, Real.exp (r*g) ∂gaussianReal 0 v) = Real.exp ((v:ℝ)*r^2/2) := by
    simpa [mgf] using (congrFun (mgf_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)) r)
  rw [hg,Real.log_mul (integral_exp_pos (μ : Measure (I → ℝ)) F (b := r) hFi).ne' (Real.exp_ne_zero _),Real.log_exp]
  field_simp [hr]
  ring

 

theorem energyRecursion_scalarShift (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (v : ℕ → ℝ≥0) (H : I → ℝ) :
    energyRecursion n b (fun i => scalarShiftLaw (μ i) (v i)) ν H =
      (∑ i ∈ Finset.range n, b i*(v i:ℝ))/2+energyRecursion n b μ ν H := by
  induction n generalizing b μ v H with
  | zero => simp [energyRecursion,cascadeRecursion]
  | succ n ih =>
    let F : (I → ℝ) → ℝ := fun a => energyRecursion n (fun i => b (i+1))
      (fun i => μ (i+1)) ν (H+a)
    have hFm : Measurable F := (measurable_energyRecursion n _ _ ν).comp
      (measurable_const.add measurable_id)
    have hFg : HasLinearGrowth F := (energyRecursion_linearGrowth n _ _ ν
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))).add_left H
    have hFi : Integrable (fun a => Real.exp (b 0*F a)) (μ 0 : Measure (I → ℝ)) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega)) hFm hFg _
    have hFsi : Integrable (fun a => Real.exp (b 0*F a))
        (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ)) :=
      integrable_exp_of_linearGrowth _ (scalarShiftLaw_exponentialNormMoments _ (hμ 0 (by omega)) _)
        hFm hFg _
    have hFc (a : I → ℝ) (c : ℝ) : F (fun x => c+a x) = c+F a := by
      dsimp [F]
      rw [show H+(fun x => c+a x) = (fun x => c+(H+a) x) by ext x; simp [Pi.add_apply]; ring]
      exact energyRecursion_add_const _ _ _ ν (fun i hi => hμ (i+1) (by omega))
        (fun i hi => hb (i+1) (by omega)) _ _
    change logMean (b 0) (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ))
      (fun a => energyRecursion n (fun i => b (i+1))
        (fun i => scalarShiftLaw (μ (i+1)) (v (i+1))) ν (H+a)) = _
    simp_rw [ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega))]
    change logMean (b 0) (scalarShiftLaw (μ 0) (v 0) : Measure (I → ℝ))
      (fun a => (∑ i ∈ Finset.range n, b (i+1)*(v (i+1):ℝ))/2+F a) = _
    rw [logMean_const_add _ (hb 0 (by omega)).ne' hFsi,
      logMean_scalarShift _ _ _ hFm hFi hFc (hb 0 (by omega)).ne']
    change _ = (∑ i ∈ Finset.range (n+1), b i*(v i:ℝ))/2+
      logMean (b 0) (μ 0 : Measure (I → ℝ)) F
    rw [Finset.sum_range_succ']
    ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAddress_injective (n : ℕ) : Function.Injective (nodeAddress n) := by
  induction n with
  | zero =>
    intro v w _
    cases v with
    | none => cases w with
      | none => rfl
      | some w => exact w.elim
    | some v => exact v.elim
  | succ n ih =>
    intro v w h
    cases v with
    | none => cases w with
      | none => rfl
      | some w => simp [nodeAddress] at h
    | some v => cases w with
      | none => simp [nodeAddress] at h
      | some w =>
        rcases v with ⟨m,i,v⟩
        rcases w with ⟨m',i',w⟩
        simp only [nodeAddress,List.cons.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,h⟩
        rw [ih h]


lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)


lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

lemma labeledEnergy_edge_sum {I : Type} (n : ℕ) (g : ForestVertex n → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n g) γ H x =
      H x + ∑ i : Fin n, g (edgeAt n γ i) x := by
  induction n generalizing H with
  | zero => simp [labeledEnergy]
  | succ n ih =>
    rw [labeledEnergy,markForestOfCoords,ih,Fin.sum_univ_succ]
    simp only [edgeAt,nodeAt_zero,nodeAt_succ,Pi.add_apply]
    ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
namespace IsingPerceptron

lemma integral_comp_preserving_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have h := integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hF)
  rw [hf.map_eq] at h
  exact h.symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinateEnergy_eq (n : ℕ) (H : I → ℝ)
    (p : LabeledTree n × (ForestVertex n → I → ℝ)) (s : I × LabeledLeaf n) :
    cascadeCoordinateEnergy n H p s = labeledEnergy n (markForestOfCoords (I → ℝ) n p.2) s.2 H s.1 :=
  (labeledEnergy_edge_sum n p.2 s.2 H s.1).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







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
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarShiftLaw_amplitude (μ : ProbabilityMeasure (I → ℝ)) (t : ℝ) :
    ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1)).map
      (fun p : (I → ℝ) × ℝ => fun x => p.1 x+t*p.2) =
      (scalarShiftLaw μ (NNReal.mk (t^2) (sq_nonneg t)) : Measure (I → ℝ)) := by
  have hp : MeasurePreserving (fun p : (I → ℝ) × ℝ => (p.1,t*p.2))
      ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1))
      ((μ : Measure (I → ℝ)).prod (gaussianReal 0 (NNReal.mk (t^2) (sq_nonneg t)))) :=
    (MeasurePreserving.id _).prod ⟨by fun_prop,by simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) t⟩
  change ((μ : Measure (I → ℝ)).prod (gaussianReal 0 1)).map
    ((fun p : (I → ℝ) × ℝ => fun x => p.1 x+p.2) ∘ (fun p => (p.1,t*p.2))) = _
  rw [← Measure.map_map (by fun_prop) hp.measurable,hp.map_eq]
  rfl

lemma edgeGaussianTag_injective (n : ℕ) : Function.Injective (edgeGaussianTag n) := by
  intro v w h
  exact Option.some.inj (nodeAddress_injective n (Encodable.encode_inj.mp h))

lemma edgeGaussianCoordinates_preserving (n : ℕ) :
    MeasurePreserving (edgeGaussianCoordinates n) gaussianCoordinates
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)) :=
  gaussian_pullback_measurePreserving (edgeGaussianTag n) (edgeGaussianTag_injective n)



omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma scalarCoordinateInsert_preserving (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (a : ℕ → ℝ) :
    MeasurePreserving (scalarCoordinateInsert n a) ((cascadeCoordinateLaw n b μ).prod gaussianCoordinates)
      (cascadeCoordinateLaw n b (fun i => scalarShiftLaw (μ i) (NNReal.mk (a i^2) (sq_nonneg _)))) := by
  let P := Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure (I → ℝ)))
  let Q := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)
  have hp : MeasurePreserving (fun p : (ForestVertex n → I → ℝ) × (ForestVertex n → ℝ) =>
      fun v => (p.1 v,p.2 v)) (P.prod Q)
      (Measure.infinitePi (fun v : ForestVertex n =>
        (μ (forestVertexDepth n v) : Measure (I → ℝ)).prod (gaussianReal 0 1))) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hs : MeasurePreserving (fun p : ForestVertex n → (I → ℝ) × ℝ =>
      fun v x => (p v).1 x+a (forestVertexDepth n v)*(p v).2)
      (Measure.infinitePi (fun v : ForestVertex n =>
        (μ (forestVertexDepth n v) : Measure (I → ℝ)).prod (gaussianReal 0 1)))
      (Measure.infinitePi (fun v : ForestVertex n =>
        (scalarShiftLaw (μ (forestVertexDepth n v)) (NNReal.mk (a (forestVertexDepth n v)^2) (sq_nonneg _)) : Measure (I → ℝ)))) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.infinitePi_map_pi (f := fun v (p : (I → ℝ) × ℝ) =>
      fun x => p.1 x+a (forestVertexDepth n v)*p.2) _ (fun _ => by fun_prop)]
    congr 1
    funext v
    exact scalarShiftLaw_amplitude _ _
  have hq := (hs.comp hp).comp ((MeasurePreserving.id P).prod (edgeGaussianCoordinates_preserving n))
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) →
      LabeledTree n × ((ForestVertex n → I → ℝ) × (ℕ → ℝ)))
      ((cascadeCoordinateLaw n b μ).prod gaussianCoordinates)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (P.prod gaussianCoordinates)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  exact ((MeasurePreserving.id _).prod hq).comp ha

lemma forestVertexDepth_edgeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n γ i) = i := by
  have h := nodeAddress_nodeAt_length n γ i.succ
  rw [nodeAt_succ,nodeAddress_length_some] at h
  exact Nat.add_right_cancel h

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma cascadeCoordinateEnergy_insert (n : ℕ) (d : Fin n) (t : ℝ) (H : I → ℝ)
    (p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ)) (s : I × LabeledLeaf n) :
    cascadeCoordinateEnergy n H (scalarCoordinateInsert n (fun i => if i = d then t else 0) p) s =
      cascadeCoordinateEnergy n H p.1 s+t*cylinderField (labelLevelCoefficients n d s) p.2 := by
  classical
  simp only [cascadeCoordinateEnergy,scalarCoordinateInsert,Finset.sum_add_distrib,
    forestVertexDepth_edgeAt]
  have he : (∑ i : Fin n, (if (i:ℕ) = d then t else 0)*edgeGaussianCoordinates n p.2 (edgeAt n s.2 i)) =
      t*edgeGaussianCoordinates n p.2 (edgeAt n s.2 d) := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro i _ hi; rw [ite_eq_right (by intro h; exact hi (Fin.ext h)),zero_mul]
    · simp
  rw [he,labelLevelCoefficients,cylinderField,Finsupp.sum_single_index (by simp),one_mul]
  dsimp only [edgeGaussianCoordinates]
  ring

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_diag (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) :
    cylinderCross (labelLevelCoefficients n d s) (labelLevelCoefficients n d s) = 1 := by
  simp [labelLevelCoefficients,cylinderCross_single_left]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_bound (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) :
    (labelLevelCoefficients n d s).sum (fun _ c => c^2) ≤ 1 := by
  simp [labelLevelCoefficients,Finsupp.sum_single_index]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_cross (n : ℕ) (d : Fin n) (s t : I × LabeledLeaf n) :
    cylinderCross (labelLevelCoefficients n d s) (labelLevelCoefficients n d t) =
      if (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) then 1 else 0 := by
  classical
  have he : edgeGaussianTag n (edgeAt n t.2 d) = edgeGaussianTag n (edgeAt n s.2 d) ↔
      (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) := by
    rw [edgeGaussianTag,edgeGaussianTag,Encodable.encode_inj,← nodeAt_succ,← nodeAt_succ,
      nodeAddress_nodeAt,nodeAddress_nodeAt]
    exact eq_comm
  simp only [labelLevelCoefficients,cylinderCross_single_left,one_mul,Finsupp.single_apply,he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma referenceReplicaMean_fold {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H G : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (heg : Integrable (fun x => Real.exp (H x+G x)) ν)
    {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean (gibbsProbability ν H) G D =
      referenceReplicaMean ν (fun x => H x+G x) D := by
  rw [gibbsProbability_eq_tilted ν H he]
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hg : Integrable (fun x => Real.exp (G x)) (ν.tilted H) := by
    rw [integrable_tilted_iff he]
    simpa only [smul_eq_mul,← Real.exp_add] using heg
  rw [referenceReplicaMean_eq_tilted _ _ hg,referenceReplicaMean_eq_tilted _ _ heg,
    tilted_tilted he]
  rfl

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma randomReplicaAverage_zero_fold {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : Ω → Measure X)
    [∀ ω, IsProbabilityMeasure (ν ω)] (H : Ω → X → ℝ)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H ω x)) (ν ω))
    (b : X → ℕ →₀ ℝ) {m : ℕ} (D : (Fin m → X) → ℝ) :
    randomReplicaAverage P (fun ω => gibbsProbability (ν ω) (H ω)) b 0 D =
      ∫ ω, referenceReplicaMean (ν ω) (H ω) D ∂P := by
  unfold randomReplicaAverage
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  calc
    _ = ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (H z.1) D ∂P.prod gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [he'] with z hz
      simp only [zero_mul]
      simpa only [add_zero] using referenceReplicaMean_fold (ν z.1) (H z.1) (fun _ => 0) hz (by simpa using hz) D
    _ = _ := by rw [integral_fun_fst (fun ω => referenceReplicaMean (ν ω) (H ω) D),probReal_univ,one_smul]



end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply
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
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_cascadeCoordinateEnergy (n : ℕ) (H : I → ℝ) :
    Measurable (fun p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (I × LabeledLeaf n) =>
      cascadeCoordinateEnergy n H p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  change Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
    H s.1+∑ i : Fin n, p.2 (edgeAt n s.2 i) s.1)
  apply measurable_const.add
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply s.1).comp ((measurable_pi_apply (edgeAt n s.2 i)).comp measurable_snd)

lemma measurable_cascadeCoordinateLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) :
    Measurable (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
        ∂labeledSpinReference n ν p.1)) := by
  simpa only [Function.comp_def,labeledEnergyLog,← cascadeCoordinateEnergy_eq] using
    (measurable_labeledEnergyLog n ν).comp
      (show Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
        (H,(p.1,markForestOfCoords (I → ℝ) n p.2))) from by fun_prop)

lemma scalarCoordinate_cgf_eq_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (d : Fin n) (t : ℝ) :
    (fun p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ) =>
      cgf (fun s => cylinderField (labelLevelCoefficients n d s) p.2)
        (gibbsProbability (labeledSpinReference n ν p.1.1) (cascadeCoordinateEnergy n H p.1)) t)
      =ᵐ[(cascadeCoordinateLaw n b μ).prod gaussianCoordinates]
      (fun p => cascadeCoordinateLog n ν H
        (scalarCoordinateInsert n (fun i => if i = (d:ℕ) then t else 0) p)-cascadeCoordinateLog n ν H p.1) := by
  classical
  have hν : Measurable (fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1) :=
    (measurable_labeledSpinReference_general n ν).comp measurable_fst
  have he := random_cgf_insertion_eq (P := cascadeCoordinateLaw n b μ) hν
    (measurable_cascadeCoordinateEnergy n H) (cascadeCoordinate_exp_integrable n b hb μ ν hμ H)
    (labelLevelCoefficients n d) (labelLevelCoefficients_bound n d) t
  filter_upwards [he] with p he
  dsimp only [cascadeCoordinateLog]
  simp_rw [cascadeCoordinateEnergy_insert]
  exact he

lemma scalarCoordinate_log_difference_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (a : ℕ → ℝ) :
    (∫ p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ),
      cascadeCoordinateLog n ν H (scalarCoordinateInsert n a p)-cascadeCoordinateLog n ν H p.1
      ∂(cascadeCoordinateLaw n b μ).prod gaussianCoordinates) =
      (∑ i ∈ Finset.range n, b i*a i^2)/2 := by
  let μ' : ℕ → ProbabilityMeasure (I → ℝ) := fun i => scalarShiftLaw (μ i) (NNReal.mk (a i^2) (sq_nonneg _))
  have hL := cascadeCoordinate_log_integral n b hb μ ν hμ H
  have hL' := cascadeCoordinate_log_integral n b hb μ' ν
    (fun i hi => scalarShiftLaw_exponentialNormMoments _ (hμ i hi) _) H
  have hp := scalarCoordinateInsert_preserving n b μ a
  have hi := hp.integrable_comp_of_integrable hL'.1
  have hj := hL.1.comp_fst gaussianCoordinates
  simp only [Function.comp_def] at hi
  unfold cascadeCoordinateLog
  rw [integral_sub hi hj]
  rw [integral_comp_preserving_ae hp (measurable_cascadeCoordinateLog n ν H).aestronglyMeasurable,
    integral_fun_fst (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s) ∂labeledSpinReference n ν p.1)),probReal_univ,one_smul]
  rw [hL'.2,hL.2]
  rw [energyRecursion_scalarShift n b μ ν hμ (fun i hi => (hb.1 i hi).1)]
  simp only [NNReal.coe_mk]
  ring

lemma scalarCoordinate_cgf_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ)
    (d : Fin n) {v : ℝ} (hv : 0 ≤ v) :
    (∫ p : (LabeledTree n × (ForestVertex n → I → ℝ)) × (ℕ → ℝ),
      cgf (fun s => cylinderField (labelLevelCoefficients n d s) p.2)
        (gibbsProbability (labeledSpinReference n ν p.1.1) (cascadeCoordinateEnergy n H p.1)) (Real.sqrt v)
      ∂(cascadeCoordinateLaw n b μ).prod gaussianCoordinates) = b d*v/2 := by
  classical
  rw [integral_congr_ae (scalarCoordinate_cgf_eq_ae n b hb μ ν hμ H d (Real.sqrt v)),
    scalarCoordinate_log_difference_mean n b hb μ ν hμ H]
  congr 1
  rw [Finset.sum_eq_single (d:ℕ)]
  · simp [Real.sq_sqrt hv]
  · intro i _ hi; simp [hi]
  · simp [d.isLt]

theorem cascadeCoordinate_tilted_label_tail (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) (d : Fin n) :
    (∫ p, referenceReplicaMean (labeledSpinReference n ν p.1) (cascadeCoordinateEnergy n H p)
      (fun σ : Fin 2 → I × LabeledLeaf n =>
        if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1)
        then 1 else 0) ∂cascadeCoordinateLaw n b μ) = 1-b d := by
  let η := fun p : LabeledTree n × (ForestVertex n → I → ℝ) =>
    gibbsProbability (labeledSpinReference n ν p.1) (cascadeCoordinateEnergy n H p)
  have hm : Measurable η := measurable_gibbsProbability
    (ν := fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1)
    ((measurable_labeledSpinReference_general n ν).comp measurable_fst)
    (measurable_cascadeCoordinateEnergy n H)
  have hd := hasDerivWithinAt_random_cylinder_variance (P := cascadeCoordinateLaw n b μ) hm
    (labelLevelCoefficients n d) (labelLevelCoefficients_bound n d) (labelLevelCoefficients_diag n d)
    (v := 0) (by norm_num)
  have hlin : HasDerivWithinAt (fun v : ℝ => b d*v/2) (b d/2) (Ici 0) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul (b d)).div_const 2).hasDerivWithinAt (s := Ici 0)
  have hde : HasDerivWithinAt (fun v : ℝ => b d*v/2)
      ((1-randomReplicaAverage (cascadeCoordinateLaw n b μ) η (labelLevelCoefficients n d) 0
        (fun σ : Fin 2 → I × LabeledLeaf n => cylinderCross
          (labelLevelCoefficients n d (σ 1)) (labelLevelCoefficients n d (σ 0))))/2) (Ici 0) 0 := by
    simp only [Real.sqrt_zero] at hd
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact (scalarCoordinate_cgf_mean n b hb μ ν hμ H d hv).symm
    · exact (scalarCoordinate_cgf_mean n b hb μ ν hμ H d (v := 0) (by norm_num)).symm
  have he := (hde.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))).symm.trans
    (hlin.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ)))
  have hf := randomReplicaAverage_zero_fold (P := cascadeCoordinateLaw n b μ)
    (fun p : LabeledTree n × (ForestVertex n → I → ℝ) => labeledSpinReference n ν p.1)
    (cascadeCoordinateEnergy n H) (cascadeCoordinate_exp_integrable n b hb μ ν hμ H)
    (labelLevelCoefficients n d)
    (fun σ : Fin 2 → I × LabeledLeaf n => cylinderCross
      (labelLevelCoefficients n d (σ 1)) (labelLevelCoefficients n d (σ 0)))
  change randomReplicaAverage (cascadeCoordinateLaw n b μ) η _ _ _ = _ at hf
  rw [hf] at he
  simp only [labelLevelCoefficients_cross] at he
  linarith

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorCascade
attribute [-instance] _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorCoordinateLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability
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

lemma tensorGaussianLaw_moments {N m k : ℕ} (hN : 0 < N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ)) := by
  let : Nonempty (SpinTensorIndex I degree) := ⟨Sum.inl ⟨0, hN⟩⟩
  have hm := IsingPerceptron.finite_gaussian_exponentialNormMoments
    (P := Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i)))
    (X := fun z : SpinTensorIndex I degree → ℝ => z) measurable_id (fun _ => 0) v
    (fun i => (measurePreserving_eval (fun j : SpinTensorIndex I degree => gaussianReal 0 (v j)) i).map_eq)
  change IsingPerceptron.ExponentialNormMoments
    ((Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i))).map id) at hm
  rw [Measure.map_id] at hm
  exact hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorLabeled
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma spinTensorEnergyMark_norm_le {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (z : SpinTensorIndex I degree → ℝ) :
    ‖spinTensorEnergy U I degree amplitude z‖ ≤
      (∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
        |spinTensorFeature U I degree amplitude σ i|) * ‖z‖ := by
  classical
  let L : ℝ := ∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
    |spinTensorFeature U I degree amplitude σ i|
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg z))).mpr
  intro σ
  rw [Real.norm_eq_abs]
  have hσ : (∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude σ i|) ≤ L := by
    apply Finset.single_le_sum (f := fun τ : Spin N =>
      ∑ i : SpinTensorIndex I degree, |spinTensorFeature U I degree amplitude τ i|)
    · exact fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact Finset.mem_univ σ
  calc
    _ ≤ ∑ i, |z i * spinTensorFeature U I degree amplitude σ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖z‖ * |spinTensorFeature U I degree amplitude σ i| :=
      Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
          (abs_nonneg _)
    _ = ‖z‖ * ∑ i, |spinTensorFeature U I degree amplitude σ i| := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖z‖ * L := mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
    _ = _ := mul_comm _ _

lemma tensorEnergyMarkLaw_moments {N m k : ℕ} (hN : 0 < N) (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    IsingPerceptron.ExponentialNormMoments (tensorEnergyMarkLaw U I degree amplitude v :
      Measure (Spin N → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop)
    (measurable_spinTensorEnergyMark U I degree amplitude).aemeasurable).mpr
  let L : ℝ := ∑ σ : Spin N, ∑ i : SpinTensorIndex I degree,
    |spinTensorFeature U I degree amplitude σ i|
  have hi := tensorGaussianLaw_moments hN I degree v (|a| * L)
  apply hi.mono' (((measurable_spinTensorEnergyMark U I degree amplitude).norm.const_mul a).exp.aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      a * ‖spinTensorEnergy U I degree amplitude z‖ ≤ |a| * ‖spinTensorEnergy U I degree amplitude z‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |a| * (L * ‖z‖) := mul_le_mul_of_nonneg_left
        (spinTensorEnergyMark_norm_le U I degree amplitude z) (abs_nonneg _)
      _ = _ := by ring

theorem tensorEnergyCoordinates_measurePreserving {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorEnergyCoordinates U I degree amplitude n)
      (tensorCoordinateLaw I degree n b v) (tensorLabeledLaw U I degree amplitude n b v) := by
  have hmark : MeasurePreserving
      (fun z : IsingPerceptron.ForestVertex n → SpinTensorIndex I degree → ℝ =>
        fun w => spinTensorEnergy U I degree amplitude (z w))
      (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
        (tensorGaussianLaw I degree (v (IsingPerceptron.forestVertexDepth n w)) :
          Measure (SpinTensorIndex I degree → ℝ))))
      (Measure.infinitePi (fun w : IsingPerceptron.ForestVertex n =>
        (tensorEnergyMarkLaw U I degree amplitude (v (IsingPerceptron.forestVertexDepth n w)) :
          Measure (Spin N → ℝ)))) := by
    refine ⟨Measurable.of_eval (fun w =>
      (measurable_spinTensorEnergyMark U I degree amplitude).comp (measurable_pi_apply w)), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_spinTensorEnergyMark U I degree amplitude)]
    rfl
  convert (MeasurePreserving.id (IsingPerceptron.labeledCascadeLaw n b :
    Measure (IsingPerceptron.LabeledTree n))).prod hmark using 1
  all_goals try with_reducible_and_instances rfl
  all_goals rfl

lemma measurable_tensorLabeledEnergy_root {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) :
    Measurable (fun p : ((SpinTensorIndex I degree → ℝ) × TensorLabeledData N n) ×
        TensorLabeledState N n => tensorLabeledEnergy eig U c I degree amplitude n p.1.1 p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  change Measurable (fun p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    tensorSpinBaseEnergy eig U c I degree amplitude p.1 s.1 +
      ∑ i : Fin n, p.2.2 (IsingPerceptron.edgeAt n s.2 i) s.1)
  unfold tensorSpinBaseEnergy spinTensorEnergy
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_NSpinTensorGaussianLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat countable Gaussian field has the actual root/forest mark law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma tensorNodeTag_injective {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × SpinTensorIndex I degree =>
      tensorNodeTag I degree n p.1 p.2) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have he := Encodable.encode_inj.mp h
  exact Prod.ext (nodeAddress_injective n (congrArg (fun p => p.2.1) he))
    (congrArg (fun p => p.2.2) he)

lemma tensorNodeTag_nodeAt {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (leaf : LabeledLeaf n)
    (level : Fin (n + 1)) (i : SpinTensorIndex I degree) :
    tensorNodeTag I degree n (nodeAt n leaf level) i = treeFeatureTag n leaf (level, i) := by
  unfold tensorNodeTag treeFeatureTag
  rw [nodeAddress_nodeAt_length, nodeAddress_nodeAt]

lemma measurable_tensorStandardGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) : Measurable (tensorStandardGaussianNodes I degree n) := by
  unfold tensorStandardGaussianNodes
  fun_prop

theorem tensorStandardGaussianNodes_law {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) :
    gaussianCoordinates.map (tensorStandardGaussianNodes I degree n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)) := by
  let t := fun p : Option (ForestVertex n) × SpinTensorIndex I degree => tensorNodeTag I degree n p.1 p.2
  have hp := gaussian_pullback_measurePreserving t (tensorNodeTag_injective I degree n)
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (SpinTensorIndex I degree) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable, hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : SpinTensorIndex I degree) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

private theorem tensorMarkScale_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (v : SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun z : SpinTensorIndex I degree → ℝ => fun i => (NNReal.sqrt (v i) : ℝ) * z i)
      (Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))
      (tensorGaussianLaw I degree v : Measure (SpinTensorIndex I degree → ℝ)) := by
  change MeasurePreserving _ _ (Measure.pi (fun i : SpinTensorIndex I degree => gaussianReal 0 (v i)))
  apply measurePreserving_pi
  intro i
  refine ⟨by fun_prop, ?_⟩
  have hs : NNReal.mk ((NNReal.sqrt (v i) : ℝ) ^ 2) (sq_nonneg _) = v i := by
    apply Subtype.ext
    change (NNReal.sqrt (v i) : ℝ) ^ 2 = (v i : ℝ)
    exact_mod_cast NNReal.sq_sqrt (v i)
  simpa only [hs, mul_zero, mul_one] using
    gaussianReal_map_const_mul (μ := 0) (v := 1) (NNReal.sqrt (v i) : ℝ)

lemma measurable_tensorGaussianNodes {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    Measurable (tensorGaussianNodes I degree n v) := by
  unfold tensorGaussianNodes tensorStandardGaussianNodes
  fun_prop

theorem tensorGaussianNodes_measurePreserving {N m k : ℕ} (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorGaussianNodes I degree n v) gaussianCoordinates
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
  have hstd : MeasurePreserving (tensorStandardGaussianNodes I degree n) gaussianCoordinates
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1))) :=
    ⟨measurable_tensorStandardGaussianNodes I degree n, tensorStandardGaussianNodes_law I degree n⟩
  have hscale : MeasurePreserving
      (fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
        fun w i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * q w i)
      (Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : SpinTensorIndex I degree => gaussianReal 0 1)))
      (Measure.infinitePi (fun w : Option (ForestVertex n) =>
        (tensorGaussianLaw I degree (v (nodeAddress n w).length) : Measure (SpinTensorIndex I degree → ℝ)))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.infinitePi_map_pi (f := fun w (z : SpinTensorIndex I degree → ℝ) =>
      fun i => (NNReal.sqrt (v (nodeAddress n w).length i) : ℝ) * z i) _ (fun _ => by fun_prop)]
    apply congrArg Measure.infinitePi
    funext w
    exact (tensorMarkScale_measurePreserving I degree (v (nodeAddress n w).length)).map_eq
  exact hscale.comp hstd

/-- The root and all forest coordinates have their independent prescribed
Gaussian laws, including zero variances. -/
theorem tensorGaussianRootForest_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (fun g => (tensorGaussianNodes I degree n v g none,
      fun w => tensorGaussianNodes I degree n v g (some w))) gaussianCoordinates
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (Measure.infinitePi (fun w : ForestVertex n =>
          (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
            Measure (SpinTensorIndex I degree → ℝ))))) := by
  refine ⟨by unfold tensorGaussianNodes tensorStandardGaussianNodes; fun_prop, ?_⟩
  change gaussianCoordinates.map ((fun q : Option (ForestVertex n) → SpinTensorIndex I degree → ℝ =>
      (q none, fun w => q (some w))) ∘ tensorGaussianNodes I degree n v) = _
  rw [← Measure.map_map (by fun_prop) (measurable_tensorGaussianNodes I degree n v),
    (tensorGaussianNodes_measurePreserving I degree n v).map_eq]
  have he := infinitePi_option_split
    (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
    (fun w : ForestVertex n => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
      Measure (SpinTensorIndex I degree → ℝ)))
  have hc : (fun w : Option (ForestVertex n) => w.elim
      (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
      (fun w => (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) :
        Measure (SpinTensorIndex I degree → ℝ)))) =
      (fun w => (tensorGaussianLaw I degree (v (nodeAddress n w).length) :
        Measure (SpinTensorIndex I degree → ℝ))) := by
    funext w
    cases w with
    | none => cases n <;> rfl
    | some w => simp only [Option.elim_some, nodeAddress_length_some]
  simpa only [hc] using he

lemma cylinderField_tensorLeaf_nodes {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (σ : Spin N) (leaf : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      spinTensorEnergy U I degree amplitude (tensorGaussianNodes I degree n v g none) σ +
      ∑ i : Fin n, spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (some (edgeAt n leaf i))) σ := by
  classical
  have he : cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) (σ, leaf)) g =
      ∑ i : Fin (n + 1), spinTensorEnergy U I degree amplitude
        (tensorGaussianNodes I degree n v g (nodeAt n leaf i)) σ := by
    rw [tensorLeafCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    unfold spinTensorEnergy tensorGaussianNodes tensorStandardGaussianNodes
    rw [nodeAddress_nodeAt_length]
    apply Finset.sum_congr rfl
    intro j _
    rw [tensorNodeTag_nodeAt]
    ring
  rw [he, Fin.sum_univ_succ]
  simp only [nodeAt_zero, nodeAt_succ]

theorem tensorFlatToCoordinates_measurePreserving {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToCoordinates I degree n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorCoordinateLaw I degree n b (fun i => v (i + 1)))) := by
  let R := (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))
  let T := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let F := Measure.infinitePi (fun w : ForestVertex n =>
    (tensorGaussianLaw I degree (v (forestVertexDepth n w + 1)) : Measure (SpinTensorIndex I degree → ℝ)))
  have hswap : MeasurePreserving Prod.swap (T.prod R) (R.prod T) := Measure.measurePreserving_swap
  have hshuffle := (measurePreserving_prodAssoc R T F).comp
    ((hswap.prod (MeasurePreserving.id F)).comp
      ((measurePreserving_prodAssoc T R F).symm MeasurableEquiv.prodAssoc))
  have hprod := (MeasurePreserving.id T).prod (tensorGaussianRootForest_measurePreserving I degree n v)
  convert hshuffle.comp hprod using 1
  all_goals try with_reducible_and_instances rfl
  all_goals rfl

/-- The flat Gaussian spin/leaf model is exactly the independent Gaussian
root and tensor-energy forest model used by the cascade recursion. -/
theorem tensorFlatToLabeled_measurePreserving {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0) :
    MeasurePreserving (tensorFlatToLabeled U I degree amplitude n v)
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates)
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorLabeledLaw U I degree amplitude n b (fun i => v (i + 1)))) := by
  have h := ((MeasurePreserving.id
    (tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ))).prod
      (tensorEnergyCoordinates_measurePreserving U I degree amplitude n b (fun i => v (i + 1)))).comp
    (tensorFlatToCoordinates_measurePreserving I degree n b v)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals rfl

theorem tensorLabeledEnergy_flat_eq {N m k : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (p : LabeledTree n × (ℕ → ℝ)) (x : Spin N × LabeledLeaf n) :
    let q := tensorFlatToLabeled U I degree amplitude n v p
    tensorLabeledEnergy eig U c I degree amplitude n q.1 q.2 x =
      rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorLeafCoefficients U I degree amplitude n (fun i => v i) x) p.2 := by
  rw [cylinderField_tensorLeaf_nodes]
  dsimp only [tensorFlatToLabeled, tensorFlatToCoordinates, tensorLabeledEnergy,
    cascadeCoordinateEnergy, tensorSpinBaseEnergy, tensorEnergyCoordinates]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar prefix test in the actual finite tensor model. The root is
averaged after the cascade marking identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal

namespace InvariantIsing

lemma tensorLeafPrefixTest_abs_le {N n : ℕ} (d : Fin n)
    (σ : Fin 2 → Spin N × LabeledLeaf n) : |tensorLeafPrefixTest d σ| ≤ 1 := by
  unfold tensorLeafPrefixTest
  split_ifs <;> norm_num

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorLeafTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cascade prefix law retains an arbitrary deterministic spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal
namespace InvariantIsing

lemma measurable_spinPriorLabeledReference {N : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (n : ℕ) : Measurable (spinPriorLabeledReference π n) :=
  (measurable_labeledSpinReference_general n π).comp measurable_fst

lemma spinPriorLabeled_tilted_parent_tail {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (z : SpinTensorIndex I degree → ℝ) (d : Fin n) :
    (∫ p, referenceReplicaMean (spinPriorLabeledReference π n p)
      (tensorLabeledEnergy eig U c I degree amp n z p) (tensorLeafPrefixTest d)
      ∂tensorLabeledLaw U I degree amp n b v) = 1 - b d :=
  cascadeCoordinate_tilted_label_tail n b hb
    (fun i => tensorEnergyMarkLaw U I degree amp (v i)) π
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amp (v i)) _ d

lemma spinPriorFlat_leafPrefix_mean_oai {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d : Fin n) :
    (∫ p : LabeledTree n × (ℕ → ℝ),
      referenceReplicaMean (labeledSpinReference n π p.1)
        (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
          cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
        (tensorLeafPrefixTest d)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) = 1 - b d := by
  let F := fun p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n =>
    referenceReplicaMean (spinPriorLabeledReference π n p.2)
      (tensorLabeledEnergy eig U c I degree amp n p.1 p.2) (tensorLeafPrefixTest d)
  have : ∀ p : (SpinTensorIndex I degree → ℝ) × TensorLabeledData N n,
      IsProbabilityMeasure ((spinPriorLabeledReference π n ∘ Prod.snd) p) := fun p => by
    dsimp only [Function.comp_apply]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hF : Measurable F := measurable_random_referenceReplicaMean
    ((measurable_spinPriorLabeledReference π n).comp measurable_snd)
    (measurable_tensorLabeledEnergy_root eig U c I degree amp n)
    ((measurable_of_countable (tensorLeafPrefixTest (N := N) d)).comp measurable_snd)
  have hFb p : |F p| ≤ 1 := referenceReplicaMean_abs_le _ _ _
    (measurable_of_countable _) zero_le_one (tensorLeafPrefixTest_abs_le d)
  have hi : Integrable F
      ((tensorGaussianLaw I degree (v 0) : Measure (SpinTensorIndex I degree → ℝ)).prod
        (tensorLabeledLaw U I degree amp n b (fun i => v (i + 1)))) :=
    integrable_of_measurable_abs_le hF hFb
  calc
    _ = ∫ p, F (tensorFlatToLabeled U I degree amp n v p)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates := by
      apply integral_congr_ae
      refine ae_of_all _ fun p => ?_
      dsimp only [F]
      have he : tensorLabeledEnergy eig U c I degree amp n
          (tensorFlatToLabeled U I degree amp n v p).1
          (tensorFlatToLabeled U I degree amp n v p).2 =
          fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
            cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2 := by
        funext x
        exact tensorLabeledEnergy_flat_eq eig U c I degree amp n v p x
      rw [he]
      rfl
    _ = ∫ p, F p ∂(tensorGaussianLaw I degree (v 0) : Measure _).prod
        (tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))) :=
      (tensorFlatToLabeled_measurePreserving U I degree amp n b v).hasLaw.integral_comp
        hF.aestronglyMeasurable
    _ = ∫ z, ∫ T, F (z,T) ∂tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))
        ∂(tensorGaussianLaw I degree (v 0) : Measure _) := integral_prod _ hi
    _ = 1 - b d := by
      have he (z : SpinTensorIndex I degree → ℝ) :
          (∫ T, F (z,T) ∂tensorLabeledLaw U I degree amp n b (fun i => v (i + 1))) = 1 - b d :=
        spinPriorLabeled_tilted_parent_tail hN π eig U c I degree amp n b _ hb z d
      simp_rw [he]
      simp only [integral_const, probReal_univ, one_smul]


end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean_oai := @OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean_oai
