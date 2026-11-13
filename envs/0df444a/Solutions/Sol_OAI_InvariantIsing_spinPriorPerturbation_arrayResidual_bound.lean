-- Prove2me | solution 1 for OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:10:04.548212+00:00
-- url     : https://prove2.me/submissions/5ead1ec9-4e57-4578-86e2-16ad66cbc407

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_spinPriorFiniteGG_individualDiagonal_bound
import Theorems.Thm_OAI_InvariantIsing_spinPriorProfileLog_variance

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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

lemma convex_derivative_fluctuation {f g : ℝ → ℝ} {v s df dg C : ℝ}
    (hs : 0 < s) (hc : ConvexOn ℝ (Icc (v-s) (v+s)) f)
    (hd : HasDerivAt f df v)
    (hplus : g (v+s) - g v - s * dg ≤ C * s^2)
    (hminus : g (v-s) - g v + s * dg ≤ C * s^2) :
    |df-dg| ≤ C*s +
      (|f (v+s)-g (v+s)| + |f (v-s)-g (v-s)| + 2*|f v-g v|)/s := by
  have hv : v ∈ Icc (v-s) (v+s) := ⟨by linarith, by linarith⟩
  have hl := hc.slope_le_of_hasDerivAt (show v-s ∈ Icc (v-s) (v+s) from
    ⟨le_rfl, by linarith⟩) hv (by linarith : v-s < v) hd
  have hr := hc.le_slope_of_hasDerivAt hv (show v+s ∈ Icc (v-s) (v+s) from
    ⟨by linarith, le_rfl⟩) (by linarith : v < v+s) hd
  rw [slope_def_field] at hl hr
  have hl' : f v - f (v-s) ≤ df*s := by
    have := (div_le_iff₀ (show 0 < v-(v-s) by linarith)).mp hl
    nlinarith
  have hr' : df*s ≤ f (v+s)-f v := by
    have := (le_div_iff₀ (show 0 < v+s-v by linarith)).mp hr
    nlinarith
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [neg_mul, add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v-s)-g (v-s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v+s)-g (v+s)), abs_nonneg (f v-g v)]
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    simp only [add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith [le_abs_self (f (v+s)-g (v+s)), neg_abs_le (f v-g v),
      abs_nonneg (f (v-s)-g (v-s)), abs_nonneg (f v-g v)]

lemma minimizer_quadratic_remainder {g : ℝ → ℝ} {v c a dg x : ℝ}
    (hmin : -g v + c*(v-a)^2 ≤ -g x + c*(x-a)^2)
    (hstationary : dg = 2*c*(v-a)) :
    g x - g v - (x-v)*dg ≤ c*(x-v)^2 := by
  rw [hstationary]
  nlinarith

open ProbabilityTheory Filter

lemma tendsto_central_second_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℝ) :
    Tendsto (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2)
      (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f v)) := by
  have ht := Real.taylor_tendsto (x₀ := v) (n := 2) convex_univ (mem_univ v) hf.contDiffOn
  simp only [nhdsWithin_univ] at ht
  have ht' : Tendsto (fun x => (f x-(f v+(x-v)*deriv f v+
      (x-v)^2/2*iteratedDeriv 2 f v))/(x-v)^2) (𝓝 v) (𝓝 0) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
      iteratedDeriv_one, smul_eq_mul]
    ring
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp := ht'.comp (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v)
  have hn := ht'.comp (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v)
  have he : (fun h : ℝ => (f (v+h)+f (v-h)-2*f v)/h^2) =ᶠ[𝓝[≠] 0]
      (fun h => ((f (v+h)-(f v+(v+h-v)*deriv f v+
        (v+h-v)^2/2*iteratedDeriv 2 f v))/(v+h-v)^2)+
        ((f (v-h)-(f v+(v-h-v)*deriv f v+
        (v-h-v)^2/2*iteratedDeriv 2 f v))/(v-h-v)^2)+iteratedDeriv 2 f v) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : h ≠ 0 := hh
    field_simp [hh']
    ring
  simpa only [zero_add] using ((hp.add hn).add_const (iteratedDeriv 2 f v)).congr' he.symm

lemma integrable_limit_of_integral_bound {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hi : ∀ i, Integrable (F i) μ) (hnn : ∀ i ω, 0 ≤ F i ω)
    (hb : ∀ᶠ i in l, (∫ ω, F i ω ∂μ) ≤ C)
    (hl : ∀ ω, Tendsto (fun i => F i ω) l (𝓝 (g ω))) :
    Integrable g μ ∧ (∫ ω, g ω ∂μ) ≤ C := by
  have hgn (ω : Ω) : 0 ≤ g ω := ge_of_tendsto (hl ω) (Eventually.of_forall (fun i => hnn i ω))
  have hgm : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae l
    (fun i => (hi i).aestronglyMeasurable) (ae_of_all _ hl)
  have hC : 0 ≤ C := by
    obtain ⟨i, h⟩ := hb.exists
    exact (integral_nonneg (hnn i)).trans h
  have he : (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (F i ω)) l ∂μ := by
        apply lintegral_congr
        intro ω
        exact (ENNReal.tendsto_ofReal (hl ω)).liminf_eq.symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (F i ω) ∂μ) l :=
        lintegral_liminf_le' (fun i => (hi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ _ := by
        refine liminf_le_of_frequently_le ?_ (isBoundedUnder_of ⟨0, fun _ => zero_le⟩)
        apply Eventually.frequently
        filter_upwards [hb] with i hiC
        rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (hnn i))]
        exact ENNReal.ofReal_le_ofReal hiC
  have hgi : Integrable g μ := (lintegral_ofReal_ne_top_iff_integrable hgm (ae_of_all _ hgn)).mp
    (ne_of_lt (he.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hgi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgn) hgm]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

lemma central_second_difference_nonneg {f : ℝ → ℝ}
    (hc : ConvexOn ℝ univ f) (v h : ℝ) : 0 ≤ (f (v+h)+f (v-h)-2*f v)/h^2 := by
  have he := hc.2 (mem_univ (v+h)) (mem_univ (v-h))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hav : (1/2:ℝ) • (v+h)+(1/2:ℝ) • (v-h) = v := by simp only [smul_eq_mul] <;> ring
  rw [hav] at he
  simp only [smul_eq_mul] at he
  exact div_nonneg (by linarith) (sq_nonneg h)

theorem expected_curvature_at_minimum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ ω, ConvexOn ℝ univ (f ω)) (hd : ∀ ω, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  let F := fun h ω => (f ω (v+h)+f ω (v-h)-2*f ω v)/h^2
  have hF (h : ℝ) : Integrable (F h) μ := ((hi (v+h)).add (hi (v-h)) |>.sub
    ((hi v).const_mul 2)).div_const _
  have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v+h) ∂μ)+c*(v+h-a)^2 :=
    (show Tendsto (fun h : ℝ => v+h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_add v).eventually hmin
  have hn : ∀ᶠ h in 𝓝[≠] (0:ℝ),
      -(∫ ω, f ω v ∂μ)+c*(v-a)^2 ≤ -(∫ ω, f ω (v-h) ∂μ)+c*(v-h-a)^2 :=
    (show Tendsto (fun h : ℝ => v-h) (𝓝[≠] 0) (𝓝 v) by simpa using hid.const_sub v).eventually hmin
  apply integrable_limit_of_integral_bound (l := 𝓝[≠] (0:ℝ)) hF
    (fun h ω => central_second_difference_nonneg (hc ω) v h) ?_
    (fun ω => tendsto_central_second_difference (hd ω) v)
  filter_upwards [hp, hn, self_mem_nhdsWithin] with h hp' hn' hz
  dsimp only [F]
  rw [integral_div, integral_sub (f := fun ω => f ω (v+h)+f ω (v-h))
    (g := fun ω => 2*f ω v) ((hi (v+h)).add (hi (v-h))) ((hi v).const_mul 2),
    integral_add (hi (v+h)) (hi (v-h)), integral_const_mul]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (show h ≠ 0 from hz))).mpr
  nlinarith

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

lemma probability_thermal_young {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ} (hY : MemLp Y 2 ν)
    {K : ℝ} (hK : 0 < K) :
    (∫ x, |Y x-(∫ y, Y y ∂ν)| ∂ν) ≤ (Var[Y; ν]+K^2)/(2*K) := by
  let m := ∫ y, Y y ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := ((hY.integrable (by norm_num)).sub (integrable_const m)).abs
  have hs : Integrable (fun x => (Y x-m)^2) ν := (hY.sub (memLp_const m)).integrable_sq
  calc
    _ ≤ ∫ x, ((Y x-m)^2+K^2)/(2*K) ∂ν := by
      apply integral_mono hi ((hs.add (integrable_const _)).div_const _)
      intro x
      change |Y x-m| ≤ ((Y x-m)^2+K^2)/(2*K)
      apply (le_div_iff₀ (by positivity : 0 < 2*K)).mpr
      nlinarith [sq_nonneg (|Y x-m|-K), sq_abs (Y x-m)]
    _ = _ := by
      rw [integral_div, integral_add hs (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [variance_eq_integral hY.aemeasurable]

end IsingPerceptron

namespace IsingPerceptron

theorem expected_curvature_at_minimum_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ} {v c a : ℝ}
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ univ (f ω))
    (hd : ∀ᵐ ω ∂μ, ContDiff ℝ 2 (f ω))
    (hi : ∀ t, Integrable (fun ω => f ω t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, f ω t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => iteratedDeriv 2 (f ω) v) μ ∧
      (∫ ω, iteratedDeriv 2 (f ω) v ∂μ) ≤ 2*c := by
  classical
  let f' : Ω → ℝ → ℝ := fun ω =>
    if ConvexOn ℝ univ (f ω) ∧ ContDiff ℝ 2 (f ω) then f ω else fun _ => 0
  have he : ∀ᵐ ω ∂μ, f' ω = f ω := by
    filter_upwards [hc,hd] with ω hω hω'
    simp [f',hω,hω']
  have hc' (ω) : ConvexOn ℝ univ (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.1
    · exact convexOn_const _ (convex_univ)   
  have hd' (ω) : ContDiff ℝ 2 (f' ω) := by
    dsimp only [f']
    split_ifs with h
    · exact h.2
    · exact contDiff_const
  have hi' (t) : Integrable (fun ω => f' ω t) μ :=
    (hi t).congr (he.mono fun _ h => congrFun h.symm t)
  have heI (t) : (∫ ω, f' ω t ∂μ) = ∫ ω, f ω t ∂μ :=
    integral_congr_ae (he.mono fun _ h => congrFun h t)
  have hmin' : IsLocalMin (fun t => -(∫ ω, f' ω t ∂μ)+c*(t-a)^2) v := by
    simpa only [heI] using hmin
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum hc' hd' hi' hmin'
  have hed : (fun ω => iteratedDeriv 2 (f' ω) v) =ᵐ[μ]
      (fun ω => iteratedDeriv 2 (f ω) v) := he.mono fun _ h => congrArg (fun k => iteratedDeriv 2 k v) h
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem expected_tilted_variance_at_minimum_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω}
    (ν : Ω → Measure X) (Y : Ω → X → ℝ) {v c a : ℝ}
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y ω x)) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (Y ω) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (Y ω) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    Integrable (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) μ ∧
      (∫ ω, Var[Y ω; (ν ω).tilted (v*Y ω ·)] ∂μ) ≤ 2*c := by
  obtain ⟨h1,h2⟩ := expected_curvature_at_minimum_ae
    (he.mono fun _ h => convexOn_cgf_of_all_exp h)
    (he.mono fun _ h => contDiff_cgf_of_all_exp h) hi hmin
  have hed : (fun ω => iteratedDeriv 2 (cgf (Y ω) (ν ω)) v) =ᵐ[μ]
      (fun ω => Var[Y ω; (ν ω).tilted (v*Y ω ·)]) := by
    filter_upwards [he] with ω hω
    exact (variance_tilted_mul (mem_interior_integrableExpSet_of_all hω v)).symm
  exact ⟨h1.congr hed,(integral_congr_ae hed).symm ▸ h2⟩

theorem integral_convex_derivative_fluctuation_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ → ℝ} {g : ℝ → ℝ}
    {v s dg C δ : ℝ} {df : Ω → ℝ} (hs : 0 < s)
    (hc : ∀ᵐ ω ∂μ, ConvexOn ℝ (Icc (v-s) (v+s)) (f ω))
    (hd : ∀ᵐ ω ∂μ, HasDerivAt (f ω) (df ω) v)
    (hplus : g (v+s)-g v-s*dg ≤ C*s^2)
    (hminus : g (v-s)-g v+s*dg ≤ C*s^2)
    (hfplus : Integrable (fun ω => f ω (v+s)) μ)
    (hfminus : Integrable (fun ω => f ω (v-s)) μ)
    (hfv : Integrable (fun ω => f ω v) μ)
    (hm : AEStronglyMeasurable df μ)
    (hep : (∫ ω, |f ω (v+s)-g (v+s)| ∂μ) ≤ δ)
    (hem : (∫ ω, |f ω (v-s)-g (v-s)| ∂μ) ≤ δ)
    (hev : (∫ ω, |f ω v-g v| ∂μ) ≤ δ) :
    Integrable df μ ∧ (∫ ω, |df ω-dg| ∂μ) ≤ C*s+4*δ/s := by
  have hp : Integrable (fun ω => |f ω (v+s)-g (v+s)|) μ := (hfplus.sub (integrable_const (g (v+s)))).abs
  have hn : Integrable (fun ω => |f ω (v-s)-g (v-s)|) μ := (hfminus.sub (integrable_const (g (v-s)))).abs
  have hv : Integrable (fun ω => |f ω v-g v|) μ := (hfv.sub (integrable_const (g v))).abs
  let B := fun ω => C*s+(|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s
  have hi : Integrable B μ := (integrable_const (C*s)).add
    ((hp.add hn |>.add (hv.const_mul 2)).div_const s)
  have hb : ∀ᵐ ω ∂μ, |df ω-dg| ≤ B ω := by
    filter_upwards [hc,hd] with ω hω hω'
    exact convex_derivative_fluctuation hs hω hω' hplus hminus
  have hid : Integrable (fun ω => df ω-dg) μ :=
    hi.mono' (hm.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨?_,?_⟩
  · have hdi : Integrable (fun ω => (df ω-dg)+dg) μ := hid.add (integrable_const dg)
    simpa only [sub_add_cancel] using hdi
  have hib : Integrable (fun ω => (|f ω (v+s)-g (v+s)|+
      |f ω (v-s)-g (v-s)|+2*|f ω v-g v|)/s) μ :=
    (hp.add hn |>.add (hv.const_mul 2)).div_const s
  have hic : Integrable (fun ω => |f ω (v+s)-g (v+s)|+|f ω (v-s)-g (v-s)|) μ := hp.add hn
  have hie : Integrable (fun ω => 2*|f ω v-g v|) μ := hv.const_mul 2
  calc
    _ ≤ ∫ ω, B ω ∂μ := integral_mono_ae hid.abs hi hb
    _ = C*s+((∫ ω, |f ω (v+s)-g (v+s)| ∂μ)+
        (∫ ω, |f ω (v-s)-g (v-s)| ∂μ)+2*(∫ ω, |f ω v-g v| ∂μ))/s := by
      dsimp [B]
      rw [integral_add (integrable_const _) hib,
        integral_div,integral_add hic hie,integral_add hp hn,integral_const_mul]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ ≤ C*s+4*δ/s := by gcongr; linarith

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

lemma integrate_thermal_majorant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T V : Ω → ℝ} {K C : ℝ}
    (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω) (hK : 0 < K)
    (hVi : Integrable V μ) (hVb : (∫ ω, V ω ∂μ) ≤ C)
    (hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K)) :
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (C+K^2)/(2*K) := by
  have hbI : Integrable (fun ω => (V ω+K^2)/(2*K)) μ :=
    (hVi.add (integrable_const _)).div_const _
  have hTi : Integrable T μ := hbI.mono' hT.aestronglyMeasurable
    (hb.mono fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hT0 ω)] using hω)
  refine ⟨hTi,(integral_mono_ae hTi hbI hb).trans ?_⟩
  rw [integral_div,integral_add hVi (integrable_const _),integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  exact div_le_div_of_nonneg_right (by linarith : (∫ ω, V ω ∂μ)+K^2 ≤ C+K^2) (by positivity)

lemma measurable_random_thermal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) (v : ℝ) :
    Measurable (fun ω => ∫ x, |Y (ω,x)-(∫ z, Y (ω,z) ∂(ν ω).tilted (fun z => v*Y (ω,z)))|
      ∂(ν ω).tilted (fun x => v*Y (ω,x))) := by
  have hm := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  exact measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z)
    (F := fun z : Ω × X => |Y z-(∫ x, Y (z.1,x) ∂(ν z.1).tilted (fun x => v*Y (z.1,x)))|)
    hν (hY.const_mul v) (hY.sub (hm.comp measurable_fst) |>.abs)

theorem expected_tilted_thermal_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a K : ℝ} (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable T μ ∧ (∫ ω, T ω ∂μ) ≤ (2*c+K^2)/(2*K) := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let V := fun ω => Var[(fun x => Y (ω,x)); (ν ω).tilted (fun x => v*Y (ω,x))]
  have hT : Measurable T := measurable_random_thermal hν hY v
  obtain ⟨hVi,hVb⟩ := expected_tilted_variance_at_minimum_ae (μ := μ) (v := v) (c := c) (a := a)
    ν (fun ω x => Y (ω,x)) he hi hmin
  change Integrable V μ at hVi
  change (∫ ω, V ω ∂μ) ≤ 2*c at hVb
  have hb : ∀ᵐ ω ∂μ, T ω ≤ (V ω+K^2)/(2*K) := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) :=
      isProbabilityMeasure_tilted (hω v)
    exact probability_thermal_young (by simpa using (memLp_tilted_mul
      (mem_interior_integrableExpSet_of_all hω v) (2:NNReal))) hK
  exact integrate_thermal_majorant (μ := μ) hT
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hK hVi hVb hb

theorem expected_tilted_mean_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ : ℝ} (hs : 0 < s)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable m μ ∧ (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hm : Measurable m := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := Y) hν (hY.const_mul v) hY
  apply integral_convex_derivative_fluctuation_ae (μ := μ) (v := v) (C := c)
    (dg := 2*c*(v-a)) (df := m) (δ := δ)
    (f := fun ω t => cgf (fun x => Y (ω,x)) (ν ω) t)
    (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ) hs
  · filter_upwards [he] with ω hω
    exact (convexOn_cgf_of_all_exp hω).subset (subset_univ _) (convex_Icc _ _)
  · filter_upwards [he] with ω hω
    have ht := mem_interior_integrableExpSet_of_all hω v
    have hd := (analyticAt_cgf ht).differentiableAt.hasDerivAt
    rwa [← integral_tilted_mul_self ht] at hd
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v+s) (hmin (v+s) ⟨by linarith,le_rfl⟩) rfl
    simpa only [add_sub_cancel_left] using h
  · have h := minimizer_quadratic_remainder (g := fun t => ∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)
      (v := v) (c := c) (a := a) (dg := 2*c*(v-a)) (x := v-s) (hmin (v-s) ⟨le_rfl,by linarith⟩) rfl
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  · exact hi _
  · exact hi _
  · exact hi _
  · exact hm.aestronglyMeasurable
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)
  · exact hconc _ (by simp)

lemma probability_energy_triangle {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {Y : X → ℝ}
    (hY : Integrable Y ν) (b : ℝ) :
    (∫ x, |Y x-b| ∂ν) ≤ (∫ x, |Y x-(∫ z, Y z ∂ν)| ∂ν)+|(∫ z, Y z ∂ν)-b| := by
  let m := ∫ z, Y z ∂ν
  have hi : Integrable (fun x => |Y x-m|) ν := (hY.sub (integrable_const m)).abs
  calc
    _ ≤ ∫ x, |Y x-m|+|m-b| ∂ν := by
      apply integral_mono ((hY.sub (integrable_const b)).abs) (hi.add (integrable_const _))
      intro x
      exact abs_sub_le (Y x) m b
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp [m]

theorem expected_tilted_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {Y : Ω × X → ℝ} (hY : Measurable Y) {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (he : ∀ᵐ ω ∂μ, ∀ t : ℝ, Integrable (fun x => Real.exp (t*Y (ω,x))) (ν ω))
    (hi : ∀ t, Integrable (fun ω => cgf (fun x => Y (ω,x)) (ν ω) t) μ)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) v ∂μ)+c*(v-a)^2 ≤
      -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω,x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω',x)) (ν ω') t ∂μ)| ∂μ) ≤ δ) :
    let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
    Integrable E μ ∧ (∫ ω, E ω ∂μ) ≤ (2*c+K^2)/(2*K)+c*s+4*δ/s := by
  let m := fun ω => ∫ x, Y (ω,x) ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let T := fun ω => ∫ x, |Y (ω,x)-m ω| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  let E := fun ω => ∫ x, |Y (ω,x)-2*c*(v-a)| ∂(ν ω).tilted (fun x => v*Y (ω,x))
  have hloc : IsLocalMin (fun t => -(∫ ω, cgf (fun x => Y (ω,x)) (ν ω) t ∂μ)+c*(t-a)^2) v := by
    filter_upwards [Icc_mem_nhds (by linarith : v-s < v) (by linarith : v < v+s)] with t ht
    exact hmin t ht
  obtain ⟨hTi,hTb⟩ := expected_tilted_thermal_at_minimum hν hY hK he hi hloc
  obtain ⟨hmi,hmb⟩ := expected_tilted_mean_at_minimum hν hY hs he hi hmin hconc
  change Integrable T μ at hTi
  change (∫ ω, T ω ∂μ) ≤ _ at hTb
  change Integrable m μ at hmi
  change (∫ ω, |m ω-2*c*(v-a)| ∂μ) ≤ _ at hmb
  have hEi : Measurable E := measurable_random_tilted_integral (ν := ν)
    (H := fun z : Ω × X => v*Y z) (F := fun z => |Y z-2*c*(v-a)|)
    hν (hY.const_mul v) (hY.sub_const _ |>.abs)
  have hb : ∀ᵐ ω ∂μ, E ω ≤ T ω+|m ω-2*c*(v-a)| := by
    filter_upwards [he] with ω hω
    have : IsProbabilityMeasure ((ν ω).tilted (fun x => v*Y (ω,x))) := isProbabilityMeasure_tilted (hω v)
    exact probability_energy_triangle
      ((memLp_tilted_mul (mem_interior_integrableExpSet_of_all hω v) (1:NNReal)).integrable (by norm_num)) _
  have hbi : Integrable (fun ω => T ω+|m ω-2*c*(v-a)|) μ :=
    hTi.add ((hmi.sub (integrable_const _)).abs)
  have hE : Integrable E μ := hbi.mono' hEi.aestronglyMeasurable
    (hb.mono fun ω hω => by
      have hnonneg : 0 ≤ E ω := integral_nonneg (fun _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hω)
  refine ⟨hE,(integral_mono_ae hE hbi hb).trans ?_⟩
  have hai : Integrable (fun ω => |m ω-2*c*(v-a)|) μ := (hmi.sub (integrable_const _)).abs
  rw [integral_add hTi hai]
  linarith

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
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma perturbationScale_nonneg (N : ℕ) : 0 ≤ perturbationScale N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma l1_center_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, |X ω-∫ t, X t ∂P| ∂P) ≤ Real.sqrt (Var[X;P]) := by
  have hL := (hX.sub (memLp_const (∫ t, X t ∂P))).norm
  have hv := variance_nonneg (fun ω => |X ω-∫ t, X t ∂P|) P
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hL)] at hv
  have he : (∫ ω, |X ω-∫ t, X t ∂P|^2 ∂P) = Var[X;P] := by
    rw [variance_eq_integral hX.aemeasurable]
    simp only [sq_abs]
  simp only [Pi.pow_apply] at hv
  rw [he] at hv
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg X P)).2
    (by linarith)

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

lemma measurable_gaussianNamespaceJoin (j : ℕ) : Measurable (gaussianNamespaceJoin j) := by
  apply Measurable.of_eval
  intro i
  by_cases h : (Nat.unpair i).1 = j
  · simp only [gaussianNamespaceJoin,dite_eq_left h]
    fun_prop
  · simp only [gaussianNamespaceJoin,dite_eq_right h]
    fun_prop

lemma gaussianNamespaceJoin_split (j : ℕ) (g : ℕ → ℝ) :
    gaussianNamespaceJoin j (gaussianNamespaceSplit j g) = g := by
  funext i
  simp only [gaussianNamespaceJoin,gaussianNamespaceSplit]
  split_ifs with h
  · rw [← h,Nat.pair_unpair]
  · rw [Nat.pair_unpair]

lemma gaussianNamespaceJoin_law (j : ℕ) :
    (gaussianCoordinates.prod (otherNamespacesLaw j)).map (gaussianNamespaceJoin j) =
      gaussianCoordinates := by
  rw [← gaussianNamespaceSplit_law,Measure.map_map
    (measurable_gaussianNamespaceJoin j) (measurable_gaussianNamespaceSplit j)]
  simp only [Function.comp_def,gaussianNamespaceJoin_split,Measure.map_id']

lemma gaussianNamespaceJoin_selected (j : ℕ) (z : ℕ → ℝ) (g : OtherNamespaces j) (i : ℕ) :
    gaussianNamespaceJoin j (z,g) (Nat.pair j i) = z i := by
  simp [gaussianNamespaceJoin,Nat.unpair_pair]

lemma gaussianNamespaceJoin_other (j : ℕ) (z : ℕ → ℝ) (g : OtherNamespaces j)
    (k : {k : ℕ // k ≠ j}) (i : ℕ) :
    gaussianNamespaceJoin j (z,g) (Nat.pair k i) = g k i := by
  simp [gaussianNamespaceJoin,Nat.unpair_pair,k.property]

theorem gaussianNamespaceJoin_preserving (j : ℕ) :
    MeasurePreserving (gaussianNamespaceJoin j)
      (gaussianCoordinates.prod (otherNamespacesLaw j)) gaussianCoordinates :=
  ⟨measurable_gaussianNamespaceJoin j,gaussianNamespaceJoin_law j⟩

lemma namespaceInsertion_preserving {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (j : ℕ) :
    MeasurePreserving (fun p : (Ω × OtherNamespaces j) × (ℕ → ℝ) =>
      (p.1.1,gaussianNamespaceJoin j (p.2,p.1.2)))
      ((P.prod (otherNamespacesLaw j)).prod gaussianCoordinates)
      (P.prod gaussianCoordinates) := by
  have h1 := measurePreserving_prodAssoc P (otherNamespacesLaw j) gaussianCoordinates
  have h2 := (MeasurePreserving.id P).prod
    (gaussianNamespaceJoin_preserving j |>.comp Measure.measurePreserving_swap)
  exact h2.comp h1

end IsingPerceptron

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

lemma centered_sub_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F B : Ω → ℝ} (hF : Integrable F P) (hB : Integrable B P)
    {δF δB : ℝ}
    (hcF : (∫ ω, |F ω-∫ ω', F ω' ∂P| ∂P) ≤ δF)
    (hcB : (∫ ω, |B ω-∫ ω', B ω' ∂P| ∂P) ≤ δB) [IsFiniteMeasure P] :
    (∫ ω, |F ω-B ω-∫ ω', (F ω'-B ω') ∂P| ∂P) ≤ δF+δB := by
  rw [integral_sub hF hB]
  have hiF : Integrable (fun ω => |F ω-∫ ω', F ω' ∂P|) P := (hF.sub (integrable_const _)).abs
  have hiB : Integrable (fun ω => |B ω-∫ ω', B ω' ∂P|) P := (hB.sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, |F ω-∫ ω', F ω' ∂P|+|B ω-∫ ω', B ω' ∂P| ∂P := by
      apply integral_mono ((hF.sub hB).sub (integrable_const _)).abs (hiF.add hiB)
      intro ω
      change |F ω-B ω-((∫ ω', F ω' ∂P)-(∫ ω', B ω' ∂P))| ≤ _
      rw [show F ω-B ω-((∫ ω', F ω' ∂P)-(∫ ω', B ω' ∂P)) =
        (F ω-∫ ω', F ω' ∂P)-(B ω-∫ ω', B ω' ∂P) by ring]
      exact abs_sub _ _
    _ = (∫ ω, |F ω-∫ ω', F ω' ∂P| ∂P)+(∫ ω, |B ω-∫ ω', B ω' ∂P| ∂P) :=
      integral_add hiF hiB
    _ ≤ _ := add_le_add hcF hcB

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma update_abs_le_two {N : ℕ} {u : Fin N → ℝ} (hu : ∀ j, |u j| ≤ 2)
    (j : Fin N) {v : ℝ} (hv : |v| ≤ 2) : ∀ k, |Function.update u j v k| ≤ 2 := by
  intro k
  by_cases hk : k = j
  · subst k; simpa using hv
  · simpa [hk] using hu k

lemma perturbationAmplitude_pos {N : ℕ} (hN : 0 < N) (j : ℕ) :
    0 < perturbationAmplitude N j := by
  unfold perturbationAmplitude perturbationScale perturbationWeight
  positivity

end IsingPerceptron

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
namespace IsingPerceptron

lemma gaussian_log_partition_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ∧
      (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ≤ K/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiH := gaussian_field_integrable (ν := ν) hm hg hv
  have hexp := gaussian_field_exp_integrable (ν := ν) hm hg hv 1
  simp only [one_mul,one_pow] at hexp
  have hZ : Integrable Z μ := hexp.1.integral_prod_left
  have hpos : ∀ᵐ ω ∂μ, 0 < Z ω := by
    filter_upwards [hexp.1.prod_right_ae] with ω hω
    exact MeasureTheory.integral_exp_pos hω
  have hiLog : Integrable (fun ω => Real.log (Z ω)) μ :=
    ((memLp_two_iff_integrable_sq hmZ.log.aestronglyMeasurable).2
      (gaussian_log_partition_second hm hg hv).1).integrable (by norm_num)
  have hexplog : Integrable (fun ω => Real.exp (Real.log (Z ω))) μ := by
    apply hZ.congr
    filter_upwards [hpos] with ω hω
    exact (Real.exp_log hω).symm
  have hmean : (∫ ω, ∫ x, H (ω,x) ∂ν ∂μ) = 0 := by
    rw [integral_integral_swap (f := fun ω x => H (ω,x)) hiH]
    have hz : ∀ x, (∫ ω, H (ω,x) ∂μ) = 0 := by
      intro x
      have hmx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
      have he := integral_map hmx.aemeasurable (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (fun y : ℝ => y) (μ.map (fun ω => H (ω,x))))
      simp only [hg x,id_eq,integral_id_gaussianReal] at he
      exact he.symm
    simp_rw [hz]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hmean]
    apply integral_mono_ae hiH.integral_prod_left hiLog
    filter_upwards [hiH.prod_right_ae,hexp.1.prod_right_ae,hpos] with ω hω heω hpω
    exact Real.exp_le_exp.mp (by
      rw [Real.exp_log hpω]
      exact exp_integral_le_partition hω heω)
  · apply Real.exp_le_exp.mp
    calc
      _ ≤ ∫ ω, Real.exp (Real.log (Z ω)) ∂μ := exp_integral_le_partition hiLog hexplog
      _ = ∫ ω, Z ω ∂μ := integral_congr_ae (hpos.mono (fun _ h => Real.exp_log h))
      _ ≤ _ := hexp.2

lemma cylinder_cgf_mean_bounds {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    0 ≤ (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ∧
      (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ≤ t^2*K/2 := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (A z.2) z.1) :=
    (measurable_cylinderFields A).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((A x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((A x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg _)
  exact gaussian_log_partition_mean_bounds (ν := ν) hm (fun x => cylinder_scaled_law A x t) hv

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma perturbationWeight_pos (j : ℕ) : 0 < perturbationWeight j := by
  unfold perturbationWeight
  positivity

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

lemma tensorPerturbationAmplitude_update {N : ℕ} (u : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    tensorPerturbationAmplitude N (Function.update u j t) =
      Function.update (tensorPerturbationAmplitude N u) j (perturbationAmplitude N j * t) := by
  classical
  funext i
  by_cases hi : i = j
  · subst i
    simp only [tensorPerturbationAmplitude, Function.update_self]
  · simp only [tensorPerturbationAmplitude, Function.update_of_ne hi]

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
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedGGFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched G G Finite. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma newReplicaEmbedding_injective (k : ℕ) (e : Equiv.Perm (Fin k)) :
    Function.Injective (newReplicaEmbedding k e) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · exact fun _ => rfl
    · intro hab
      have hlt := (e b).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      have hlt := (e a).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
    · intro hab
      apply congrArg Fin.succ
      apply e.injective
      apply Fin.val_injective
      exact hab

lemma sum_nonzero_permutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (f : Fin (m+1) → ℝ) :
    (∑ l : Fin m, f (e l.succ)) = ∑ j ∈ Finset.univ.erase (e 0), f j := by
  classical
  have he := Equiv.sum_comp e f
  rw [Fin.sum_univ_succ,← Finset.add_sum_erase _ _ (Finset.mem_univ (e 0))] at he
  exact add_left_cancel he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_Overlaps
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap geometry

The finite projected overlaps are Gram matrices. Panchenko's ultrametricity
theorem applies to their limit arrays satisfying the Ghirlanda–Guerra identities.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma projectedOverlap_self_nonneg {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Spin N) : 0 ≤ projectedOverlap U I σ σ := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_OverlapBounds
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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

lemma projectedOverlap_self_le_one {N : ℕ} (U : Rotation N) (I : Finset (Fin N)) (σ : Spin N) :
    projectedOverlap U I σ σ ≤ 1 :=
  (le_abs_self _).trans (projectedOverlap_abs_le_one U I σ σ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationFeatures
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
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

theorem jointSpectralMonomialCoefficients_cross {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x y : Spin N × IsingPerceptron.LabeledLeaf n) :
    IsingPerceptron.cylinderCross (jointSpectralMonomialCoefficients U I d n r x)
      (jointSpectralMonomialCoefficients U I d n r y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a) *
        IsingPerceptron.treeOverlap n x.2 y.2 ^ r := by
  unfold jointSpectralMonomialCoefficients
  rw [IsingPerceptron.treeField_path_cross n x.2 y.2
    (IsingPerceptron.monomialPath_monotone n r)
    (IsingPerceptron.monomialPath_nonneg n r 0), spectralMonomialFeature_cross]
  exact mul_comm _ _

theorem jointSpectralMonomialCoefficients_variance_le_one {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × IsingPerceptron.LabeledLeaf n) :
    (jointSpectralMonomialCoefficients U I d n r x).sum (fun _ c => c ^ 2) ≤ 1 := by
  rw [← IsingPerceptron.cylinderCross_self, jointSpectralMonomialCoefficients_cross]
  have ht : 0 ≤ IsingPerceptron.treeOverlap n x.2 x.2 ^ r := by
    unfold IsingPerceptron.treeOverlap
    positivity
  have htl : IsingPerceptron.treeOverlap n x.2 x.2 ^ r ≤ 1 := by
    simpa only [IsingPerceptron.treeOverlap, IsingPerceptron.labeledCommonDepth_self,
      IsingPerceptron.monomialPath] using IsingPerceptron.monomialPath_diag_le_one n r
  exact (mul_le_mul ((le_abs_self _).trans (spectralMonomial_abs_le_one U I d x.1 x.1))
    htl ht (by norm_num)).trans_eq (one_mul 1)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PerturbationMeasurability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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

lemma cylinderField_single (j : ℕ) (c : ℝ) (g : ℕ → ℝ) :
    cylinderField (Finsupp.single j c) g = c * g j :=
  Finsupp.sum_single_index (zero_mul _)

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderField]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, cylinderField_add, ih]

lemma cylinderField_featureCoefficients {J : Type*} [Fintype J]
    (tag : J → ℕ) (c : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients tag c) g = ∑ j, c j * g (tag j) := by
  rw [featureCoefficients, cylinderField_finset_sum]
  simp_rw [cylinderField_single]

lemma measurable_jointSpectralMonomialField {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (jointSpectralMonomialCoefficients (specialRotation p.1) I d n r x) p.2) := by
  unfold jointSpectralMonomialCoefficients treeFieldCoefficients
  simp_rw [cylinderField_featureCoefficients]
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_spectralMonomialFeature I d x.1 j.2).comp measurable_fst |>.const_mul _).mul
    ((measurable_pi_apply _).comp measurable_snd)

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorRootTreeLaw_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
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

private lemma sqrt_varianceIncrement {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    (NNReal.sqrt (varianceIncrement q i) : ℝ) = pathAmplitude q i := by
  rw [Real.coe_sqrt, varianceIncrement_coe hq h0]
  rfl

/-- The reindexed field is exactly the sum of the linear enrichment and
the displayed independent spectral/tree Gaussian monomials. -/
theorem tensorNamespacedField_expand {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (x : Spin N × LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x) g =
      cylinderField (tensorLinearCoefficients n h x) (fun i => g (Nat.pair 0 i)) +
        ∑ j, amplitude j * cylinderField
          (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x)
          (fun i => g (Nat.pair (j + 1) i)) := by
  rw [tensorNamespacedCoefficients, cylinderField_feature, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorPathProfile, tensorVarianceProfile, spinTensorFeature, tensorNamespaceTag]
  simp_rw [sqrt_varianceIncrement hh h0,
    sqrt_varianceIncrement (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [tensorLinearCoefficients, treeFieldCoefficients, cylinderField_feature, Fintype.sum_prod_type]
    rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [jointSpectralMonomialCoefficients, treeFieldCoefficients, cylinderField_feature,
      Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [treeFeatureTag]
    ring

lemma tensorNamespacedField_frozen {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (x : Spin N × LabeledLeaf n) (z : ℕ → ℝ) (g : OtherNamespaces (j + 1)) :
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (z, g)) =
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, g)) := by
  classical
  simp_rw [tensorNamespacedField_expand U I degree _ n treeDegree h hh h0]
  congr 1
  · congr 1
    funext i
    exact (gaussianNamespaceJoin_other (j + 1) z g ⟨0, by omega⟩ i).trans
      (gaussianNamespaceJoin_other (j + 1) 0 g ⟨0, by omega⟩ i).symm
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = j
    · subst a
      simp
    · simp only [Function.update_of_ne ha]
      congr 1
      congr 1
      funext i
      have hv : (a : ℕ) + 1 ≠ (j : ℕ) + 1 := fun he => ha (Fin.ext (Nat.add_right_cancel he))
      exact (gaussianNamespaceJoin_other (j + 1) z g ⟨a + 1, hv⟩ i).trans
        (gaussianNamespaceJoin_other (j + 1) 0 g ⟨a + 1, hv⟩ i).symm

/-- Inserting the selected standard Gaussian family adds exactly its
actual amplitude times `jointSpectralMonomialCoefficients`. -/
theorem tensorNamespacedField_insert {N m k : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (x : Spin N × LabeledLeaf n) (z : ℕ → ℝ) (g : OtherNamespaces (j + 1)) :
    cylinderField (tensorNamespacedCoefficients U I degree amplitude n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (z, g)) =
    cylinderField (tensorNamespacedCoefficients U I degree (Function.update amplitude j 0) n
      (fun i => tensorPathProfile I degree n treeDegree h i) x)
      (gaussianNamespaceJoin (j + 1) (0, g)) +
        amplitude j * cylinderField (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x) z := by
  classical
  rw [← tensorNamespacedField_frozen U I degree amplitude n treeDegree h hh h0 j x z g]
  simp_rw [tensorNamespacedField_expand U I degree _ n treeDegree h hh h0]
  let Y := fun a : Fin k => cylinderField
    (jointSpectralMonomialCoefficients U I (degree a) n (treeDegree a) x)
    (fun i => gaussianNamespaceJoin (j + 1) (z, g) (Nat.pair (a + 1) i))
  have he (a : Fin k) : amplitude a * Y a = Function.update amplitude j 0 a * Y a +
      if a = j then amplitude j * Y j else 0 := by
    by_cases ha : a = j
    · subst a; simp
    · simp [ha]
  change _ + ∑ a, amplitude a * Y a = _
  have hsum : (∑ a, amplitude a * Y a) =
      ∑ a, (Function.update amplitude j 0 a * Y a + if a = j then amplitude j * Y j else 0) :=
    Finset.sum_congr rfl (fun a _ => he a)
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have hY : Y j = cylinderField (jointSpectralMonomialCoefficients U I (degree j) n (treeDegree j) x) z := by
    simp only [Y, gaussianNamespaceJoin_selected]
  rw [hY]
  ring

lemma measurable_tensorFrozenBaseEnergy {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (Function.uncurry (tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j)) := by
  change Measurable (fun p : TensorFrozenData N n j × (Spin N × LabeledLeaf n) =>
    tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j p.1 p.2)
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun ω : TensorFrozenData N n j =>
    rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (gaussianNamespaceJoin (j + 1) (0, ω.2)))
  have hrot0 : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul (1 / 2 : ℝ)
  have hrot : Measurable (fun ω : TensorFrozenData N n j => rotatedEnergy eig (specialRotation ω.1.1) x.1) :=
    hrot0.comp measurable_fst.fst
  have hm : Measurable (fun ω : TensorFrozenData N n j =>
      (ω.1.1, gaussianNamespaceJoin (j + 1) (0, ω.2))) :=
    measurable_fst.fst.prodMk ((measurable_gaussianNamespaceJoin (j + 1)).comp
      (measurable_const.prodMk measurable_snd))
  let v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0 :=
    fun i => tensorPathProfile I degree n treeDegree h i
  have hfield0 := measurable_tensorNamespacedFields_joint I degree
    (Function.update amplitude j 0) n v x
  have hfield : Measurable (fun ω : TensorFrozenData N n j =>
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree
        (Function.update amplitude j 0) n v x) (gaussianNamespaceJoin (j + 1) (0, ω.2))) := by
    convert hfield0.comp hm using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  convert (hrot.add_const (fieldEnergy c x.1)).add hfield using 1
  all_goals try with_reducible_and_instances rfl

theorem tensorFrozenEnergy_insert {N m k : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (ω : TensorFrozenData N n j) (z : ℕ → ℝ) (x : Spin N × LabeledLeaf n) :
    rotatedEnergy eig (specialRotation ω.1.1) x.1 + fieldEnergy c x.1 +
      cylinderField (tensorNamespacedCoefficients (specialRotation ω.1.1) I degree amplitude n
        (fun i => tensorPathProfile I degree n treeDegree h i) x)
        (gaussianNamespaceJoin (j + 1) (z, ω.2)) =
      tensorFrozenBaseEnergy eig c I degree amplitude n treeDegree h j ω x +
        amplitude j * cylinderField (jointSpectralMonomialCoefficients
          (specialRotation ω.1.1) I (degree j) n (treeDegree j) x) z := by
  rw [tensorNamespacedField_insert (specialRotation ω.1.1) I degree amplitude n treeDegree h hh h0 j x z ω.2]
  exact (add_assoc _ _ _).symm

/-- The selected field is a genuinely independent Gaussian product factor;
all remaining marks, the rotation, and the tree form external disorder. -/
theorem tensorFrozenInsertion_measurePreserving {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    MeasurePreserving (fun p : TensorFrozenData N n j × (ℕ → ℝ) =>
      (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2)))
      ((tensorFrozenLaw μ n b j).prod gaussianCoordinates)
      ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) :=
  namespaceInsertion_preserving _ _

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
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureDifferenceConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centering a logpartition difference using its two pressure variances. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

/-- The frozen CGF of one perturbation is a scaled difference of two
pressures. Both variances suffice even though those pressures are dependent. -/
theorem centered_scaled_difference_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F G Z : Ω → ℝ} {a B : ℝ}
    (hF : MemLp F 2 P) (hG : MemLp G 2 P)
    (hvF : variance F P ≤ B) (hvG : variance G P ≤ B)
    (he : Z =ᵐ[P] fun ω => a * (F ω - G ω)) :
    MemLp Z 2 P ∧
      (∫ ω, |Z ω - ∫ ω', Z ω' ∂P| ∂P) ≤ 2 * |a| * Real.sqrt B := by
  have hiF := hF.integrable (by norm_num)
  have hiG := hG.integrable (by norm_num)
  have hZ : MemLp Z 2 P := MemLp.ae_eq he.symm ((hF.sub hG).const_mul a)
  have hcF : (∫ ω, |F ω - ∫ ω', F ω' ∂P| ∂P) ≤ Real.sqrt B :=
    (l1_center_le_sqrt_variance hF).trans (Real.sqrt_le_sqrt hvF)
  have hcG : (∫ ω, |G ω - ∫ ω', G ω' ∂P| ∂P) ≤ Real.sqrt B :=
    (l1_center_le_sqrt_variance hG).trans (Real.sqrt_le_sqrt hvG)
  have hc := centered_sub_L1_bound P hiF hiG hcF hcG
  have hm : (∫ ω, Z ω ∂P) = a * (∫ ω, F ω - G ω ∂P) := by
    rw [integral_congr_ae he, integral_const_mul]
  refine ⟨hZ, ?_⟩
  rw [hm]
  calc
    _ = ∫ ω, |a| * |F ω - G ω - ∫ ω', F ω' - G ω' ∂P| ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω, ← mul_sub, abs_mul]
    _ = |a| * (∫ ω, |F ω - G ω - ∫ ω', F ω' - G ω' ∂P| ∂P) := integral_const_mul _ _
    _ ≤ |a| * (Real.sqrt B + Real.sqrt B) :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = _ := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_RandomCoefficientGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! GG estimates for Haar-dependent Gaussian perturbation tensors. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

variable [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

/-- Gaussian mean logpartition bounds remain valid when the coefficient
vectors depend on the external rotation disorder. -/
lemma randomCoefficient_cgf_mean_bounds (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    0 ≤ (∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates) ∧
    (∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
      ∂P.prod gaussianCoordinates) ≤ t ^ 2 * B / 2 := by
  have hi := integrable_randomCoefficient_cgf (P := P) hν A hAm hA t
  rw [integral_prod _ hi]
  refine ⟨integral_nonneg (fun ω => (cylinder_cgf_mean_bounds (ν ω) (A ω) (hA ω) t).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, t ^ 2 * B / 2 ∂P := integral_mono hi.integral_prod_left
      (integrable_const _) (fun ω => (cylinder_cgf_mean_bounds (ν ω) (A ω) (hA ω) t).2)
    _ = _ := by simp

/-- The local-minimum fluctuation estimate applies to the actual
Haar-dependent Gaussian fields, rather than requiring fixed coefficients. -/
theorem randomCoefficient_energy_at_minimum (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {B : ℝ} (hA : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Set.Icc (v - s) (v + s),
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) v
        ∂P.prod gaussianCoordinates) + c * (v - a) ^ 2 ≤
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t
        ∂P.prod gaussianCoordinates) + c * (t - a) ^ 2)
    (hconc : ∀ t ∈ ({v - s, v, v + s} : Set ℝ),
      (∫ z : Ω × (ℕ → ℝ), |cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t -
        (∫ z' : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (A z'.1 x) z'.2) (ν z'.1) t
          ∂P.prod gaussianCoordinates)| ∂P.prod gaussianCoordinates) ≤ δ) :
    let E := fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (A z.1 x) z.2 - 2 * c * (v - a)|
        ∂(ν z.1).tilted (fun x => v * cylinderField (A z.1 x) z.2)
    Integrable E (P.prod gaussianCoordinates) ∧
      (∫ z, E z ∂P.prod gaussianCoordinates) ≤ (2 * c + K ^ 2) / (2 * K) + c * s + 4 * δ / s := by
  exact expected_tilted_energy_at_minimum (μ := P.prod gaussianCoordinates)
    (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (Y := fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2)
    (hν.comp measurable_fst) hAm hs hK
    (randomCoefficient_all_exp_ae hν A hAm hA)
    (integrable_randomCoefficient_cgf hν A hAm hA) hmin hconc

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

lemma bounded_nonnegative_cgf_bounds {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → ℝ) (hY : Measurable Y)
    (hbound : ∀ x, Y x ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cgf Y ν t ∧ cgf Y ν t ≤ t := by
  have he : Integrable (fun x => Real.exp (t * Y x)) ν :=
    exp_mul_integrable_of_bound ν hY
      (fun x => by rw [abs_of_nonneg (hbound x).1]; exact (hbound x).2) t
  have hlo : (1 : ℝ) ≤ ∫ x, Real.exp (t * Y x) ∂ν := by
    calc
      _ = ∫ _ : X, (1 : ℝ) ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) he (fun x =>
        Real.one_le_exp_iff.mpr (mul_nonneg ht (hbound x).1))
  have hhi : (∫ x, Real.exp (t * Y x) ∂ν) ≤ Real.exp t := by
    calc
      _ ≤ ∫ _ : X, Real.exp t ∂ν := integral_mono he (integrable_const _)
        (fun x => Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (hbound x).2 ht).trans_eq (mul_one _)))
      _ = _ := by simp
  constructor
  · exact Real.log_nonneg hlo
  · change Real.log (∫ x, Real.exp (t * Y x) ∂ν) ≤ t
    exact (Real.log_le_log (by linarith) hhi).trans_eq (Real.log_exp t)

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

/-- Unlike the Gaussian perturbation, a diagonal coordinate is a bounded
observable of the random rotation. Its exact tilted fluctuation still follows
from convexity, the deterministic minimum, and three pointwise concentration
bounds. -/
theorem boundedObservable_energy_at_minimum {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω × X → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : ∀ ω x, |Y (ω, x)| ≤ B)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Set.Icc (v - s) (v + s),
      -(∫ ω, cgf (fun x => Y (ω, x)) (ν ω) v ∂P) + c * (v - a) ^ 2 ≤
      -(∫ ω, cgf (fun x => Y (ω, x)) (ν ω) t ∂P) + c * (t - a) ^ 2)
    (hconc : ∀ t ∈ ({v - s, v, v + s} : Set ℝ),
      (∫ ω, |cgf (fun x => Y (ω, x)) (ν ω) t -
        (∫ ω', cgf (fun x => Y (ω', x)) (ν ω') t ∂P)| ∂P) ≤ δ) :
    let E := fun ω => ∫ x, |Y (ω, x) - 2 * c * (v - a)|
      ∂(ν ω).tilted (fun x => v * Y (ω, x))
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤ (2 * c + K ^ 2) / (2 * K) + c * s + 4 * δ / s := by
  apply expected_tilted_energy_at_minimum hν hY hs hK
  · exact ae_of_all _ fun ω t => exp_mul_integrable_of_bound (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) t
  · exact integrable_bounded_random_cgf P ν hν Y hY B hB
  · exact hmin
  · exact hconc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDiagonalPerturbation
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
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

/-- Replacing one diagonal coordinate adds exactly its bounded observable,
even when all other spectral coordinates and the temperature are present. -/
lemma rotatedEnergy_diagonal_coordinate {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) U σ =
      rotatedEnergy (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) U σ +
        N * perturbationScale N * w * projectedOverlap U (I a) σ σ := by
  classical
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN]
  have hs : (∑ b, Function.update v a w b * projectedOverlap U (I b) σ σ) =
      (∑ b, Function.update v a 0 b * projectedOverlap U (I b) σ σ) +
        w * projectedOverlap U (I a) σ σ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [Function.update_self, zero_mul, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Function.update_of_ne hba]
  rw [hs]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian GG bound specialized to the manuscript's spectral/tree kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma measurable_spectralPerturbationFields {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (spectralPerturbationCoefficients U I d n r p.1.1 p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have h := (measurable_jointSpectralMonomialField I d n r x).comp
    (hU.prodMap measurable_id)
  simpa only [spectralPerturbationCoefficients, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorReplicaAverageLaw
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_spectralEntryMonomial {m : ℕ} (d : Fin m → ℕ) :
    Continuous (spectralEntryMonomial d) := by
  exact continuous_finsetProd _ fun a _ => ((continuous_apply a).subtype_val).pow _

lemma continuous_spectralBlockView (m n : ℕ) : Continuous (spectralBlockView m n) := by
  unfold spectralBlockView
  fun_prop

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

lemma spectralJointEntry_tree {N m : ℕ} (U : Rotation N) (I : Fin m → Finset (Fin N))
    (n : ℕ) (x y : Spin N × LabeledLeaf n) :
    (spectralJointEntry U I n x y (Fin.last m) : ℝ) = treeOverlap n x.2 y.2 := by
  simp only [spectralJointEntry, Fin.lastCases_last]

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
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
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

private lemma measurable_finiteReplicaBlock {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (J : Ω → X → X → Y)
    (hJ : Measurable (fun p : Ω × (X × X) => J p.1 p.2.1 p.2.2)) :
    Measurable (fun p : Ω × (Fin z → X) => fun i j : Fin z => J p.1 (p.2 i) (p.2 j)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  have hi : Measurable (fun p : Ω × (Fin z → X) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hj : Measurable (fun p : Ω × (Fin z → X) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact hJ.comp (measurable_fst.prodMk (hi.prodMk hj))

lemma measurable_finiteSpectralBlock {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) :
    Measurable (fun p : SpecialOrthogonal N × (Fin z → Spin N × LabeledLeaf n) =>
      finiteSpectralBlock (specialRotation p.1) I n p.2) := by
  exact measurable_finiteReplicaBlock (fun U => spectralJointEntry (specialRotation U) I n)
    (measurable_spectralJointEntry I n)

private lemma measurable_permutedReplicaTest {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] {z : ℕ}
    (B : Ω → (Fin z → X) → Y) (hB : Measurable (Function.uncurry B))
    (e : Equiv.Perm (Fin z)) (D : Y → ℝ) (hD : Measurable D) :
    Measurable (Function.uncurry (fun U σ => D (B U (σ ∘ e.symm)))) := by
  have hm : Measurable (fun p : Ω × (Fin z → X) => (p.1, p.2 ∘ e.symm)) :=
    measurable_fst.prodMk (Measurable.of_eval fun i => (measurable_pi_apply (e.symm i)).comp measurable_snd)
  exact hD.comp (hB.comp hm)

lemma measurable_permutedSpectralBlockTest {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (hD : Continuous D) :
    Measurable (Function.uncurry (permutedSpectralBlockTest I n e D)) := by
  exact measurable_permutedReplicaTest (fun U => finiteSpectralBlock (specialRotation U) I n)
    (measurable_finiteSpectralBlock I n) e D hD.measurable

lemma permutedSpectralBlockTest_embedding {N m z : ℕ}
    (I : Fin m → Finset (Fin N)) (n : ℕ) (e : Equiv.Perm (Fin z))
    (D : SpectralBlock (m + 1) z → ℝ) (U : SpecialOrthogonal N)
    (σ : ℕ → Spin N × LabeledLeaf n) :
    permutedSpectralBlockTest I n e D U (fun j => σ (e j)) =
      D (spectralBlockView (m + 1) z (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) := by
  apply congrArg D
  funext i j
  simp only [finiteSpectralBlock, Function.comp_apply,
    Equiv.apply_symm_apply, spectralBlockView]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayResidual
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite tensor GG residual is the spectral-array residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralJointEntry_monomial {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n) (d : Fin (m + 1) → ℕ) :
    spectralEntryMonomial d (spectralJointEntry U I n x y) =
      (∏ a, projectedOverlap U (I a) x.1 y.1 ^ d a.castSucc) *
        treeOverlap n x.2 y.2 ^ d (Fin.last m) := by
  unfold spectralEntryMonomial
  rw [Fin.prod_univ_castSucc]
  simp only [spectralJointEntry_spectral, spectralJointEntry_tree]

lemma spectralJointEntry_selectedMonomial {N m : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ) (x y : Spin N × LabeledLeaf n)
    (d : Fin m → ℕ) (r : ℕ) :
    spectralEntryMonomial (Fin.lastCases r d) (spectralJointEntry (specialRotation U) I n x y) =
      spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I d n r U x y := by
  rw [spectralJointEntry_monomial]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, spectralPerturbationKernel, id_eq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldDerivativeIntegrability
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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

lemma measurable_tensorDeterministicEnergy {N : ℕ} (eig c : Fin N → ℝ) (n : ℕ) :
    Measurable (Function.uncurry (tensorDeterministicEnergy eig c n)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun U : SpecialOrthogonal N => rotatedEnergy eig (specialRotation U) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add_const (fieldEnergy c x.1)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Pressure_PressureCoordinateMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of a pressure-coordinate minimum to its selected-field CGF. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma pressureCoordinate_minimum_rescale {M L : ℝ → ℝ} {N a w s c : ℝ}
    (hN : 0 ≤ N) (ha : 0 < a) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (hlo : 1 ≤ w - s) (hhi : w + s ≤ 2)
    (hmean : ∀ v ∈ Set.Icc (1 : ℝ) 2, L (a * v) = N * (M v - M 0))
    (hmin : ∀ v ∈ Set.Icc (1 : ℝ) 2,
      -M w + c * (w - 3 / 2) ^ 2 ≤ -M v + c * (v - 3 / 2) ^ 2) :
    ∀ t ∈ Set.Icc (a * w - a * s) (a * w + a * s),
      -L (a * w) + (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 ≤
      -L t + (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 := by
  intro t ht
  have htv : t / a ∈ Set.Icc (1 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ ha).mpr
      nlinarith [ht.1]
    · apply (div_le_iff₀ ha).mpr
      nlinarith [ht.2]
  have hm := hmean (t / a) htv
  rw [mul_div_cancel₀ _ ha.ne'] at hm
  rw [hm, hmean w hw]
  have hc := mul_le_mul_of_nonneg_left (hmin (t / a) htv) hN
  have he1 : (N * c / a ^ 2) * (a * w - a * (3 / 2)) ^ 2 =
      N * (c * (w - 3 / 2) ^ 2) := by field_simp
  have he2 : (N * c / a ^ 2) * (t - a * (3 / 2)) ^ 2 =
      N * (c * (t / a - 3 / 2) ^ 2) := by field_simp
  rw [he1, he2]
  linarith

/-- Comparing a Gaussian-coordinate minimum with its centered choice
puts it in the interior, using the Gaussian variance cap of the frozen field. -/
lemma gaussianCoordinate_minimum_penalty {N : ℕ} (hN : 0 < N) (j : Fin N)
    (M : ℝ → ℝ) (u : ℝ) (hu : |u| ≤ 2)
    (hcost : 0 ≤ M (3 / 2) - M 0 ∧ M u - M 0 ≤ (perturbationAmplitude N j * u) ^ 2 / (2 * N))
    (hmin : -M u + perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      -M (3 / 2) + perturbationWeight j * (3 / 2 - 3 / 2) ^ 2) :
    (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := perturbationWeight_pos j
  have ha := perturbationAmplitude_sq N j
  have hu2 : u ^ 2 ≤ 4 := by
    have hb := abs_le.mp hu
    nlinarith [sq_nonneg (u + 2), sq_nonneg (u - 2)]
  have hanu : (perturbationAmplitude N j * u) ^ 2 / (2 * N) ≤
      2 * perturbationScale N ^ 2 * perturbationWeight j ^ 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (N : ℝ) by positivity)).mpr
    rw [mul_pow, ha]
    nlinarith [mul_le_mul_of_nonneg_left hu2
      (show 0 ≤ (N : ℝ) * perturbationScale N ^ 2 * perturbationWeight j ^ 2 by positivity)]
  have hm : perturbationWeight j * (u - 3 / 2) ^ 2 ≤
      perturbationWeight j * (2 * perturbationScale N ^ 2 * perturbationWeight j) := by
    nlinarith [hcost.1, hcost.2]
  exact (mul_le_mul_iff_right₀ hw).mp hm

lemma gaussianCoordinate_minimum_interior {N : ℕ} (j : Fin N) {u s : ℝ}
    (hpen : (u - 3 / 2) ^ 2 ≤ 2 * perturbationScale N ^ 2 * perturbationWeight j)
    (he : perturbationScale N ≤ 1 / 8) (hs : s ≤ 1 / 4) :
    1 ≤ u - s ∧ u + s ≤ 2 := by
  have he0 := perturbationScale_nonneg N
  have hw := perturbationWeight_le_one j
  have hbnd : (u - 3 / 2) ^ 2 ≤ 1 / 32 := by
    have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * perturbationScale N ^ 2 by positivity)
    nlinarith [sq_nonneg (perturbationScale N - 1 / 8)]
  constructor <;> nlinarith [sq_nonneg (u - 3 / 2 - 1 / 4), sq_nonneg (u - 3 / 2 + 1 / 4)]

lemma diagonalCoordinate_minimum_penalty {M : ℝ → ℝ} {w e : ℝ}
    (hcost : 0 ≤ M (3 / 2) - M 0 ∧ M w - M 0 ≤ 2 * e)
    (hmin : -M w + (w - 3 / 2) ^ 2 ≤ -M (3 / 2) + (3 / 2 - 3 / 2) ^ 2) :
    (w - 3 / 2) ^ 2 ≤ 2 * e := by
  nlinarith [hcost.1, hcost.2]

lemma diagonalCoordinate_minimum_interior {w e s : ℝ}
    (hpen : (w - 3 / 2) ^ 2 ≤ 2 * e) (he : e ≤ 1 / 32) (hs : s ≤ 1 / 4) :
    1 ≤ w - s ∧ w + s ≤ 2 := by
  constructor <;> nlinarith [sq_nonneg (w - 3 / 2 - 1 / 4), sq_nonneg (w - 3 / 2 + 1 / 4)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_PriorMinimumFluctuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing self-overlap fluctuation in the actual constrained-prior Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma sqrt_dimension_mul {N : ℕ} (hN : 0<N) (L : ℝ) :
    Real.sqrt (N*L) = N*Real.sqrt (L/N) := by
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (N : ℝ)*L=(N : ℝ)^2*(L/N) := by field_simp
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorExponential
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential integrability of the actual cascade-enriched Hamiltonian
for a normalized deterministic spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n π p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n π ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n π ω.2)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) :=
    finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ)
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorDeterministicEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_tensorNamespacedPathFields I degree amplitude n treeDegree h
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFrozenReference
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One independent Gaussian coordinate frozen inside the actual constrained
cascade model. The cascade tree remains part of the external disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

lemma measurable_spinPriorFrozenReference {N m k : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ)
    (h : ℕ → ℝ) (j : Fin k) :
    Measurable (spinPriorFrozenReference π eig c I degree amp n r h j) := by
  have : ∀ ω : TensorFrozenData N n j, IsProbabilityMeasure
      ((labeledSpinReference n π ∘ fun ω : TensorFrozenData N n j => ω.1.2) ω) := fun ω => by
        change IsProbabilityMeasure (labeledSpinReference n π ω.1.2)
        first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact measurable_gibbsProbability
    (H := Function.uncurry (tensorFrozenBaseEnergy eig c I degree amp n r h j))
    ((measurable_labeledSpinReference_general n π).comp measurable_fst.snd)
    (measurable_tensorFrozenBaseEnergy eig c I degree amp n r h j)

theorem spinPriorFrozenBase_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) :
    ∀ᵐ ω ∂tensorFrozenLaw μ n b j,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amp n r h j ω x))
        (labeledSpinReference n π ω.1.2) := by
  have he := (tensorFrozenInsertion_measurePreserving μ n b j).quasiMeasurePreserving.ae
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree (Function.update amp j 0) n b r h hh h0)
  have he' : ∀ᵐ p : TensorFrozenData N n j × (ℕ → ℝ)
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amp n r h j p.1 x))
        (labeledSpinReference n π p.1.1.2) := by
    filter_upwards [he] with p hp
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    congr 1
    unfold tensorFrozenBaseEnergy
    rw [tensorNamespacedField_frozen (specialRotation p.1.1.1) I degree amp n r h hh h0 j x p.2 p.1.2]
  filter_upwards [Measure.ae_ae_of_ae_prod he'] with ω hω
  obtain ⟨z,hz⟩ := hω.exists
  exact hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFrozenGibbs
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen Gaussian and diagonal tilts reconstruct the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem spinPriorFrozenDiagonal_reference_fold_ae {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    ∀ᵐ p : TensorFlatDisorder N n
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude r h p).tilted
        (fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
          projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1) =
      spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude r h p := by
  have hb := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hh h0
  have hw := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h hh h0
  filter_upwards [hb, hw] with p hp₀ hpw
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n r h p
  let G := fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
    projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1
  have he : tensorNamespacedHamiltonian
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n r h p =
      fun x => H x + G x := by
    funext x
    dsimp only [tensorNamespacedHamiltonian, H, G]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1.1) I v t a w x.1]
    ring
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    convert hpw using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact congrArg Real.exp (congrFun he x).symm
  change (gibbsProbability ν H).tilted G = gibbsProbability ν
    (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
      c I degree amplitude n r h p)
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp₀
  rw [he, gibbsProbability_eq_tilted ν H hH, gibbsProbability_eq_tilted ν (fun x => H x + G x) hi]
  rw [tilted_tilted hH G]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorArrayLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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
theorem spinPriorArrayLaw_test {N m k z : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F)
    (D : SpecialOrthogonal N → (Fin z → Spin N × LabeledLeaf n) → ℝ)
    (ι : Fin z → ℕ) (hi : Function.Injective ι)
    (he : ∀ (U : SpecialOrthogonal N) (σ : ℕ → Spin N × LabeledLeaf n), F (fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2)) = D U (fun i => σ (ι i))) :
    (∫ x, F x ∂(spinPriorArrayLaw μ π eig c I degree amplitude n b r h :
      Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h D := by
  rw [spinPriorArrayLaw, spectralArrayLaw_integral _ _ _ _ _ _ _ F hF]
  unfold spinPriorReplicaAverage
  simp only [referenceReplicaMean_zero]
  apply integral_congr_ae
  filter_upwards [] with p
  have hm : Measurable (fun σ : ℕ → Spin N × LabeledLeaf n => fun i : Fin z => σ (ι i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ι i)
  let ν := spinPriorNamespacedReference (n := n) π eig c I degree amplitude r h p
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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorObservableAverageLaw
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both frozen coordinates control observables in the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

theorem spinPriorFrozenDiagonal_observableAverage {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ)
    (D : SpecialOrthogonal N → (Spin N × LabeledLeaf n) → ℝ) :
    (∫ p : TensorFlatDisorder N n, ∫ x, D p.1.1 x
      ∂(spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude r h p).tilted
        (fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
          projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) =
      spinPriorObservableAverage μ π
        (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude b r h D := by
  apply integral_congr_ae
  filter_upwards [spinPriorFrozenDiagonal_reference_fold_ae hN μ π eig c I degree amplitude n b r h hh h0 v t a w]
    with p hp
  rw [hp]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorArrayResidual
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact equality of the constrained finite-model and spectral-array GG residuals. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

/-- Common rotation is retained in every finite test; arbitrary replica
indices are handled by injective sampling, not by independence of rotations. -/
theorem spinPriorArrayLaw_residual {N m k n q : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (e : Equiv.Perm (Fin (q + 1))) (D : SpectralBlock (m + 1) (q + 1) → ℝ) (hD : Continuous D) :
    spectralMonomialResidual (spinPriorArrayLaw μ π eig c I degree amplitude n b r h)
      (q + 1) (e 0) D (Fin.lastCases (r j) (degree j)) =
      spinPriorSpectralGGResidual μ π b eig c I degree amplitude r h j
        (permutedSpectralBlockTest I n e D) := by
  classical
  let L := spinPriorArrayLaw μ π eig c I degree amplitude n b r h
  let d : Fin (m + 1) → ℕ := Fin.lastCases (r j) (degree j)
  let D' := permutedSpectralBlockTest I n e D
  let κ := spectralPerturbationKernel (id : SpecialOrthogonal N → SpecialOrthogonal N) I (degree j) n (r j)
  have hcD : Continuous (fun x => D (spectralBlockView (m + 1) (q + 1) x)) :=
    hD.comp (continuous_spectralBlockView _ _)
  have hmono : Continuous (spectralEntryMonomial d) := continuous_spectralEntryMonomial d
  have hnew : (∫ x, D (spectralBlockView (m + 1) (q + 1) x) *
      spectralEntryMonomial d (x (e 0, q + 1)) ∂(L : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h
        (fun U (τ : Fin (q + 1 + 1) → Spin N × LabeledLeaf n) =>
          D' U (Fin.tail τ) * κ U ((Fin.tail τ) 0) (τ 0)) := by
    apply spinPriorArrayLaw_test μ π eig c I degree amplitude n b r h
      _ (hcD.mul (hmono.comp (continuous_apply _))) _
      (newReplicaEmbedding (q + 1) e) (newReplicaEmbedding_injective _ e)
    intro U σ
    simp only [Pi.mul_apply, Function.comp_apply, newReplicaEmbedding, Fin.cases_zero, Fin.cases_succ, Fin.tail]
    change D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) *
        spectralEntryMonomial d (spectralJointEntry (specialRotation U) I n (σ (e 0)) (σ (q + 1))) =
      D' U (fun i => σ (e i)) * κ U (σ (e 0)) (σ (q + 1))
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    simp only [spectralJointEntry_selectedMonomial, d, κ]
  have hblock : (∫ x, D (spectralBlockView (m + 1) (q + 1) x)
      ∂(L : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h D' := by
    apply spinPriorArrayLaw_test μ π eig c I degree amplitude n b r h _ hcD D'
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    exact (permutedSpectralBlockTest_embedding I n e D U σ).symm
  have hpair : (∫ x, spectralEntryMonomial d (x (0, 1))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h
        (fun U (τ : Fin 2 → Spin N × LabeledLeaf n) => κ U (τ 1) (τ 0)) := by
    refine spinPriorArrayLaw_test μ π eig c I degree amplitude n b r h _
      (hmono.comp (continuous_apply _)) _ ![1, 0] ?_ ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro U σ
      exact spectralJointEntry_selectedMonomial U I n (σ 0) (σ 1) (degree j) (r j)
  have hsum : (∑ a ∈ Finset.univ.erase (e 0), ∫ x,
      D (spectralBlockView (m + 1) (q + 1) x) * spectralEntryMonomial d (x (e 0, a))
      ∂(L : Measure (SpectralArray (m + 1)))) =
      spinPriorReplicaAverage μ π eig c I degree amplitude n b r h
        (fun U σ => D' U σ * ∑ l : Fin q, κ U (σ 0) (σ l.succ)) := by
    have hI (a : Fin (q + 1)) : Integrable
        (fun x : SpectralArray (m + 1) => D (spectralBlockView (m + 1) (q + 1) x) *
          spectralEntryMonomial d (x (e 0, a))) (L : Measure (SpectralArray (m + 1))) :=
      compact_integrable (hcD.mul (hmono.comp (continuous_apply _)))
    rw [← integral_finsetSum _ (fun a _ => hI a)]
    apply spinPriorArrayLaw_test μ π eig c I degree amplitude n b r h
      _ (continuous_finsetSum _ fun a _ => hcD.mul (hmono.comp (continuous_apply _))) _
      (fun i => (e i).val) (Fin.val_injective.comp e.injective)
    intro U σ
    rw [show D' U (fun i => σ ((e i).val)) =
      D (spectralBlockView (m + 1) (q + 1) (fun ij : ℕ × ℕ =>
        spectralJointEntry (specialRotation U) I n (σ ij.1) (σ ij.2))) from
      permutedSpectralBlockTest_embedding I n e D U σ]
    rw [sum_nonzero_permutation e (fun a => κ U (σ (e 0)) (σ a)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.mul_apply, Function.comp_apply, d, spectralJointEntry_selectedMonomial, κ]
  unfold spectralMonomialResidual
  rw [hnew, hblock, hpair, hsum]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorFrozenCGF
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen Gaussian cumulants in the actual constrained cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorFrozenCGF_eq_log_difference {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) (t : ℝ) :
    spinPriorFrozenCGF π eig c I degree amp n r h j t =ᵐ[(tensorFrozenLaw μ n b j).prod gaussianCoordinates]
      fun p => spinPriorNamespacedLog π eig c I degree (Function.update amp j t) r h
          (p.1.1, gaussianNamespaceJoin (j+1) (p.2,p.1.2))-
        spinPriorNamespacedLog π eig c I degree (Function.update amp j 0) r h
          (p.1.1, gaussianNamespaceJoin (j+1) (p.2,p.1.2)) := by
  have hbase := (measurePreserving_fst (μ := tensorFrozenLaw μ n b j)
    (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (spinPriorFrozenBase_exp_integrable_ae μ π eig c I degree amp n b r h hh h0 j)
  have hfull := (tensorFrozenInsertion_measurePreserving μ n b j).quasiMeasurePreserving.ae
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree (Function.update amp j t) n b r h hh h0)
  filter_upwards [hbase,hfull] with p hb hf
  let ν := labeledSpinReference n π p.1.1.2
  let H := tensorFrozenBaseEnergy eig c I degree amp n r h j p.1
  let Y := fun x : Spin N × LabeledLeaf n => cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2
  have he (a : ℝ) (x : Spin N × LabeledLeaf n) :
      tensorNamespacedHamiltonian eig c I degree (Function.update amp j a) n r h
        (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x = H x+a*Y x := by
    simpa only [H,Y,tensorNamespacedHamiltonian,tensorFrozenBaseEnergy,Function.update_idem,Function.update_self] using
      tensorFrozenEnergy_insert eig c I degree (Function.update amp j a) n r h hh h0 j p.1 p.2 x
  have hi : Integrable (fun x => Real.exp (H x+t*Y x)) ν := by
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact congrArg Real.exp (he t x).symm
  change cgf Y (gibbsProbability ν H) t = _
  rw [cgf_fold ν H Y t hb hi]
  change Real.log (∫ x, Real.exp (H x+t*Y x) ∂ν)-Real.log (∫ x, Real.exp (H x) ∂ν) = _
  change _ = Real.log (∫ x, Real.exp (tensorNamespacedHamiltonian eig c I degree
    (Function.update amp j t) n r h (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x) ∂ν)-
    Real.log (∫ x, Real.exp (tensorNamespacedHamiltonian eig c I degree
      (Function.update amp j 0) n r h (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2)) x) ∂ν)
  simp only [he,zero_mul,add_zero]

theorem spinPriorFrozenCGF_statistics {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) (t B : ℝ)
    (hF : ∀ a : ℝ, a=t ∨ a=0 →
      MemLp (spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h) 2
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ a : ℝ, a=t ∨ a=0 →
      variance (spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h)
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤ B) :
    let P := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let Q := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let M := fun a => ∫ p, spinPriorNamespacedLog π eig c I degree (Function.update amp j a) r h p ∂Q
    let Z := spinPriorFrozenCGF π eig c I degree amp n r h j t
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M t-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P) ≤ 2*Real.sqrt B := by
  intro P Q M Z
  let F := fun a => spinPriorNamespacedLog (n := n) π eig c I degree (Function.update amp j a) r h
  let J := fun p : TensorFrozenData N n j × (ℕ → ℝ) =>
    (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2))
  have hp : MeasurePreserving J P Q := tensorFrozenInsertion_measurePreserving μ n b j
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F t (J p)-F 0 (J p)) := by
    simpa only [one_mul] using spinPriorFrozenCGF_eq_log_difference μ π eig c I degree amp n b r h hh h0 j t
  have ht := hF t (Or.inl rfl)
  have hz := hF 0 (Or.inr rfl)
  have hc := centered_scaled_difference_L1_bound P
    (ht.comp_measurePreserving hp) (hz.comp_measurePreserving hp)
    ((hp.variance_fun_comp ht.aemeasurable).trans_le (hv t (Or.inl rfl)))
    ((hp.variance_fun_comp hz.aemeasurable).trans_le (hv 0 (Or.inr rfl))) he
  refine ⟨hc.1,?_,?_⟩
  · rw [integral_congr_ae he]
    simp only [one_mul]
    exact (integral_sub ((ht.comp_measurePreserving hp).integrable (by norm_num))
      ((hz.comp_measurePreserving hp).integrable (by norm_num))).trans
      (congrArg₂ (·-·) (hp.hasLaw.integral_comp ht.aestronglyMeasurable)
        (hp.hasLaw.integral_comp hz.aestronglyMeasurable))
  · simpa only [abs_one,mul_one,one_mul] using hc.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorGaussianMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected Gaussian energy at the actual constrained-prior minimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorFrozenCGF_mean_bounds {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) (t : ℝ) :
    0≤(∫ p, spinPriorFrozenCGF π eig c I degree amplitude n r h j t p
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
    (∫ p, spinPriorFrozenCGF π eig c I degree amplitude n r h j t p
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates)≤t^2/2 := by
  let U : TensorFrozenData N n j → SpecialOrthogonal N := fun ω => ω.1.1
  have hb := randomCoefficient_cgf_mean_bounds
    (P := tensorFrozenLaw μ n b j) (measurable_spinPriorFrozenReference π eig c I degree amplitude n r h j)
    (spectralPerturbationCoefficients U I (degree j) n (r j))
    (measurable_spectralPerturbationFields U measurable_fst.fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation (U ω)) I (degree j) n (r j) x) t
  simpa only [spinPriorFrozenCGF,spectralPerturbationCoefficients,U,mul_one] using hb

theorem spinPriorGaussian_energy_at_minimum {N m n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (amplitude : Fin N → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin N) (w s K B : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/8)
    (hs : 0 < s) (hs' : s≤1/4) (hK : 0<K)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        r h) 2 (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        r h) (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))≤B)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*q))
        r h p ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
      ∀ q∈Set.Icc (1 : ℝ) 2,
        -M w+perturbationWeight j*(w-3/2)^2≤-M q+perturbationWeight j*(q-3/2)^2) :
    let a := perturbationAmplitude N j
    let c₀ := N*perturbationWeight j/a^2
    let P := (tensorFrozenLaw μ n b j).prod gaussianCoordinates
    let A := fun ω : TensorFrozenData N n j =>
      jointSpectralMonomialCoefficients (specialRotation ω.1.1) I (degree j) n (r j)
    let ν := spinPriorFrozenReference π eig c I degree amplitude n r h j
    let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
      |cylinderField (A p.1 x) p.2-2*c₀*(a*w-a*(3/2))|
      ∂(ν p.1).tilted (fun x => a*w*cylinderField (A p.1 x) p.2)
    Integrable E P ∧ (∫ p, E p ∂P)≤
      (2*c₀+K^2)/(2*K)+c₀*(a*s)+4*(2*Real.sqrt B)/(a*s) := by
  intro a c₀ P A ν E
  let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π eig c I degree
    (Function.update amplitude j (a*q)) r h p
    ∂((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
  let L := fun t => ∫ p, spinPriorFrozenCGF π eig c I degree amplitude n r h j t p ∂P
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have ha : 0<a := perturbationAmplitude_pos hN j
  have hstat (q : ℝ) (hq : |q|≤2) := spinPriorFrozenCGF_statistics μ π eig c I degree amplitude
    n b r h hh h0 j (a*q) B
    (fun b hb => by
      rcases hb with rfl | rfl
      · exact hF q hq
      · simpa only [mul_zero] using hF 0 (by norm_num))
    (fun b hb => by
      rcases hb with rfl | rfl
      · exact hv q hq
      · simpa only [mul_zero] using hv 0 (by norm_num))
  have hmean (q : ℝ) (hq : |q|≤2) : L (a*q)=N*(M q-M 0) := by
    dsimp only [L,P,M]
    rw [(hstat q hq).2.1]
    simp only [mul_zero]
    field_simp [hn.ne']
  have hcost (q : ℝ) (hq : |q|≤2) :
      0≤M q-M 0 ∧ M q-M 0≤(a*q)^2/(2*N) := by
    have hb := spinPriorFrozenCGF_mean_bounds (n := n) μ π b eig c I degree amplitude r h j (a*q)
    change 0≤L (a*q) ∧ L (a*q)≤(a*q)^2/2 at hb
    rw [hmean q hq] at hb
    refine ⟨(mul_nonneg_iff_of_pos_left hn).mp hb.1,?_⟩
    apply (le_div_iff₀ (show 0<2*(N : ℝ) by positivity)).mpr
    nlinarith [hb.2]
  have hwa : |w|≤2 := abs_le.mpr ⟨by linarith [hw.1],hw.2⟩
  have hpen := gaussianCoordinate_minimum_penalty hN j M w hwa
    ⟨(hcost (3/2) (by norm_num)).1,(hcost w hwa).2⟩
    (hmin (3/2) (by constructor <;> norm_num))
  obtain ⟨hlo,hhi⟩ := gaussianCoordinate_minimum_interior j hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) ha hw hlo hhi
    (fun q hq => hmean q (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩)) hmin
  have hconc (t : ℝ) (ht : t∈({a*w-a*s,a*w,a*w+a*s} : Set ℝ)) :
      (∫ p, |spinPriorFrozenCGF π eig c I degree amplitude n r h j t p-L t| ∂P)≤2*Real.sqrt B := by
    have hti : t∈Set.Icc (a*w-a*s) (a*w+a*s) := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos ha hs]
    have htq : t/a∈Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ ha).mpr
        nlinarith [hti.1]
      · apply (div_le_iff₀ ha).mpr
        nlinarith [hti.2]
    have hta : |t/a|≤2 := abs_le.mpr ⟨by linarith [htq.1],htq.2⟩
    simpa only [mul_div_cancel₀ _ ha.ne'] using (hstat (t/a) hta).2.2
  exact randomCoefficient_energy_at_minimum (P := tensorFrozenLaw μ n b j)
    (measurable_spinPriorFrozenReference π eig c I degree amplitude n r h j) A
    (measurable_spectralPerturbationFields (fun ω : TensorFrozenData N n j => ω.1.1)
      measurable_fst.fst I (degree j) n (r j))
    (fun ω x => jointSpectralMonomialCoefficients_variance_le_one
      (specialRotation ω.1.1) I (degree j) n (r j) x) (mul_pos ha hs) hK hlocal hconc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorDiagonalStatistics
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal CGF and pressure concentration for the actual constrained
cascade model. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

/-- At its true coefficient `N e_N w`, a frozen diagonal tilt is exactly
the actual perturbed partition difference. -/
theorem spinPriorDiagonalCGF_eq_log_difference {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (N * perturbationScale N * w) =ᵐ[
      (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates]
      (fun p => spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude r h p -
        spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
          c I degree amplitude r h p) := by
  have he := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hh h0
  filter_upwards [he] with p hp
  let H := tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n r h p
  let Y := fun x : Spin N × LabeledLeaf n => projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1
  have hbnd : ∀ x, |(N * perturbationScale N * w) * Y x| ≤ |N * perturbationScale N * w| := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (projectedOverlap_abs_le_one _ _ _ _) (abs_nonneg _)).trans_eq (mul_one _)
  have ht : Integrable (fun x => Real.exp (H x + (N * perturbationScale N * w) * Y x))
      (labeledSpinReference n π p.1.2) := by
    simpa only [add_comm] using integrable_exp_bounded_add (H := H)
      (B := fun x => (N * perturbationScale N * w) * Y x) hp (measurable_of_countable _)
      (fun x => (le_abs_self _).trans (hbnd x))
  have heq : (fun x => H x + (N * perturbationScale N * w) * Y x) =
      tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude n r h p := by
    funext x
    dsimp only [H, Y, tensorNamespacedHamiltonian]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1.1) I v t a w x.1]
    ring
  change cgf Y (gibbsProbability _ H) _ = _
  rw [cgf_fold _ H Y _ hp ht, heq]
  rfl

theorem spinPriorDiagonalCGF_statistics {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w B : ℝ)
    (hF : ∀ q : ℝ, q=w ∨ q=0 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)))
    (hv : ∀ q : ℝ, q=w ∨ q=0 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) (((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)) ≤ B) :
    let P := ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)
    let M := fun q => ∫ p, spinPriorNamespacedLog (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
      c I degree amplitude r h p ∂P
    let Z := spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (N*perturbationScale N*w)
    MemLp Z 2 P ∧ (∫ p, Z p ∂P)=M w-M 0 ∧
      (∫ p, |Z p-∫ p', Z p' ∂P| ∂P)≤2*Real.sqrt B := by
  intro P M Z
  let F := fun q => spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
    c I degree amplitude r h
  have he : Z =ᵐ[P] fun p => (1 : ℝ)*(F w p-F 0 p) := by
    filter_upwards [spinPriorDiagonalCGF_eq_log_difference hN μ π eig c I degree amplitude
      n b r h hh h0 v t a w] with p hp
    simpa only [one_mul,Z,F,spinPriorDiagonalCGF] using hp
  have hc := centered_scaled_difference_L1_bound P (hF w (Or.inl rfl))
    (hF 0 (Or.inr rfl)) (hv w (Or.inl rfl)) (hv 0 (Or.inr rfl)) he
  refine ⟨hc.1,?_,?_⟩
  · rw [integral_congr_ae he]
    simp only [one_mul]
    exact integral_sub ((hF w (Or.inl rfl)).integrable (by norm_num))
      ((hF 0 (Or.inr rfl)).integrable (by norm_num))
  · simpa only [abs_one,mul_one,one_mul] using hc.2


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorDiagonalMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral self-overlap estimate at a actual quenched constrained-cascade pressure minimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorDiagonal_energy_at_minimum {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w s K B : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/32)
    (hs : 0 < s) (hs' : s≤1/4) (hK : 0<K)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤B)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2, -M w+(w-3/2)^2≤-M q+(q-3/2)^2) :
    let A := N*perturbationScale N
    let c₀ := N/A^2
    let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let ν := spinPriorNamespacedReference (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude
      r h
    let Y := fun p : (TensorFlatDisorder N n) × (Spin N × LabeledLeaf n) =>
      projectedOverlap (specialRotation p.1.1.1) (I a) p.2.1 p.2.1
    let E := fun p : TensorFlatDisorder N n => ∫ x, |Y (p,x)-2*c₀*(A*w-A*(3/2))|
      ∂(ν p).tilted (fun x => A*w*Y (p,x))
    Integrable E P ∧ (∫ p, E p ∂P)≤
      (2*c₀+K^2)/(2*K)+c₀*(A*s)+4*(2*Real.sqrt B)/(A*s) := by
  intro A c₀ P ν Y E
  let Q := P
  let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
    (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
    c I degree amplitude r h p ∂P
  let L := fun z => ∫ p, spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a z p ∂Q
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 < A := mul_pos hn (Real.rpow_pos_of_pos hn _)
  have hY : Measurable Y := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_projectedOverlap (I a) x.1 x.1).comp measurable_fst.fst
  have hYb (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) :
      Y (p, x) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨projectedOverlap_self_nonneg _ _ _, projectedOverlap_self_le_one _ _ _⟩
  have hstat (q : ℝ) (hq : |q| ≤ 2) :=
    spinPriorDiagonalCGF_statistics hN μ π b eig c I degree amplitude r h hh h0 v t a q B
      (fun z hz => by
        rcases hz with hz | hz
        · rw [hz]
          exact hF q hq
        · rw [hz]
          exact hF 0 (by norm_num))
      (fun z hz => by
        rcases hz with hz | hz
        · rw [hz]
          exact hv q hq
        · rw [hz]
          exact hv 0 (by norm_num))
  have hmean (q : ℝ) (hq : |q| ≤ 2) : L (A * q) = N * (M q - M 0) := by
    dsimp only [L,A,Q,P,M]
    rw [(hstat q hq).2.1]
    have hn0 := hn.ne'
    field_simp
  have hcost (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 2) :
      0 ≤ M q - M 0 ∧ M q - M 0 ≤ 2 * perturbationScale N := by
    have hqa : |q| ≤ 2 := abs_le.mpr ⟨by linarith [hq.1], hq.2⟩
    have hqb : ∀ p, 0 ≤ spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (A * q) p ∧
        spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (A * q) p ≤ A * q := by
      intro p
      exact bounded_nonnegative_cgf_bounds (ν p) (fun x => Y (p, x))
        (measurable_of_countable _) (hYb p) (mul_nonneg hA.le (by linarith [hq.1]))
    have hlo : 0 ≤ L (A * q) := integral_nonneg (fun p => (hqb p).1)
    have hhi : L (A * q) ≤ A * q := by
      calc
        _ ≤ ∫ _ : TensorFlatDisorder N n, A * q ∂Q :=
          integral_mono ((hstat q hqa).1.integrable (by norm_num)) (integrable_const _) (fun p => (hqb p).2)
        _ = _ := by simp [Q,P]
    rw [hmean q hqa] at hlo hhi
    have hbound := mul_le_mul_of_nonneg_left hq.2 hA.le
    refine ⟨(mul_nonneg_iff_of_pos_left hn).mp hlo, ?_⟩
    dsimp only [A] at hbound hhi
    nlinarith
  have hpen := diagonalCoordinate_minimum_penalty
    ⟨(hcost (3 / 2) (by constructor <;> norm_num)).1, (hcost w hw).2⟩
    (hmin (3 / 2) (by constructor <;> norm_num))
  obtain ⟨hlo, hhi⟩ := diagonalCoordinate_minimum_interior hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) hA hw hlo hhi
    (fun q hq => hmean q (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩))
    (show ∀ q ∈ Set.Icc (1 : ℝ) 2, -M w + 1 * (w - 3 / 2) ^ 2 ≤
      -M q + 1 * (q - 3 / 2) ^ 2 by simpa only [one_mul] using hmin)
  have hconc (z : ℝ) (hz : z ∈ ({A * w - A * s, A * w, A * w + A * s} : Set ℝ)) :
      (∫ p, |spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a z p - L z| ∂Q) ≤
        2 * Real.sqrt B := by
    have hzi : z ∈ Set.Icc (A * w - A * s) (A * w + A * s) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos hA hs]
    have hzq : z / A ∈ Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hA).mpr
        nlinarith [hzi.1]
      · apply (div_le_iff₀ hA).mpr
        nlinarith [hzi.2]
    have hza : |z / A| ≤ 2 := abs_le.mpr ⟨by linarith [hzq.1], hzq.2⟩
    have hc := (hstat (z / A) hza).2.2
    simpa only [A, mul_div_cancel₀ _ hA.ne'] using hc
  simpa only [mul_one] using boundedObservable_energy_at_minimum Q ν
    (measurable_spinPriorNamespacedReference (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude r h)
    Y hY 1 (fun p x => projectedOverlap_abs_le_one _ _ _ _)
    (mul_pos hA hs) hK hlocal hconc

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorMinimumFluctuations
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing self-overlap fluctuation in the actual constrained-prior Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorDiagonal_fluctuation_at_minimum {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w L : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/32) (hs : contactStep N≤1/4)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2, -M w+(w-3/2)^2≤-M q+(q-3/2)^2) :
    let A := N*perturbationScale N
    let center := 2*(N/A^2)*(A*w-A*(3/2))
    spinPriorObservableAverage (n := n) μ π
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-center|)≤diagonalContactRate N L := by
  intro A center
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < 1 / (Real.sqrt N * perturbationScale N) :=
    one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr hn) he')
  have hE := spinPriorDiagonal_energy_at_minimum hN μ π b eig c I degree amplitude r h hh h0 v t a
    w (contactStep N) (1 / (Real.sqrt N * perturbationScale N)) (N * L) hw he hs' hs hθ hF hv hmin
  have ht := spinPriorFrozenDiagonal_observableAverage hN μ π eig c I degree amplitude n b r h hh h0 v t a w
    (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1 - center|)
  rw [← ht]
  simpa only [sqrt_dimension_mul hN L,center,A,diagonalContactRate,mul_assoc] using hE.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorGGMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit vanishing GG rate at a constrained-prior coordinate minimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorGaussianGG_at_minimum {N m n q : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (amplitude : Fin N → ℝ) (r : Fin N → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin N) (w L : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/8) (hs : contactStep N≤1/4)
    (hamp : amplitude j=perturbationAmplitude N j*w)
    (hF : ∀ z : ℝ, |z|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*z))
        r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ z : ℝ, |z|≤2 →
      variance (spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*z))
        r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L)
    (hmin :
      let M := fun z => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π eig c I degree
        (Function.update amplitude j (perturbationAmplitude N j*z))
        r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ z∈Set.Icc (1 : ℝ) 2,
        -M w+perturbationWeight j*(w-3/2)^2≤-M z+perturbationWeight j*(z-3/2)^2)
    (C : ℝ) (hC : 0≤C)
    (D : SpecialOrthogonal N → (Fin (q+1) → Spin N × LabeledLeaf n) → ℝ)
    (hD : Measurable (Function.uncurry D)) (hDb : ∀ U σ, |D U σ|≤C)
    (center δ : Fin m → ℝ)
    (hδ : ∀ a, spinPriorObservableAverage (n := n) μ π eig c I degree amplitude b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-center a|)≤δ a) :
    |spinPriorSpectralGGResidual μ π b eig c I degree amplitude r h j D|≤
      contactGGRate N j L C+2*C*∑ a, (degree j a : ℝ)*δ a := by
  let a := perturbationAmplitude N j
  let c₀ := N * perturbationWeight j / a ^ 2
  let θ := 1 / perturbationScale N
  let G := (2 * c₀ + θ ^ 2) / (2 * θ) + c₀ * (a * contactStep N) +
    4 * (2 * N * Real.sqrt (L / N)) / (a * contactStep N)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he' : 0 < perturbationScale N := Real.rpow_pos_of_pos hn _
  have hs' : 0 < contactStep N := Real.rpow_pos_of_pos hn _
  have hθ : 0 < θ := one_div_pos.mpr he'
  have ha : 0 < a := perturbationAmplitude_pos hN j
  have hc₀ : 0 < c₀ := div_pos (mul_pos hn (perturbationWeight_pos j)) (sq_pos_of_pos ha)
  have hG : 0 ≤ G := by dsimp only [G] <;> positivity
  have hE := spinPriorGaussian_energy_at_minimum hN μ π b eig c I degree amplitude r h hh h0 j
    w (contactStep N) θ (N * L) hw he hs' hs hθ hF hv hmin
  have hamp' : 0 < |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha]
    exact mul_pos ha (abs_pos.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)))
  have hEa :
      let A := spectralPerturbationCoefficients (fun ω : TensorFrozenData N n j => ω.1.1)
        I (degree j) n (r j)
      let ν := spinPriorFrozenReference π eig c I degree amplitude n r h j
      let E := fun p : TensorFrozenData N n j × (ℕ → ℝ) => ∫ x,
        |cylinderField (A p.1 x) p.2 - 2 * c₀ * (a * w - a * (3 / 2))|
        ∂(ν p.1).tilted (fun x => amplitude j * cylinderField (A p.1 x) p.2)
      Integrable E ((tensorFrozenLaw μ n b j).prod gaussianCoordinates) ∧
        (∫ p, E p ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates) ≤ G := by
    simpa only [hamp, spectralPerturbationCoefficients, a, c₀, G, sqrt_dimension_mul hN L, mul_assoc] using hE
  have hgg := spinPriorFiniteGG_individualDiagonal_bound μ π b eig c I degree amplitude r h hh h0 j
    (2 * c₀ * (a * w - a * (3 / 2))) G C hC hamp' D hD hDb center δ hδ hEa
  have hampl : a ≤ |amplitude j| := by
    rw [hamp, abs_mul, abs_of_pos ha, abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw.1)]
    nlinarith [hw.1]
  calc
    _ ≤ 2 * C * (G / |amplitude j| + ∑ a, (degree j a : ℝ) * δ a) := hgg
    _ ≤ 2 * C * (G / a + ∑ a, (degree j a : ℝ) * δ a) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_left hG ha hampl) le_rfl) (mul_nonneg (by norm_num) hC)
    _ = _ := by unfold contactGGRate; dsimp only [G, c₀, θ, a] <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorMinimumCoordinates
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A joint constrained-prior minimum gives the two actual coordinate minima. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma spinPriorPerturbationPressureMean_eq_namespaced {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ) :
    spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h u v =
      (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I
        (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N u)
        (fun j => enumeratedTreeDegree m j) h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates := by
  unfold spinPriorPerturbationPressureMean spinPriorMeanPressure
  ring

private lemma penalty_update_p2 {z : ℕ} (u w : Fin z → ℝ) (j : Fin z) (s : ℝ) :
    (∑ i, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      (∑ i, w i * (u i - 3 / 2) ^ 2) - w j * (u j - 3 / 2) ^ 2 + w j * (s - 3 / 2) ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have he : (∑ i ∈ Finset.univ.erase j, w i * (Function.update u j s i - 3 / 2) ^ 2) =
      ∑ i ∈ Finset.univ.erase j, w i * (u i - 3 / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he, Function.update_self]
  ring

private lemma update_mem_Icc_p2 {z : ℕ} (u : Fin z → ℝ) (hu : ∀ i, u i ∈ Set.Icc (1 : ℝ) 2)
    (j : Fin z) (s : ℝ) (hs : s ∈ Set.Icc (1 : ℝ) 2) :
    ∀ i, Function.update u j s i ∈ Set.Icc (1 : ℝ) 2 := by
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [Function.update_self] using hs
  · simpa only [Function.update_of_ne hi] using hu i

theorem spinPriorPerturbation_minimum_coordinates {N m n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) (π : Measure (Spin N)) (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (t : ℝ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (v : Fin m → ℝ)
    (hu : ∀ j, u j∈Set.Icc (1 : ℝ) 2) (hv : ∀ a, v a∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') :
    let M := spinPriorPerturbationPressureMean (n := n) μ π eig c I b t h
    (∀ (j : Fin N) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+perturbationWeight j*(u j-3/2)^2≤
        -M (Function.update u j s) v+perturbationWeight j*(s-3/2)^2) ∧
    (∀ (a : Fin m) (s : ℝ), s∈Set.Icc (1 : ℝ) 2 →
      -M u v+(v a-3/2)^2≤-M u (Function.update v a s)+(s-3/2)^2) := by
  intro M
  constructor
  · intro j s hs
    have hc := hmin (Function.update u j s) v (update_mem_Icc_p2 u hu j s hs) hv
    unfold spinPriorPerturbationObjective at hc
    rw [penalty_update_p2] at hc
    linarith
  · intro a s hs
    have hc := hmin u (Function.update v a s) hu (update_mem_Icc_p2 v hv a s hs)
    unfold spinPriorPerturbationObjective at hc
    have he := penalty_update_p2 v (fun _ => 1) a s
    simp only [one_mul] at he
    rw [he] at hc
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorPerturbationVariance
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform concentration of the actual finite perturbation for a deterministic
spin constraint, with the cascade retained as quenched disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorPerturbation_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, |u j|≤2) →
    ∀ v : Fin m → ℝ, (∀ a, |v a|≤2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let F := spinPriorProfileLog π (diagonalPerturbedEigenvalues eig I v t) c I d
        (tensorPerturbationAmplitude N u) (fun i => tensorPathProfile I d n r h i)
      MemLp F 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
        variance F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤
          N*(4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
            ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2) := by
  obtain ⟨C,hC,hvar⟩ := spinPriorProfileLog_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH d r F
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  have hNp : 0<N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast hNp
  let a := tensorPerturbationAmplitude N u
  let L := (K+4*m)*N + 2*(∑ i : Fin (n+1), ∑ j : Fin N,
    (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2*∑ b, (d j b : ℝ))
  have hp := hvar N hN μ hμ hμinv π hπ m N n
    (diagonalPerturbedEigenvalues eig I v t) c (K+4*m) (by positivity)
    (diagonalPerturbedEigenvalues_abs_le hNp eig I v hv t ht K heig) I d a b hb
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
  let T := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))
  have hT : 0 ≤ T := mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)
  have hroot : (varianceIncrement h 0 : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) 0 : ℝ)*a j^2 ≤ (H+4)*N := by
    apply le_trans ?_ hG
    exact Finset.single_le_sum
      (f := fun i : Fin (n+1) => (varianceIncrement h i : ℝ)*N+
        ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) i : ℝ)*a j^2)
      (fun i _ => add_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity))
      (Finset.mem_univ (0 : Fin (n+1)))
  have hroot' : T+(varianceIncrement h 0 : ℝ)*N+
      ∑ j : Fin N, (varianceIncrement (monomialPath n (r j)) 0 : ℝ)*a j^2 ≤ T+(H+4)*N := by
    linarith
  have hvar' := hp.2.trans (add_le_add hroot' 
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq hC.le) hNr.le))
  refine ⟨hp.1, ?_⟩
  have he : C*(N*(K+4*m+8))^2/N = N*(C*(K+4*m+8)^2) := by
    field_simp [hNr.ne']
  rw [he] at hvar'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hTN : T ≤ N*T := by nlinarith
  change variance F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤
    T+(H+4)*N+N*(C*(K+4*m+8)^2) at hvar'
  change variance F _ ≤ N*(T+H+4+C*(K+4*m+8)^2)
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorMinimumBounds
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual constrained-prior minima satisfy both uniform perturbation bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorPerturbation_minimum_bounds (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
      perturbationScale N≤1/32 → contactStep N≤1/4 →
      (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') →
      (∀ a, spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I v t)
        c I d (tensorPerturbationAmplitude N u) b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-diagonalMinimumCenter N (v a)|)
          ≤diagonalContactRate N L) ∧
      (∀ j : Fin N, ∀ q : ℕ, ∀ B : ℝ, 0≤B →
        ∀ D : SpecialOrthogonal N → (Fin (q+1) → Spin N × LabeledLeaf n) → ℝ,
        Measurable (Function.uncurry D) → (∀ U σ, |D U σ|≤B) →
        |spinPriorSpectralGGResidual μ π b (diagonalPerturbedEigenvalues eig I v t)
          c I d (tensorPerturbationAmplitude N u) r h j D|≤
          contactGGRate N j L B+2*B*(∑ a, (d j a : ℝ))*diagonalContactRate N L) := by
  obtain ⟨C,hC,hvar⟩ := spinPriorPerturbation_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH d r L he hs hmin
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  have hNp : 0<N := by omega
  have hua : ∀ j, |u j|≤2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1],(hu j).2⟩
  have hva : ∀ a, |v a|≤2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1],(hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  have hcoords := spinPriorPerturbation_minimum_coordinates (n := n) μ π b eig c I t h u v hu hv hmin
  have hgv (a : Fin m) (w : ℝ) (hw : |w|≤2) :
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I d amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I d amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L := by
    exact hvar N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hua
      (Function.update v a w) (update_abs_le_two hva a hw) t ht h hh h0 H hH
  have hdiag (a : Fin m) : spinPriorObservableAverage (n := n) μ π
      (diagonalPerturbedEigenvalues eig I v t) c I d amplitude b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-diagonalMinimumCenter N (v a)|)
        ≤diagonalContactRate N L := by
    have hd := spinPriorDiagonal_fluctuation_at_minimum hNp μ π b eig c I d amplitude r h hh h0
      v t a (v a) L (hv a) he hs (fun w hw => (hgv a w hw).1) (fun w hw => (hgv a w hw).2) (by
        dsimp only
        intro w hw
        simpa only [spinPriorPerturbationPressureMean_eq_namespaced,Function.update_eq_self]
          using hcoords.2 a w hw)
    simpa only [Function.update_eq_self,diagonalMinimumCenter] using hd
  refine ⟨hdiag,?_⟩
  intro j q B hB D hD hDb
  have hgu (w : ℝ) (hw : |w|≤2) :
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I d
        (Function.update amplitude j (perturbationAmplitude N j*w))
        r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I d
        (Function.update amplitude j (perturbationAmplitude N j*w))
        r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L := by
    have hx := hvar N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I (Function.update u j w)
      (update_abs_le_two hua j hw) v hva t ht h hh h0 H hH
    change MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
      c I d (tensorPerturbationAmplitude N (Function.update u j w)) r h) 2
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
        c I d (tensorPerturbationAmplitude N (Function.update u j w)) r h)
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤ N*L at hx
    simpa only [tensorPerturbationAmplitude_update] using hx

  have hgm :
      let M := fun w => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
        c I d (Function.update amplitude j (perturbationAmplitude N j*w))
        r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ w∈Set.Icc (1 : ℝ) 2,
        -M (u j)+perturbationWeight j*(u j-3/2)^2≤-M w+perturbationWeight j*(w-3/2)^2 := by
    dsimp only
    intro w hw
    simpa only [amplitude,spinPriorPerturbationPressureMean_eq_namespaced,← tensorPerturbationAmplitude_update,
      Function.update_eq_self] using hcoords.1 j w hw
  have hg := spinPriorGaussianGG_at_minimum hNp μ π b (diagonalPerturbedEigenvalues eig I v t)
    c I d amplitude r h hh h0 j (u j) L (hu j) (by linarith) hs rfl
    (fun w hw => (hgu w hw).1) (fun w hw => (hgu w hw).2) hgm B hB D hD hDb
    (fun a => diagonalMinimumCenter N (v a)) (fun _ => diagonalContactRate N L) hdiag
  simpa only [← Finset.sum_mul,mul_assoc] using hg

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_SpinPriorArrayResidualBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform GG residual bounds for the actual constrained-prior array. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorPerturbation_arrayResidual_bound_oai (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), ∀ [IsProbabilityMeasure μ], μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), ∀ [IsProbabilityMeasure π],
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
      perturbationScale N≤1/32 → contactStep N≤1/4 →
      (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') →
      ∀ j : Fin N, ∀ q : ℕ, ∀ i : Fin (q+1),
      ∀ D : SpectralBlock (m+1) (q+1) → ℝ, Continuous D →
      ∀ B : ℝ, 0≤B → (∀ x, |D x|≤B) →
      |spectralMonomialResidual
        (spinPriorArrayLaw μ π (diagonalPerturbedEigenvalues eig I v t) c I d
          (tensorPerturbationAmplitude N u) n b r h)
        (q+1) i D (Fin.lastCases (r j) (d j))|≤tensorContactGGRate N j m L B := by
  obtain ⟨C,hC,hgg⟩ := spinPriorPerturbation_minimum_bounds hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH d r L
    he hs hmin j q i D hD B hB hDb
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  let e := Equiv.swap 0 i
  have hg := (hgg N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH
    he hs hmin).2 j q B hB (permutedSpectralBlockTest I n e D)
    (measurable_permutedSpectralBlockTest I n e D hD) (fun U σ => hDb _)
  have hr := spinPriorArrayLaw_residual (n := n) μ π b (diagonalPerturbedEigenvalues eig I v t) c I d
    (tensorPerturbationAmplitude N u) r h j e D hD
  have hei : e 0=i := Equiv.swap_apply_left 0 i
  rw [hei] at hr
  rw [hr]
  exact hg

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound_oai := @OAI.InvariantIsing.spinPriorPerturbation_arrayResidual_bound_oai
