-- Prove2me | solution 1 for OAI.InvariantIsing.tensorContact_limit_tail_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:11:26.051355+00:00
-- url     : https://prove2.me/submissions/a1a11c78-cd5e-4e23-9bef-c13112859c21

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_tensorContact_minimum_field_cone
import Theorems.Thm_OAI_InvariantIsing_tensorFlat_leafPrefix_mean

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
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron



lemma polya_no_linear_cap {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : b < 1)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (h0 : 0 < r 0)
    (hrec : ∀ k, r (k+1) = r k * ((n : ℝ) + k - b) / ((n : ℝ) + k))
    (hcap : ∀ k : ℕ, (k+1 : ℝ) * r k ≤ 1) : False := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let t : ℕ → ℝ := fun k => ((n : ℝ) + k - 1) * r k
  have ht : ∀ k, t (k+1) = t k + (1-b) * r k := by
    intro k
    have hnk : (n : ℝ) + k ≠ 0 := by positivity
    dsimp [t]
    rw [hrec]
    push_cast
    field_simp
    ring
  have hbase : 0 < t 0 := by
    dsimp [t]; simp only [Nat.cast_zero, add_zero]
    exact mul_pos (by linarith) h0
  have hmono : Monotone t := monotone_nat_of_le_succ (fun k => by
    rw [ht]
    nlinarith [hr k])
  have hlower : ∀ k, t 0 / ((n : ℝ) + k - 1) ≤ r k := by
    intro k
    have h := hmono (Nat.zero_le k)
    have hden : 0 < (n : ℝ) + k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact (div_le_iff₀ hden).mpr (by simpa only [t, mul_comm] using h)
  have hsum : ∀ k, t 0 + (1-b)*t 0 *
      (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1)) ≤ t k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ht]
      have he := mul_le_mul_of_nonneg_left (hlower k) (sub_pos.mpr hb).le
      calc
        _ = (t 0 + (1-b)*t 0 * (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1))) +
              (1-b)*(t 0 / ((n : ℝ) + k - 1)) := by ring
        _ ≤ _ := add_le_add ih he
  have hupper : ∀ k, t k ≤ (n : ℝ) - 1 := by
    intro k
    have h := hcap k
    have he : (n : ℝ) + k - 1 ≤ ((n : ℝ)-1) * (k+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have he' := mul_le_mul_of_nonneg_right he (hr k)
    have h' := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ (n : ℝ)-1)
    dsimp [t]
    nlinarith
  have hcompare : ∀ k, (∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n ≤
      ∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1) := by
    intro k
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hden : 0 < (n : ℝ) + j - 1 := by linarith
    rw [div_div]
    apply one_div_le_one_div_of_le hden
    nlinarith
  have hH : Tendsto (fun k => t 0 + (1-b)*t 0 *
      ((∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop (by positivity)
    exact Filter.Tendsto.atTop_div_const (by positivity)
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨k, hk⟩ := ((tendsto_atTop.1 hH) ((n : ℝ) - 1 + 1)).exists
  have he := (mul_le_mul_of_nonneg_left (hcompare k) (by positivity : 0 ≤ (1-b)*t 0))
  have hs := hsum k
  have hu := hupper k
  linarith

 

lemma equal_probability_aedisjoint_cap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {s : Fin (k+1) → Set Ω}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => AEDisjoint μ (s i) (s j)))
    {r : ℝ} (hs : ∀ i, μ.real (s i) = r) : (k+1 : ℝ)*r ≤ 1 := by
  have he := measureReal_biUnion_finset₀ (μ := μ) (s := Finset.univ)
    (fun i _ j _ hij => hd hij) (fun i _ => (hm i).nullMeasurableSet)
    (fun i _ => measure_ne_top μ (s i))
  have hu : (⋃ i ∈ Finset.univ, s i) = ⋃ i, s i := by simp
  rw [hu] at he
  have hh : μ.real (⋃ i, s i) ≤ 1 := measureReal_le_one
  rw [he] at hh
  simpa [hs, Nat.cast_add, Nat.cast_one] using hh

lemma swap_hasFiniteSupport (i j : ℕ) : {a | (Equiv.swap i j) a ≠ a}.Finite := by
  apply ((Set.finite_singleton j).insert i).subset
  intro a ha
  by_contra hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
  exact ha (Equiv.swap_apply_of_ne_of_ne hn.1 hn.2)

lemma measurableSet_starSet {a : ℕ} (J : Finset ℕ) {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i : ℕ) : MeasurableSet (starSet a J A T t i) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  change MeasurableSet {b : RealArray | ∀ j ∈ J, j ≠ i → b i j < t}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt
      (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const

lemma measurableSet_duplicateSet {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i j : ℕ) : MeasurableSet (duplicateSet a A T t i j) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  exact (hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply j).comp (measurable_pi_apply (x : ℕ)))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const)

lemma starSet_permute {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) (hJ : ∀ j, j ∈ J ↔ e j ∈ J) :
    permuteArray e ⁻¹' starSet a J A T t i = starSet a J A T t (e i) := by
  ext b
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    funext x
    simp only [permuteArray, hfix x x.isLt]
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hji
    have hj' : e.symm j ∈ J := (hJ _).mpr (by simpa using hj)
    have hji' : e.symm j ≠ i := by intro he; apply hji; rw [← he]; simp
    simpa only [permuteArray, Equiv.apply_symm_apply] using hs _ hj' hji'
  · rintro ⟨ha, ht, hs⟩
    exact ⟨ha, ht, fun j hj hji => hs (e j) ((hJ j).mp hj) (e.injective.ne hji)⟩

lemma duplicateSet_permute {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i j : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) :
    permuteArray e ⁻¹' duplicateSet a A T t i j = duplicateSet a A T t (e i) (e j) := by
  ext b
  change (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _)
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : ∀ i, (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    intro i; funext x
    simp only [permuteArray, hfix x x.isLt]
  rw [hA, hT i, hT j]
  rfl

lemma swap_preserves_ge {a x y z : ℕ} (hx : a ≤ x) (hy : a ≤ y) (hz : a ≤ z) :
    a ≤ (Equiv.swap x y) z := by
  by_cases hzx : z = x
  · subst z; simpa using hy
  by_cases hzy : z = y
  · subst z; simpa using hx
  simpa only [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

lemma star_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    {t : ℝ} {i j : ℕ} (hai : a ≤ i) (haj : a ≤ j) (hi : i ∈ J) (hj : j ∈ J) :
    μ (B ⁻¹' starSet a J A T t i) = μ (B ⁻¹' starSet a J A T t j) := by
  have h := (hwe (Equiv.swap i j) (swap_hasFiniteSupport i j)).measure_mem_eq
    (measurableSet_starSet J hA hT t i)
  change μ (B ⁻¹' starSet a J A T t i) =
    μ (B ⁻¹' (permuteArray (Equiv.swap i j) ⁻¹' starSet a J A T t i)) at h
  have hfix : ∀ x < a, (Equiv.swap i j) x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hJ : ∀ x, x ∈ J ↔ (Equiv.swap i j) x ∈ J := by
    intro x
    by_cases hxi : x = i
    · subst x; simp only [Equiv.swap_apply_left]; exact iff_of_true hi hj
    by_cases hxj : x = j
    · subst x; simp only [Equiv.swap_apply_right]; exact iff_of_true hj hi
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [starSet_permute hfix hJ, Equiv.swap_apply_left] at h
  exact h

lemma duplicate_probability_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ) (i j : ℕ)
    {x y : ℕ} (hx : a ≤ x) (hy : a ≤ y) :
    μ (B ⁻¹' duplicateSet a A T t i j) =
      μ (B ⁻¹' duplicateSet a A T t ((Equiv.swap x y) i) ((Equiv.swap x y) j)) := by
  have h := (hwe (Equiv.swap x y) (swap_hasFiniteSupport x y)).measure_mem_eq
    (measurableSet_duplicateSet hA hT t i j)
  change μ (B ⁻¹' duplicateSet a A T t i j) =
    μ (B ⁻¹' (permuteArray (Equiv.swap x y) ⁻¹' duplicateSet a A T t i j)) at h
  rwa [duplicateSet_permute (by
    intro z hz
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))] at h

lemma duplicate_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    {i j : ℕ} (hi : a ≤ i) (hj : a ≤ j) (hij : i ≠ j) :
    μ (B ⁻¹' duplicateSet a A T t a (a+1)) = μ (B ⁻¹' duplicateSet a A T t i j) := by
  let k := (Equiv.swap a i) (a+1)
  have hk : a ≤ k := swap_preserves_ge (le_refl a) hi (by omega)
  have hki : k ≠ i := by
    have hh : (Equiv.swap a i) (a+1) ≠ (Equiv.swap a i) a :=
      (Equiv.swap a i).injective.ne (by omega)
    simpa only [Equiv.swap_apply_left] using hh
  have h₁ := duplicate_probability_swap hwe hA hT t a (a+1) (le_refl a) hi
  have h₂ := duplicate_probability_swap hwe hA hT t i k hk hj
  rw [Equiv.swap_apply_of_ne_of_ne hki.symm hij, Equiv.swap_apply_left] at h₂
  rw [Equiv.swap_apply_left] at h₁
  exact h₁.trans h₂

lemma no_duplicate_star_cap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hdup : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0) (k : ℕ) :
    (k+1 : ℝ) * μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) ≤ 1 := by
  let J := Finset.Ico a (a+k+1)
  let s : Fin (k+1) → Set Ω := fun i => B ⁻¹' starSet a J A T t (a+i)
  have hmem : ∀ i : Fin (k+1), a+i ∈ J := by
    intro i
    simp only [J, Finset.mem_Ico]
    constructor <;> omega
  apply equal_probability_aedisjoint_cap (μ := μ) (s := s)
  · intro i
    exact (measurableSet_starSet J hA hT t (a+i)).preimage hm
  · intro i j hij
    have hnull : μ (B ⁻¹' duplicateSet a A T t (a+i) (a+j)) = 0 := by
      rw [← duplicate_probability_equal hwe hA hT t (by omega) (by omega)
        (by intro h; apply hij; apply Fin.ext; omega), hdup]
    change μ (s i ∩ s j) = 0
    apply measure_mono_null (t := B ⁻¹' duplicateSet a A T t (a+i) (a+j)) ?_ hnull
    intro ω hω
    exact ⟨hω.1.1, hω.1.2.1, hω.2.2.1,
      hω.1.2.2 (a+j) (hmem j) (by intro h; apply hij; apply Fin.ext; omega)⟩
  · intro i
    apply congrArg ENNReal.toReal
    exact star_probability_equal hwe hA hT (by omega) (le_refl a) (hmem i)
      (by simp only [J, Finset.mem_Ico]; constructor <;> omega)


lemma measurable_extendArrayBlock (n : ℕ) : Measurable (extendArrayBlock n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hi : i < n
  · by_cases hj : j < n
    · simpa only [extendArrayBlock, dite_eq_left hi, dite_eq_left hj, Function.comp_def] using
        ((measurable_pi_apply (⟨j,hj⟩ : Fin n)).comp (measurable_pi_apply (⟨i,hi⟩ : Fin n)))
    · simp only [extendArrayBlock, dite_eq_left hi, dite_eq_right hj]; exact measurable_const
  · simp only [extendArrayBlock, dite_eq_right hi]; exact measurable_const

lemma starSet_dependsOn {Ω : Type*} {B : Ω → RealArray} {ω : Ω}
    {n a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    {t : ℝ} {i : ℕ} (han : a ≤ n) (hin : i < n) (hJ : ∀ j ∈ J, j < n) :
    extendArrayBlock n (arrayBlock B n ω) ∈ starSet a J A T t i ↔
      B ω ∈ starSet a J A T t i := by
  have he : ∀ x y, x < n → y < n →
      extendArrayBlock n (arrayBlock B n ω) x y = B ω x y := by
    intro x y hx hy
    simp only [extendArrayBlock, dite_eq_left hx, dite_eq_left hy, arrayBlock]
  have hA : (fun x y : Fin a => extendArrayBlock n (arrayBlock B n ω) x y) =
      fun x y : Fin a => B ω x y := by
    funext x y
    exact he x y (x.isLt.trans_le han) (y.isLt.trans_le han)
  have hT : (fun x : Fin a => extendArrayBlock n (arrayBlock B n ω) x i) =
      fun x : Fin a => B ω x i := by
    funext x
    exact he x i (x.isLt.trans_le han) hin
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro j
  apply forall_congr'; intro hj
  rw [he i j hin (hJ j hj)]

lemma starSet_chain_succ {a k : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} :
    starSet a (Finset.Ico a (a+(k+1)+1)) A T t a =
      starSet a (Finset.Ico a (a+k+1)) A T t a ∩ {b | b a (a+k+1) < t} := by
  ext b
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨⟨ha, ht, fun j hj hja => hs j ?_ hja⟩, hs (a+k+1) ?_ (by omega)⟩
    · simp only [Finset.mem_Ico] at hj ⊢; omega
    · simp only [Finset.mem_Ico]; omega
  · rintro ⟨⟨ha, ht, hs⟩, hn⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hja
    by_cases hjn : j = a+k+1
    · change b a (a+k+1) < t at hn
      simpa only [hjn] using hn
    · apply hs j _ hja
      simp only [Finset.mem_Ico] at hj ⊢; omega

lemma gg_star_chain_recurrence {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t) (k : ℕ) :
    μ.real (B ⁻¹' starSet a (Finset.Ico a (a+(k+1)+1)) A T t a) =
      μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) *
        ((a+1 : ℕ) + (k : ℝ) - (1 - μ.real {ω | B ω 0 1 < t})) /
        ((a+1 : ℕ) + (k : ℝ)) := by
  classical
  let n := a+k+1
  let J := Finset.Ico a n
  let C : Set Ω := B ⁻¹' starSet a J A T t a
  let F : Set (Fin n → Fin n → ℝ) := extendArrayBlock n ⁻¹' starSet a J A T t a
  let i : Fin n := ⟨a, by dsimp [n]; omega⟩
  have hF : MeasurableSet F :=
    (measurableSet_starSet J hA hT t a).preimage (measurable_extendArrayBlock n)
  have hC : arrayBlock B n ⁻¹' F = C := by
    ext ω
    exact starSet_dependsOn (by dsimp [n]; omega) (by dsimp [n]; omega)
      (by intro j hj; exact (Finset.mem_Ico.mp hj).2)
  have h := hGG n (by dsimp [n]; omega) i F hF (Set.Iio t) measurableSet_Iio
  rw [hC] at h
  have hevent : ∀ j ∈ Finset.univ.erase i,
      C ∩ {ω | B ω i j ∈ Set.Iio t} = C := by
    intro j hj
    apply Set.inter_eq_left.mpr
    intro ω hω
    have hji : j.val ≠ a := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    change B ω a j.val < t
    by_cases hja : j.val < a
    · rw [hsym ω a j.val]
      exact hTlow _ hω.2.1 ⟨j.val,hja⟩
    · exact hω.2.2 j.val (Finset.mem_Ico.mpr ⟨by omega, j.isLt⟩) hji
  have hsum : (∑ j ∈ Finset.univ.erase i, μ.real (C ∩ {ω | B ω i j ∈ Set.Iio t})) =
      (n-1 : ℝ) * μ.real C := by
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, μ.real C :=
        Finset.sum_congr rfl (fun j hj => congrArg μ.real (hevent j hj))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub (by dsimp [n]; omega : 1 ≤ n), Nat.cast_one]
  rw [hsum] at h
  rw [starSet_chain_succ, Set.preimage_inter]
  change μ.real (C ∩ {ω | B ω a n < t}) = _
  change μ.real (C ∩ {ω | B ω a n < t}) = _ at h
  rw [h]
  dsimp [C, J, n]
  simp only [Set.mem_Iio]
  push_cast
  ring

lemma low_pair_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} (ha : 0 < a) (t : ℝ) :
    μ {ω | B ω 0 1 < t} = μ {ω | B ω 0 a < t} := by
  have h := (hwe (Equiv.swap 1 a) (swap_hasFiniteSupport 1 a)).measure_mem_eq
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b 0 1))
      (measurable_const (a := t)))
  have hz : (Equiv.swap 1 a) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  simpa only [Set.preimage_ofPred_eq, permuteArray, hz, Equiv.swap_apply_left] using h

lemma starSet_base (a : ℕ) (A : Set (Fin a → Fin a → ℝ)) (T : Set (Fin a → ℝ)) (t : ℝ) :
    starSet a (Finset.Ico a (a+1)) A T t a =
      {b | (fun x y : Fin a => b x y) ∈ A ∧ (fun x : Fin a => b x a) ∈ T} := by
  ext b
  constructor
  · intro h; exact ⟨h.1, h.2.1⟩
  · rintro ⟨hA, hT⟩
    refine ⟨hA, hT, ?_⟩
    intro j hj hjne
    simp only [Finset.mem_Ico] at hj
    omega

 

theorem gg_duplication_positive {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t)
    (hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) A T t a)) :
    0 < μ.real (B ⁻¹' duplicateSet a A T t a (a+1)) := by
  by_contra hn
  have hzero : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0 := by
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    exact le_antisymm (not_lt.mp hn) measureReal_nonneg
  have hp : 0 < μ.real {ω | B ω 0 1 < t} := by
    have he := congrArg ENNReal.toReal (low_pair_probability_equal hwe ha t)
    change μ.real {ω | B ω 0 1 < t} = μ.real {ω | B ω 0 a < t} at he
    rw [he]
    exact hpos.trans_le (measureReal_mono (μ := μ) (fun ω hω => hTlow _ hω.2.1 ⟨0,ha⟩))
  apply polya_no_linear_cap (n := a+1) (b := 1 - μ.real {ω | B ω 0 1 < t})
    (r := fun k => μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a))
    (by omega) (by linarith) (fun _ => measureReal_nonneg)
    (by simpa only [Nat.add_zero] using hpos)
  · exact gg_star_chain_recurrence hsym hGG ha hA hT t hTlow
  · exact no_duplicate_star_cap hm hwe hA hT t hzero


lemma measurable_arrayBlock {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} (hm : Measurable B) (n : ℕ) :
    Measurable (arrayBlock B n) := by
  unfold arrayBlock
  fun_prop

lemma blockLaw_support_compact {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hb : ∀ ω i j, |B ω i j| ≤ D) (n : ℕ) :
    IsCompact (blockLaw B μ n).support := by
  apply (isCompact_Icc (a := fun _ _ : Fin n => -D)
    (b := fun _ _ : Fin n => D)).of_isClosed_subset Measure.isClosed_support
  apply Measure.support_subset_of_isClosed isClosed_Icc
  rw [mem_ae_iff]
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) isClosed_Icc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' (Set.Icc (fun _ _ : Fin n => -D) (fun _ _ : Fin n => D))ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hω
    constructor
    · intro i j; exact (abs_le.mp (hb ω i j)).1
    · intro i j; exact (abs_le.mp (hb ω i j)).2
  rw [he, measure_empty]

 

theorem gg_duplicate_supported_last {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) {t : ℝ}
    (ht : ∀ i : Fin a, A i.castSucc (Fin.last a) ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, C i.castSucc.castSucc j.castSucc.castSucc = A i.castSucc j.castSucc) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last a).castSucc = A i.castSucc (Fin.last a)) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last (a+1)) = A i.castSucc (Fin.last a)) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) ≤ t := by
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, |C i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) < t+ε := by
    intro ε hε
    let F : Set (Fin a → Fin a → ℝ) :=
      {c | ∀ i j, |c i j - A i.castSucc j.castSucc| < ε}
    let T : Set (Fin a → ℝ) :=
      {c | ∀ i, |c i - A i.castSucc (Fin.last a)| < ε}
    have hF : MeasurableSet F := by
      dsimp [F]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
    have hT : MeasurableSet T := by
      dsimp [T]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
    have hball := (Measure.mem_support_iff_forall A).mp hA
      (Metric.ball A ε) (Metric.ball_mem_nhds A hε)
    rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+1)) Metric.isOpen_ball.measurableSet] at hball
    have hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a) := by
      have hsub : arrayBlock B (a+1) ⁻¹' Metric.ball A ε ⊆
          B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a := by
        intro ω hω
        rw [starSet_base]
        have hc := (dist_pi_lt_iff hε).mp hω
        constructor
        · intro i j
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) j.castSucc
        · intro i
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) (Fin.last a)
      exact ENNReal.toReal_pos (ne_of_gt (hball.trans_le (measure_mono hsub))) (measure_ne_top _ _)
    have hd := gg_duplication_positive hm hsym hwe hGG ha hF hT (t+ε)
      (by intro v hv i; have hi := (abs_lt.mp (hv i)).2; have := ht i; linarith) hpos
    let E : Set (Fin (a+2) → Fin (a+2) → ℝ) := {c |
      (∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε}
    have hE : MeasurableSet E := by
      change MeasurableSet ({c : Fin (a+2) → Fin (a+2) → ℝ | ∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε} ∩
        {c | c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε})))
      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · exact measurableSet_lt (by fun_prop) measurable_const
    have hEp : 0 < (blockLaw B μ (a+2)) E := by
      rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+2)) hE]
      exact ENNReal.toReal_pos_iff.mp hd |>.1
    obtain ⟨C, hCE, hCs⟩ := Measure.nonempty_inter_support_of_pos hEp
    exact ⟨C, hCs, hCE⟩
  choose C hCs hC using fun k : ℕ => happrox (1 / (k+1)) (by positivity)
  obtain ⟨L, hLs, φ, hφ, hlim⟩ := (blockLaw_support_compact hm hb (a+2)).tendsto_subseq hCs
  have hzero : Tendsto (fun k => 1 / ((φ k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hentry : ∀ i j, Tendsto (fun k => C (φ k) i j) atTop (𝓝 (L i j)) := by
    intro i j
    exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp hlim
  have heq : ∀ (i j : Fin (a+2)) (v : ℝ),
      (∀ k, |C k i j-v| < 1/((k:ℝ)+1)) → L i j = v := by
    intro i j v hv
    have hl := ((hentry i j).sub (tendsto_const_nhds (x := v))).abs
    have hg : |L i j-v| ≤ 0 := le_of_tendsto_of_tendsto hl hzero
      (Filter.Eventually.of_forall fun k => (hv (φ k)).le)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hg (abs_nonneg _)))
  refine ⟨L, hLs, ?_, ?_, ?_, ?_⟩
  · intro i j; exact heq _ _ _ (fun k => (hC k).1 i j)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.1 i)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.2.1 i)
  · have htlim := tendsto_const_nhds.add hzero (a := t)
    simp only [add_zero] at htlim
    exact le_of_tendsto_of_tendsto (hentry _ _) htlim
      (Filter.Eventually.of_forall fun k => (hC (φ k)).2.2.2.le)

lemma support_mem_of_continuous_invariant {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : Continuous f) (hi : ∀ s, MeasurableSet s → μ (f ⁻¹' s) = μ s)
    {x : X} (hx : x ∈ μ.support) : f x ∈ μ.support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  have hp := (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV))
  rw [hi V hVo.measurableSet] at hp
  exact hp.trans_le (measure_mono hVU)

lemma blockLaw_support_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω}
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {n : ℕ} {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support)
    (i j : Fin n) :
    (fun x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)) ∈
      (blockLaw B μ n).support := by
  have hcoe : ∀ x : Fin n, ((Equiv.swap i j) x).val = (Equiv.swap i.val j.val) x.val := by
    intro x
    by_cases hxi : x = i
    · subst x; simp
    by_cases hxj : x = j
    · subst x; simp
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj,
      Equiv.swap_apply_of_ne_of_ne (fun h => hxi (Fin.ext h)) (fun h => hxj (Fin.ext h))]
  let f : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun A x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)
  have hf : Continuous f := by unfold f; fun_prop
  apply support_mem_of_continuous_invariant hf _ hA
  intro S hS
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) (hS.preimage hf.measurable),
    Measure.map_apply (measurable_arrayBlock hm n) hS]
  have h := (hwe (Equiv.swap i.val j.val) (swap_hasFiniteSupport i.val j.val)).measure_mem_eq
    (s := (fun b : RealArray => arrayBlock (fun _ : Unit => b) n ()) ⁻¹' S)
    (hS.preimage (by unfold arrayBlock; fun_prop))
  convert h.symm using 2 <;> first | (with_reducible_and_instances rfl) | (ext ω <;> simp only [Set.mem_preimage, arrayBlock, f, hcoe] <;> rfl)

lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma blockLaw_support_gram {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support) :
    Matrix.PosSemidef A ∧ ∀ i, A i i = D := by
  have hdclosed : IsClosed {A : Fin n → Fin n → ℝ | ∀ i, A i i = D} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D} :=
    (isClosed_setOf_posSemidef n).inter hdclosed
  apply Measure.support_subset_of_isClosed hc _ hA
  rw [mem_ae_iff, blockLaw, Measure.map_apply (measurable_arrayBlock hm n) hc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D}ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω ⟨hpsd ω n, fun i => hdiag ω i⟩
  rw [he, measure_empty]

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm

 
theorem gg_duplicate_supported {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) (p : Fin (a+1)) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin (a+1), C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin (a+1), i ≠ p → C i.castSucc (Fin.last (a+1)) = A i p) ∧
      C p.castSucc (Fin.last (a+1)) ≤ t := by
  let e := Equiv.swap p (Fin.last a)
  let A' : Fin (a+1) → Fin (a+1) → ℝ := fun i j => A (e i) (e j)
  have hA' : A' ∈ (blockLaw B μ (a+1)).support := blockLaw_support_swap hm hwe hA p (Fin.last a)
  have ht' : ∀ i : Fin a, A' i.castSucc (Fin.last a) ≤ t := by
    intro i
    simp only [A', e, Equiv.swap_apply_right]
    apply ht
    intro he
    have hh := congrArg e he
    simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_left] at hh
    exact Fin.castSucc_ne_last i hh
  obtain ⟨C, hCs, hC0, hC1, hC2, hC3⟩ :=
    gg_duplicate_supported_last hm hsym hwe hGG hb ha hA' ht'
  have hgramA := blockLaw_support_gram hm hpsd hdiag hA
  have hgramC := blockLaw_support_gram hm hpsd hdiag hCs
  have hfull : ∀ i j : Fin (a+1), C i.castSucc j.castSucc = A' i j := by
    intro i j
    refine Fin.lastCases ?_ (fun ii => ?_) i
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact (hgramC.2 _).trans (hgramA.2 _).symm
      · rw [real_posSemidef_symm hgramC.1, hC1]
        exact real_posSemidef_symm hgramA.1 _ _
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact hC1 ii
      · exact hC0 ii jj
  let e' := Equiv.swap p.castSucc (Fin.last a).castSucc
  have hecast : ∀ i : Fin (a+1), e' i.castSucc = (e i).castSucc := by
    intro i
    by_cases hi : i = p
    · subst i; simp [e', e]
    by_cases hil : i = Fin.last a
    · subst i; simp [e', e]
    rw [show e i = i from Equiv.swap_apply_of_ne_of_ne hi hil]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (Fin.castSucc_injective _ h))
      (fun h => hil (Fin.castSucc_injective _ h))
  have helast : e' (Fin.last (a+1)) = Fin.last (a+1) := by
    apply Equiv.swap_apply_of_ne_of_ne <;> exact (Fin.castSucc_ne_last _).symm
  refine ⟨fun i j => C (e' i) (e' j), blockLaw_support_swap hm hwe hCs _ _, ?_, ?_, ?_⟩
  · intro i j
    change C (e' i.castSucc) (e' j.castSucc) = _
    rw [hecast, hecast, hfull]
    simp only [A', e, Equiv.swap_apply_self]
  · intro i hip
    change C (e' i.castSucc) (e' (Fin.last (a+1))) = _
    rw [hecast, helast]
    have heil : e i ≠ Fin.last a := by
      intro he
      have he' := congrArg e he
      simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_right] at he'
      exact hip he'
    obtain ⟨ii, hii⟩ := Fin.eq_castSucc_of_ne_last heil
    rw [← hii, hC2]
    dsimp [A']
    have heii : e ii.castSucc = i := by rw [hii]; exact Equiv.swap_apply_self _ _ _
    rw [heii]
    simp [e]
  · change C (e' p.castSucc) (e' (Fin.last (a+1))) ≤ _
    rw [hecast, helast]
    simpa only [e, Equiv.swap_apply_left] using hC3

lemma psd_bilinear_symm {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  have hs : ∀ i j, B i j = B j i := by
    intro i j
    have h := congrFun (congrFun hB.1 i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j i]
  ring

lemma psd_cauchy_schwarz {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    (x ⬝ᵥ (B *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (B *ᵥ x)) * (y ⬝ᵥ (B *ᵥ y)) := by
  have hq : ∀ t : ℝ, 0 ≤ (x ⬝ᵥ (B *ᵥ x)) * (t * t) +
      (2 * (x ⬝ᵥ (B *ᵥ y))) * t + (y ⬝ᵥ (B *ᵥ y)) := by
    intro t
    have h := hB.dotProduct_mulVec_nonneg (t • x + y)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [psd_bilinear_symm hB y x] at h
    nlinarith
  have h := discrim_le_zero hq
  dsimp [discrim] at h
  nlinarith

lemma psd_three_gap {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosSemidef) :
    (B 0 2 - B 0 1) ^ 2 ≤ B 0 0 * (B 1 1 + B 2 2 - 2 * B 1 2) := by
  have hs : B 2 1 = B 1 2 := by
    have h := congrFun (congrFun hB.1 1) 2
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have h := psd_cauchy_schwarz hB ![1, 0, 0] ![0, -1, 1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs] at h
  nlinarith


lemma groupAverageMatrix_posSemidef {m : ℕ}
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} (hB : B.PosSemidef) :
    (groupAverageMatrix B).PosSemidef := by
  classical
  let C : Matrix (Fin 3 × Fin m) (Fin 3) ℝ := fun a i => if a.1 = i then (m : ℝ)⁻¹ else 0
  have h := hB.conjTranspose_mul_mul_same C
  have heq : C.conjTranspose * B * C = groupAverageMatrix B := by
    ext i j
    change (∑ a : Fin 3 × Fin m, (∑ b : Fin 3 × Fin m, C b i * B b a) * C a j) = _
    simp only [C, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_mul]
    dsimp [groupAverageMatrix]
    rw [Finset.sum_comm]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rwa [heq] at h

lemma groupAverageMatrix_cross {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i j : Fin 3} {q : ℝ}
    (h : ∀ a b, B (i,a) (j,b) = q) : groupAverageMatrix B i j = q := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [groupAverageMatrix, h, pow_two]
  field_simp

lemma groupAverageMatrix_diag_le {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i : Fin 3} {D q : ℝ}
    (hd : ∀ a, B (i,a) (i,a) = D)
    (ho : ∀ a b, a ≠ b → B (i,a) (i,b) ≤ q) :
    groupAverageMatrix B i i ≤ D / m + (1 - 1 / (m : ℝ)) * q := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : ∀ a, ∑ b : Fin m, B (i,a) (i,b) ≤ D + (m - 1 : ℝ) * q := by
    intro a
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), hd a]
    have h := Finset.sum_le_sum (s := Finset.univ.erase a)
      (f := fun b => B (i,a) (i,b)) (g := fun _ => q)
      (fun b hb => ho a b (Ne.symm (Finset.mem_erase.mp hb).1))
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hr a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  dsimp [groupAverageMatrix]
  apply (div_le_iff₀ (sq_pos_of_pos hm')).mpr
  calc
    _ ≤ m * (D + (m - 1 : ℝ) * q) := h
    _ = _ := by field_simp

lemma psd_entry_le_diagonal {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) {D : ℝ} (hd : ∀ i, B i i = D) (i j : ι) : B i j ≤ D := by
  classical
  have hD : 0 ≤ D := hd i ▸ hB.diag_nonneg
  have h := psd_cauchy_schwarz hB (Pi.single i 1) (Pi.single j 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at h
  nlinarith [sq_nonneg (B i j - D)]

lemma groupAverageMatrix_diag_le_common {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D : ℝ}
    (hB : B.PosSemidef) (hd : ∀ a, B a a = D) (i : Fin 3) :
    groupAverageMatrix B i i ≤ D := by
  have h := groupAverageMatrix_diag_le hm (fun a => hd (i,a))
    (fun a b _ => psd_entry_le_diagonal hB hd (i,a) (i,b))
  have hD : D / (m : ℝ) + (1 - 1 / (m : ℝ)) * D = D := by ring
  rwa [hD] at h

 
lemma duplicated_triple_gap_bound {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D a b c : ℝ}
    (hB : B.PosSemidef) (hd : ∀ i, B i i = D)
    (hab : ∀ i j, B (0,i) (1,j) = a)
    (hac : ∀ i j, B (0,i) (2,j) = b)
    (hbc : ∀ i j, B (1,i) (2,j) = c)
    (h22 : ∀ i j, i ≠ j → B (1,i) (1,j) ≤ c)
    (h33 : ∀ i j, i ≠ j → B (2,i) (2,j) ≤ c) :
    (b - a)^2 ≤ 2 * D * (D - c) / m := by
  have hG := groupAverageMatrix_posSemidef hB
  have h := psd_three_gap hG
  have h00 := groupAverageMatrix_diag_le_common hm hB hd 0
  have h11 := groupAverageMatrix_diag_le hm (fun i => hd (1,i)) h22
  have h22' := groupAverageMatrix_diag_le hm (fun i => hd (2,i)) h33
  have h01 := groupAverageMatrix_cross hm hab
  have h02 := groupAverageMatrix_cross hm hac
  have h12 := groupAverageMatrix_cross hm hbc
  rw [h01, h02, h12] at h
  have hD : 0 ≤ D := (hG.diag_nonneg (i := 0)).trans h00
  have hq : 0 ≤ groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2 * c := by
    have h0 := hG.dotProduct_mulVec_nonneg ![0, -1, 1]
    have hs : groupAverageMatrix B 2 1 = groupAverageMatrix B 1 2 := by
      have he := congrFun (congrFun hG.1 1) 2
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs, h12] at h0
    linarith
  calc
    (b - a)^2 ≤ groupAverageMatrix B 0 0 *
        (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) := h
    _ ≤ D * (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) :=
      mul_le_mul_of_nonneg_right h00 hq
    _ ≤ D * (2 * (D / m + (1 - 1 / (m : ℝ)) * c) - 2*c) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    _ = 2 * D * (D - c) / m := by ring

 

lemma no_arbitrary_nonultrametric_duplicates {D a b c : ℝ} (hab : a < b)
    (hex : ∀ m : ℕ, 0 < m → ∃ B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ,
      B.PosSemidef ∧ (∀ i, B i i = D) ∧
      (∀ i j, B (0,i) (1,j) = a) ∧ (∀ i j, B (0,i) (2,j) = b) ∧
      (∀ i j, B (1,i) (2,j) = c) ∧
      (∀ i j, i ≠ j → B (1,i) (1,j) ≤ c) ∧
      (∀ i j, i ≠ j → B (2,i) (2,j) ≤ c)) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * D * (D - c) / (b-a)^2)
  obtain ⟨B, hB, hd, h01, h02, h12, h11, h22⟩ := hex (m+1) (by omega)
  have h := duplicated_triple_gap_bound (by omega : 0 < m+1) hB hd h01 h02 h12 h11 h22
  have hp : 0 < (b-a)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hm' : (0 : ℝ) < (m+1 : ℕ) := by positivity
  have hbound := (div_lt_iff₀ hp).mp hm
  have hbig := (le_div_iff₀ hm').mp h
  simp only [Nat.cast_add, Nat.cast_one] at hbig
  nlinarith

lemma gg_duplicate_supported_of_two_le {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {n : ℕ} (hn : 2 ≤ n) {A : Fin n → Fin n → ℝ}
    (hA : A ∈ (blockLaw B μ n).support) (p : Fin n) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (n+1)).support,
      (∀ i j : Fin n, C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin n, i ≠ p → C i.castSucc (Fin.last n) = A i p) ∧
      C p.castSucc (Fin.last n) ≤ t := by
  cases n with
  | zero => omega
  | succ a => exact gg_duplicate_supported hm hsym hwe hGG hb hpsd hdiag (by omega) hA p ht



lemma gg_supported_populations {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    {t : ℝ} (ht : ∀ i j, i ≠ j → Q i j ≤ t) :
    ∀ n, 3 ≤ n → ∃ A ∈ (blockLaw B μ n).support,
      (∀ i j, i ≠ j → A i j ≤ t) ∧
      (∀ i j, tripleLabel i ≠ tripleLabel j → A i j = Q (tripleLabel i) (tripleLabel j)) := by
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨Q, hQ, ht, ?_⟩
    intro i j _
    have hh : ∀ i : Fin 3, tripleLabel i = i := fun i => Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hh, hh]
  | succ n hn ih =>
    obtain ⟨A, hAs, hAo, hAc⟩ := ih
    let p : Fin n := ⟨n % 3, (Nat.mod_lt n (by decide : 0 < 3)).trans_le hn⟩
    have hp : tripleLabel p = tripleLabel (Fin.last n) := by
      apply Fin.ext; exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    obtain ⟨C, hCs, hC0, hC1, hCp⟩ := gg_duplicate_supported_of_two_le
      hm hsym hwe hGG hb hpsd hdiag (by omega) hAs p (fun i hi => hAo i p hi)
    have hCsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hCs).1
    refine ⟨C, hCs, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          rw [hCsym]
          by_cases hj : jj = p
          · subst jj; exact hCp
          · rw [hC1 jj hj]; exact hAo jj p hj
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro _
          by_cases hi : ii = p
          · subst ii; exact hCp
          · rw [hC1 ii hi]; exact hAo ii p hi
        · intro hij
          rw [hC0]; exact hAo ii jj (fun he => hij (congrArg Fin.castSucc he))
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro hij
          have hjp : tripleLabel jj ≠ tripleLabel p := by
            intro he; apply hij; exact hp.symm.trans he.symm
          have hjne : jj ≠ p := fun he => hjp (congrArg tripleLabel he)
          rw [hCsym, hC1 jj hjne, hAc jj p hjp, hp, hQsym]
          rfl
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij
          have hip : tripleLabel ii ≠ tripleLabel p := by
            intro he; apply hij; exact he.trans hp
          have hine : ii ≠ p := fun he => hip (congrArg tripleLabel he)
          rw [hC1 ii hine, hAc ii p hip, hp]
          rfl
        · intro hij
          rw [hC0]; exact hAc ii jj hij

lemma gg_supported_triple_ordered {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    (horder : Q 0 2 ≤ Q 1 2) : Q 0 2 ≤ Q 0 1 := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  have hQo : ∀ i j : Fin 3, i ≠ j → Q i j ≤ Q 1 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hlt.le.trans horder
    · exact horder
    · exact (hQsym 1 0).le.trans (hlt.le.trans horder)
    · exact (hij rfl).elim
    · exact le_rfl
    · exact (hQsym 2 0).le.trans horder
    · exact (hQsym 2 1).le
    · exact (hij rfl).elim
  apply no_arbitrary_nonultrametric_duplicates hlt
  intro m hmpos
  obtain ⟨A, hAs, hAo, hAc⟩ := gg_supported_populations hm hsym hwe hGG hb hpsd hdiag
    hQ hQo (3*m) (by omega)
  let e : Fin 3 × Fin m → Fin (3*m) := fun x => ⟨3*x.2.val+x.1.val, by omega⟩
  have he : ∀ i a, tripleLabel (e (i,a)) = i := by
    intro i a
    apply Fin.ext
    dsimp [tripleLabel, e]
    omega
  have hei : Function.Injective e := by
    intro x y hxy
    have hv := congrArg Fin.val hxy
    dsimp [e] at hv
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hgram := blockLaw_support_gram hm hpsd hdiag hAs
  refine ⟨Matrix.submatrix A e e, Matrix.PosSemidef.submatrix hgram.1 e,
    fun _ => hgram.2 _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change A (e (0,i)) (e (1,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (0,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (1,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))

lemma array_entry_abs_le_diagonal {B : RealArray} {D : ℝ}
    (hp : ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j))
    (hd : ∀ i, B i i = D) (i j : ℕ) : |B i j| ≤ D := by
  let n := max i j + 1
  let ii : Fin n := ⟨i, by dsimp [n]; omega⟩
  let jj : Fin n := ⟨j, by dsimp [n]; omega⟩
  have hD : 0 ≤ D := (hp n).diag_nonneg (i := ii) |>.trans (hd i).le
  have hs := psd_cauchy_schwarz (hp n) (Pi.single ii 1) (Pi.single jj 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at hs
  change B i j ^ 2 ≤ D * D at hs
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (B i j - D), sq_nonneg (B i j + D)]

lemma gg_supported_triple_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support) :
    min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
  have hb : ∀ ω i j, |B ω i j| ≤ D :=
    fun ω => array_entry_abs_le_diagonal (hpsd ω) (hdiag ω)
  by_cases ho : Q 0 2 ≤ Q 1 2
  · rw [min_eq_left ho]
    exact gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQ ho
  · have ho' : Q 1 2 ≤ Q 0 2 := le_of_not_ge ho
    rw [min_eq_right ho']
    have hQs := blockLaw_support_swap hm hwe hQ 0 1
    have hqsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
    have hh : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have h := gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQs
      (by simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh] using ho')
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh, hqsym 1 0] using h

 

theorem gg_ultrametric_triple {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, min (B ω 0 2) (B ω 1 2) ≤ B ω 0 1 := by
  have hs : ∀ᵐ A ∂blockLaw B μ 3, A ∈ (blockLaw B μ 3).support :=
    Measure.support_mem_ae
  have ht : ∀ᵐ A ∂blockLaw B μ 3, min (A 0 2) (A 1 2) ≤ A 0 1 :=
    hs.mono (fun _ h => gg_supported_triple_ultrametric hm hsym hwe hGG hpsd hdiag h)
  exact (ae_map_iff (measurable_arrayBlock hm 3).aemeasurable
    (measurableSet_le (by fun_prop) (by fun_prop))).mp ht


lemma finite_permutation_extending {ι β : Type*} [Fintype ι]
    (f g : ι → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : Equiv.Perm β, {b | e b ≠ b}.Finite ∧ ∀ i, e (f i) = g i := by
  classical
  let U : Finset β := Finset.univ.image f ∪ Finset.univ.image g
  let f' : ι → U := fun i => ⟨f i, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  let g' : ι → U := fun i => ⟨g i, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  have hf' : Function.Injective f' := fun i j h => hf (congrArg Subtype.val h)
  have hg' : Function.Injective g' := fun i j h => hg (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g' hf' hg'
  let emb : U ↪ β := Function.Embedding.subtype _
  refine ⟨σ.viaFintypeEmbedding emb, ?_, ?_⟩
  · apply U.finite_toSet.subset
    intro b hb
    by_contra h
    apply hb
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨a, rfl⟩
    exact h a.2
  · intro i
    change σ.viaFintypeEmbedding emb (emb (f' i)) = emb (g' i)
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image, hσ]

lemma gg_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  have ht := gg_ultrametric_triple hm hsym hwe hGG hpsd hdiag
  have hall : ∀ i j k, ∀ᵐ ω ∂μ, min (B ω i k) (B ω j k) ≤ B ω i j := by
    intro i j k
    by_cases hij : i = j
    · subst j
      apply ae_of_all
      intro ω
      have hb := array_entry_abs_le_diagonal (hpsd ω) (hdiag ω) i k
      simpa only [min_self, hdiag] using (le_abs_self (B ω i k)).trans hb
    by_cases hik : i = k
    · subst k
      exact ae_of_all _ (fun ω => by rw [hsym ω j i]; exact min_le_right _ _)
    by_cases hjk : j = k
    · subst k
      exact ae_of_all _ (fun ω => min_le_left _ _)
    let f : Fin 3 → ℕ := fun a => a.val
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e, he, hef⟩ := finite_permutation_extending f g Fin.val_injective hg
    have hh := (hwe e he).ae_mem_snd
      (t := {b : RealArray | min (b 0 2) (b 1 2) ≤ b 0 1})
      (measurableSet_le (by fun_prop) (by fun_prop)) ht
    have he0 : e 0 = i := hef 0
    have he1 : e 1 = j := hef 1
    have he2 : e 2 = k := hef 2
    simpa only [Set.mem_ofPred_eq, permuteArray, he0, he1, he2] using hh
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (hall i j)))


lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

lemma gg_two_links_positive {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {B : Ω → ℕ → ℕ → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hGG : HasEntryGhirlandaGuerra B μ) {A C : Set E}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hpA : 0 < μ.real {ω | B ω 0 1 ∈ A}) (hpC : 0 < μ.real {ω | B ω 0 1 ∈ C}) :
    0 < μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) := by
  have h := hGG 2 (by omega) 0 {b : Fin 2 → Fin 2 → E | b 0 1 ∈ A}
    (hA.preimage (by fun_prop)) C hC
  change μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) = _ at h
  rw [h]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hpA hpC) (by norm_num))
    (div_nonneg (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)) (by norm_num))

lemma ultrametric_no_crossing {r t : RealArray}
    (hr : IsUltrametricArray r) (ht : IsUltrametricArray t)
    (hs : IsUltrametricArray (fun i j => r i j + t i j))
    (hrsym : ∀ i j, r i j = r j i) (htsym : ∀ i j, t i j = t j i) :
    ¬ (r 0 1 < r 0 2 ∧ t 0 2 < t 0 1) := by
  rintro ⟨hR, hT⟩
  have hr23 : r 1 2 = r 0 1 := by
    have h1 := hr 0 1 2
    have h2 := hr 1 2 0
    rw [hrsym 1 0, hrsym 2 0, min_eq_left hR.le] at h2
    have : r 1 2 ≤ r 0 1 := by
      by_contra! hn
      exact (lt_min hR hn).not_ge h1
    exact le_antisymm this h2
  have ht23 : t 1 2 = t 0 2 := by
    have h1 := ht 0 2 1
    have h2 := ht 1 2 0
    rw [htsym 2 1] at h1
    rw [htsym 1 0, htsym 2 0, min_eq_right hT.le] at h2
    have : t 1 2 ≤ t 0 2 := by
      by_contra! hn
      exact (lt_min hT hn).not_ge h1
    exact le_antisymm this h2
  have hh := hs 1 2 0
  simp only [hrsym 1 0, hrsym 2 0, htsym 1 0, htsym 2 0, hr23, ht23] at hh
  exact (lt_min (by linarith) (by linarith)).not_ge hh

 

theorem jointGG_support_ordered {Ω : Type*} [MeasurableSpace Ω]
    {R T : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hR : Measurable R) (hT : Measurable T)
    (hGG : HasEntryGhirlandaGuerra (fun ω i j => (R ω i j, T ω i j)) μ)
    (huR : ∀ᵐ ω ∂μ, IsUltrametricArray (R ω))
    (huT : ∀ᵐ ω ∂μ, IsUltrametricArray (T ω))
    (huS : ∀ᵐ ω ∂μ, IsUltrametricArray (fun i j => R ω i j + T ω i j))
    (hsR : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hsT : ∀ᵐ ω ∂μ, ∀ i j, T ω i j = T ω j i) :
    let ν := μ.map (fun ω => (R ω 0 1, T ω 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  dsimp only
  intro x hx y hy hxy
  by_contra! hc
  let a := (x.1+y.1)/2
  let b := (x.2+y.2)/2
  let A : Set (ℝ × ℝ) := {z | z.1 < a ∧ b < z.2}
  let C : Set (ℝ × ℝ) := {z | a < z.1 ∧ z.2 < b}
  have hAo : IsOpen A := (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hCo : IsOpen C := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_snd continuous_const)
  have hm : Measurable (fun ω => (R ω 0 1, T ω 0 1)) := by fun_prop
  have hyp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) A :=
    (Measure.mem_support_iff_forall x).mp hx A (hAo.mem_nhds (by dsimp [A,a,b]; constructor <;> linarith))
  have hxp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) C :=
    (Measure.mem_support_iff_forall y).mp hy C (hCo.mem_nhds (by dsimp [C,a,b]; constructor <;> linarith))
  rw [Measure.map_apply hm hAo.measurableSet] at hyp
  rw [Measure.map_apply hm hCo.measurableSet] at hxp
  have hp := gg_two_links_positive hGG hAo.measurableSet hCo.measurableSet
    (ENNReal.toReal_pos hyp.ne' (measure_ne_top _ _))
    (ENNReal.toReal_pos hxp.ne' (measure_ne_top _ _))
  have hz : μ ({ω | (R ω 0 1,T ω 0 1) ∈ A} ∩
      {ω | (R ω 0 2,T ω 0 2) ∈ C}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [huR,huT,huS,hsR,hsT] with ω hr ht hs hsr hst
    rintro ⟨ha,hc⟩
    exact ultrametric_no_crossing hr ht hs hsr hst
      ⟨ha.1.trans hc.1, hc.2.trans ha.2⟩
  rw [measureReal_def, hz, ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

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







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma labeledCommonDepth_sum (n : ℕ) (x y : LabeledLeaf n) :
    (∑ d ∈ Finset.range n, if (labeledAddress n x).take (d+1) =
      (labeledAddress n y).take (d+1) then (1:ℝ) else 0) = labeledCommonDepth n x y := by
  have hc := labeledCommonDepth_le n x y
  calc
    _ = ∑ d ∈ Finset.range n, if d < labeledCommonDepth n x y then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [labeled_prefix_eq_iff n x y (d := d+1) (by have := Finset.mem_range.mp hd; omega), Nat.add_one_le_iff]
    _ = labeledCommonDepth n x y := by
      simp only [Finset.sum_boole]
      congr 1
      have he : (Finset.range n).filter (fun d => d < labeledCommonDepth n x y) =
          Finset.range (labeledCommonDepth n x y) := by
        ext d
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
      rw [he,Finset.card_range]

lemma treeOverlap_posSemidef (n : ℕ) {m : ℕ} (x : Fin m → LabeledLeaf n) :
    Matrix.PosSemidef (fun i j => treeOverlap n (x i) (x j)) := by
  classical
  let A : ℕ → Matrix (Fin m) (Fin m) ℝ := fun d =>
    Matrix.submatrix (1 : Matrix (List ChildLabel) (List ChildLabel) ℝ)
      (fun i => (labeledAddress n (x i)).take (d+1)) (fun i => (labeledAddress n (x i)).take (d+1))
  have hp (d : ℕ) : (A d).PosSemidef := Matrix.PosSemidef.one.submatrix _
  have hs := (Matrix.posSemidef_sum (Finset.range n) (fun d _ => hp d)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
  have he : (fun i j => treeOverlap n (x i) (x j)) =
      ((n+1:ℕ):ℝ)⁻¹ • (∑ d ∈ Finset.range n, A d) := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,A,Matrix.submatrix_apply,Matrix.one_apply]
    rw [labeledCommonDepth_sum]
    simp only [treeOverlap,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hs

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma HasGhirlandaGuerra.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {B C : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (he : B =ᵐ[μ] C) :
    HasGhirlandaGuerra C μ := by
  have hm (P : RealArray → Prop) : μ.real {ω | P (C ω)} = μ.real {ω | P (B ω)} := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    change P (C ω) = P (B ω)
    rw [hω]
  intro n hn i A hA t ht
  change μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i n ∈ t} =
    (μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A} * μ.real {ω | C ω 0 1 ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) / n
  rw [hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i n ∈ t),
    hm (fun b => (fun j k : Fin n => b j k) ∈ A), hm (fun b => b 0 1 ∈ t)]
  have hs : (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) =
      ∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A ∧ B ω i j ∈ t} := by
    apply Finset.sum_congr rfl
    intro j _
    exact hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i j ∈ t)
  rw [hs]
  exact h n hn i A hA t ht

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

lemma GramDiagonal.default {D : ℝ} (hD : 0 ≤ D) :
    GramDiagonal D (fun i j => if i=j then D else 0) := by
  constructor
  · intro n
    have he : (fun i j : Fin n => if (i:ℕ)=(j:ℕ) then D else 0) =
        Matrix.diagonal (fun _ : Fin n => D) := by
      ext i j
      simp only [Matrix.diagonal_apply,Fin.val_inj]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun _ => hD)
  · intro i
    simp

 

lemma gg_ultrametric_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have hcwe : WeaklyExchangeable C μ := by
    intro e hefin
    have ht := (IdentDistrib.of_ae_eq hm.aemeasurable he).comp
      (u := permuteArray e) (by unfold permuteArray; fun_prop)
    exact (IdentDistrib.of_ae_eq hm.aemeasurable he).symm.trans ((hwe e hefin).trans ht)
  have ht := gg_ultrametric hc (fun ω => (hCG ω).symm) hcwe (hgg.congr_ae he)
    (fun ω => (hCG ω).1) (fun ω => (hCG ω).2)
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht


end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma le_cdf_overlapQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    u ≤ cdf μ (overlapQuantile μ u) := by
  rw [← (cdf μ).iInf_Ioi_eq]
  apply le_ciInf
  intro y
  obtain ⟨x,hx,hxy⟩ := exists_lt_of_csInf_lt (quantileSet_nonempty hs hu) y.2
  exact hx.2.trans ((monotone_cdf μ) hxy.le)

lemma overlapQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hx : x ∈ Icc (0:ℝ) 1) : overlapQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · intro h
    exact (le_cdf_overlapQuantile hs hu.2.le).trans ((monotone_cdf μ) h)
  · intro h
    exact csInf_le (quantileSet_bddBelow μ u) ⟨hx,h⟩

lemma cdf_of_lt_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {x : ℝ} (hx : x < 0) : cdf μ x = 0 := by
  rw [cdf_eq_real,Measure.real]
  have he : μ (Iic x) = 0 := by
    apply measure_mono_null (t := {y : ℝ | ¬y ∈ Icc (0:ℝ) 1}) _ (ae_iff.mp hs)
    intro y hy hy'
    exact (not_le.mpr (hx.trans_le hy'.1)) hy
  rw [he,ENNReal.toReal_zero]

lemma quantileFunction_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    quantileFunction μ u ≤ x ↔ u ≤ cdf μ x := by
  by_cases hx : x < 0
  · rw [cdf_of_lt_zero hs hx]
    exact iff_of_false (not_le.mpr (hx.trans_le (quantileFunction_mem hs u).1))
      (not_le.mpr hu.1)
  · by_cases hx' : x ≤ 1
    · simpa only [quantileFunction,min_eq_left hu.2.le] using overlapQuantile_le_iff hs hu ⟨le_of_not_gt hx,hx'⟩
    · have hc : cdf μ x = 1 := le_antisymm (cdf_le_one μ x)
        (by simpa only [cdf_one_of_unit_support hs] using (monotone_cdf μ) (le_of_not_ge hx'))
      rw [hc]
      exact iff_of_true ((quantileFunction_mem hs u).2.trans (le_of_not_ge hx')) hu.2.le

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

lemma quantile_preimage_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (x : ℝ) :
    quantileFunction μ ⁻¹' Iic x =ᵐ[unitUniform] Iic (cdf μ x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact propext (quantileFunction_le_iff hs hu)

 
lemma quantileFunction_law {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) : unitUniform.map (quantileFunction μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (monotone_quantileFunction hs).measurable measurableSet_Iic,
    measure_congr (quantile_preimage_Iic hs x),unitUniform_Iic ⟨cdf_nonneg μ x,cdf_le_one μ x⟩,
    ofReal_cdf]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
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
namespace IsingPerceptron

lemma map_restrict_fst_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hS : MeasurableSet S) :
    ((μ.restrict (univ ×ˢ T)).map Prod.fst) S = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_fst hS,Measure.restrict_apply (hS.preimage measurable_fst)]
  congr 1
  ext x
  simp

lemma map_restrict_snd_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hT : MeasurableSet T) :
    ((μ.restrict (S ×ˢ univ)).map Prod.snd) T = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_snd hT,Measure.restrict_apply (hT.preimage measurable_snd)]
  congr 1
  ext x
  simp [and_comm]

lemma measure_pair_eq_of_lower_rectangles {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ a b : ℝ, μ (Iic a ×ˢ Iic b) = ν (Iic a ×ˢ Iic b))
    (hU : μ univ = ν univ) : μ = ν := by
  have hfirst (a : ℝ) : (μ.restrict (Iic a ×ˢ univ)).map Prod.snd =
      (ν.restrict (Iic a ×ˢ univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro b
    rw [map_restrict_snd_rectangle μ measurableSet_Iic,map_restrict_snd_rectangle ν measurableSet_Iic]
    exact h a b
  have hsecond (T : Set ℝ) (hT : MeasurableSet T) :
      (μ.restrict (univ ×ˢ T)).map Prod.fst = (ν.restrict (univ ×ˢ T)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro a
    rw [map_restrict_fst_rectangle μ measurableSet_Iic,map_restrict_fst_rectangle ν measurableSet_Iic]
    have he := congrArg (fun ρ : Measure ℝ => ρ T) (hfirst a)
    simpa only [map_restrict_snd_rectangle μ hT,map_restrict_snd_rectangle ν hT] using he
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod _ hU
  rintro _ ⟨S,hS,T,hT,rfl⟩
  have he := congrArg (fun ρ : Measure ℝ => ρ S) (hsecond T hT)
  simpa only [map_restrict_fst_rectangle μ hS,map_restrict_fst_rectangle ν hS] using he

lemma ordered_pair_cdf (μ : Measure (ℝ × ℝ))
    (ho : ∀ x ∈ μ.support, ∀ y ∈ μ.support, x.1 < y.1 → x.2 ≤ y.2) (a b : ℝ) :
    μ (Iic a ×ˢ Iic b) = min (μ (Prod.fst ⁻¹' Iic a)) (μ (Prod.snd ⁻¹' Iic b)) := by
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic a
  let T : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic b
  have hrect : Iic a ×ˢ Iic b = S ∩ T := rfl
  rw [hrect]
  change μ (S ∩ T) = min (μ S) (μ T)
  have hsupport : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  by_cases h : ∀ x ∈ μ.support, x ∈ S → x ∈ T
  · have hst : S ≤ᵐ[μ] T := hsupport.mono (fun x hx => h x hx)
    rw [min_eq_left (measure_mono_ae hst)]
    apply measure_congr
    filter_upwards [hst] with x hx
    exact propext ⟨fun hh => hh.1,fun hh => ⟨hh,hx hh⟩⟩
  · push Not at h
    obtain ⟨x,hx,hxs,hxt⟩ := h
    have hts : T ≤ᵐ[μ] S := by
      filter_upwards [hsupport] with y hy
      intro hyt
      change y.1 ≤ a
      by_contra! hy'
      have hxy := ho x hx y hy (lt_of_le_of_lt hxs hy')
      exact hxt (hxy.trans hyt)
    rw [min_eq_right (measure_mono_ae hts)]
    apply measure_congr
    filter_upwards [hts] with y hy
    exact propext ⟨fun hh => hh.2,fun hh => ⟨hy hh,hh⟩⟩

lemma pair_quantile_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (a b : ℝ) :
    (unitUniform.map (fun u => (quantileFunction μ u,quantileFunction ν u))) (Iic a ×ˢ Iic b) =
      min (μ (Iic a)) (ν (Iic b)) := by
  rw [Measure.map_apply ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable) (measurableSet_Iic.prod measurableSet_Iic)]
  have he : (fun u => (quantileFunction μ u,quantileFunction ν u)) ⁻¹' (Iic a ×ˢ Iic b) =ᵐ[unitUniform]
      Iic (min (cdf μ a) (cdf ν b)) := by
    filter_upwards [quantile_preimage_Iic hμ a,quantile_preimage_Iic hν b] with u hu hv
    change (quantileFunction μ u ≤ a ∧ quantileFunction ν u ≤ b) = (u ≤ min (cdf μ a) (cdf ν b))
    rw [le_min_iff]
    exact congrArg₂ And hu hv
  rw [measure_congr he,unitUniform_Iic ⟨le_min (cdf_nonneg μ a) (cdf_nonneg ν b),
    (min_le_left _ _).trans (cdf_le_one μ a)⟩,ENNReal.ofReal_min,ofReal_cdf,ofReal_cdf]

 

theorem ordered_pair_quantile_law {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (ho : ∀ x ∈ ρ.support, ∀ y ∈ ρ.support, x.1 < y.1 → x.2 ≤ y.2)
    (hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0:ℝ) 1 ∧ x.2 ∈ Icc (0:ℝ) 1) :
    unitUniform.map (fun u => (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u)) = ρ := by
  let : IsProbabilityMeasure (ρ.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (ρ.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance
  have hμ : ∀ᵐ x ∂ρ.map Prod.fst, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.1))
  have hν : ∀ᵐ x ∂ρ.map Prod.snd, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.2))
  let : IsProbabilityMeasure (unitUniform.map (fun u =>
      (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u))) :=
    (Measure.isProbabilityMeasure_map_iff ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable).aemeasurable).mpr inferInstance
  apply measure_pair_eq_of_lower_rectangles _ (by simp)
  intro a b
  rw [pair_quantile_cdf hμ hν,ordered_pair_cdf ρ ho,
    Measure.map_apply measurable_fst measurableSet_Iic,Measure.map_apply measurable_snd measurableSet_Iic]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma continuous_treeTail (n d : ℕ) : Continuous (treeTail n d) := by
  unfold treeTail; fun_prop

lemma treeTail_mem (n d : ℕ) (t : ℝ) : treeTail n d t ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma treeTail_level (n d j : ℕ) : treeTail n d ((j:ℝ)/(n+1:ℕ)) =
    if d < j then 1 else 0 := by
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [treeTail,mul_div_cancel₀ _ hn]
  split_ifs with h
  · have h' : (d:ℝ)+1 ≤ j := by exact_mod_cast h
    rw [min_eq_left (by linarith),max_eq_right zero_le_one]
  · have h' : (j:ℝ) ≤ d := by exact_mod_cast (Nat.le_of_not_gt h)
    rw [min_eq_right (by linarith),max_eq_left (by linarith)]

lemma treeTail_overlap (n : ℕ) (d : Fin n) (x y : LabeledLeaf n) :
    treeTail n d (treeOverlap n x y) =
      if (labeledAddress n x).take (d+1) = (labeledAddress n y).take (d+1) then 1 else 0 := by
  rw [treeOverlap,treeTail_level]
  simp only [labeled_prefix_eq_iff n x y (d := d+1) (by omega),Nat.add_one_le_iff]

lemma isClosed_treeLevels (n : ℕ) : IsClosed (treeLevels n) := (finite_range _).isClosed

lemma treeOverlap_mem_levels (n : ℕ) (x y : LabeledLeaf n) : treeOverlap n x y ∈ treeLevels n :=
  ⟨⟨labeledCommonDepth n x y,by have := labeledCommonDepth_le n x y; omega⟩,rfl⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma treeTail_eq_level_indicator {n d : ℕ} {t : ℝ} (ht : t ∈ treeLevels n) :
    treeTail n d t = if (d:ℝ)/(n+1:ℕ) < t then 1 else 0 := by
  obtain ⟨j,rfl⟩ := ht
  rw [treeTail_level]
  simp only [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (n+1:ℕ)),Nat.cast_lt]

lemma cdf_of_treeTail {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {n d : ℕ}
    (hρ : ∀ᵐ t ∂ρ, t ∈ treeLevels n) {b : ℝ}
    (hb : (∫ t, treeTail n d t ∂ρ) = 1-b) : cdf ρ ((d:ℝ)/(n+1:ℕ)) = b := by
  have hi : Integrable (treeTail n d) ρ :=
    integrable_of_measurable_abs_le (continuous_treeTail n d).measurable
      (fun t => by rw [abs_of_nonneg (treeTail_mem n d t).1]; exact (treeTail_mem n d t).2)
  calc
    _ = ∫ t, (Iic ((d:ℝ)/(n+1:ℕ))).indicator (fun _ => (1:ℝ)) t ∂ρ := by
      rw [integral_indicator_const _ measurableSet_Iic,cdf_eq_real,smul_eq_mul,mul_one]
    _ = ∫ t, 1-treeTail n d t ∂ρ := integral_congr_ae (hρ.mono (fun t ht => by
      simp only [treeTail_eq_level_indicator (d := d) ht]
      by_cases h : (d:ℝ)/(n+1:ℕ) < t
      · simp only [Set.indicator,Set.mem_Iic,h,not_le.mpr h,ite_false, if_false,ite_true, if_true,sub_self]
      · simp only [Set.indicator,Set.mem_Iic,h,le_of_not_gt h,ite_false, if_false,ite_true, if_true,sub_zero]))
    _ = b := by rw [integral_sub (integrable_const _) hi,hb]; simp

lemma quantile_treeTail {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {n d : ℕ}
    (hs : ∀ᵐ t ∂ρ, t ∈ Icc (0:ℝ) 1)
    (hρ : ∀ᵐ t ∂ρ, t ∈ treeLevels n) {b : ℝ}
    (hb : (∫ t, treeTail n d t ∂ρ) = 1-b) :
    ∀ᵐ u ∂unitUniform, treeTail n d (quantileFunction ρ u) = if b < u then 1 else 0 := by
  have hm := (monotone_quantileFunction hs).measurable
  have hl := quantileFunction_law hs
  have hlev : ∀ᵐ u ∂unitUniform, quantileFunction ρ u ∈ treeLevels n := by
    apply (ae_map_iff hm.aemeasurable (isClosed_treeLevels n).measurableSet).mp
    rw [hl]
    exact hρ
  have hc := cdf_of_treeTail hρ hb
  filter_upwards [hlev,ae_restrict_mem (μ := volume) measurableSet_Ioo] with u hu hu'
  rw [treeTail_eq_level_indicator hu]
  have he := quantileFunction_le_iff hs hu' (x := (d:ℝ)/(n+1:ℕ))
  rw [hc] at he
  have he' : (d:ℝ)/(n+1:ℕ) < quantileFunction ρ u ↔ b < u := by
    simpa only [not_le] using not_congr he
  simp only [he']



end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





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





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma continuous_depthTail (n j : ℕ) : Continuous (depthTail n j) := by
  unfold depthTail
  split_ifs
  · exact continuous_const
  · exact continuous_treeTail n (j-1)
lemma depthTail_level (n j d : ℕ) : depthTail n j ((d:ℝ)/(n+1:ℕ)) = if j ≤ d then 1 else 0 := by
  by_cases hj : j=0
  · simp [depthTail,hj]
  · simp only [depthTail,hj,ite_false, if_false,treeTail_level,show j-1<d ↔ j ≤ d by omega]

lemma finiteFieldPath_single {n : ℕ} (j : Fin (n+1)) (i : ℕ) :
    finiteFieldPath (Pi.single j (1:ℝ)) i=if j.val ≤ i then 1 else 0 := by
  classical
  unfold finiteFieldPath
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · simp

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

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

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

lemma integral_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u ∂pathMeasure) = ∑ i, (ζ i.succ-ζ i.castSucc)*v i := by
  classical
  let : IsFiniteMeasure pathMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs (i : Fin k) : Ioo (ζ i.castSucc) (ζ i.succ) ⊆ Ioo (0:ℝ) 1 := by
    intro u hu
    have h0 : 0≤ζ i.castSucc := by rw [← hz0]; exact hz.monotone (Fin.zero_le _)
    have h1 : ζ i.succ≤1 := by rw [← hz1]; exact hz.monotone (Fin.le_last _)
    exact ⟨h0.trans_lt hu.1,hu.2.trans_le h1⟩
  have hind (i : Fin k) : (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) =
      (Ioo (ζ i.castSucc) (ζ i.succ)).indicator (fun _ : ℝ => v i) := by
    ext u
    simp only [Set.indicator_apply,Set.mem_Ioo]
  have hi (i : Fin k) : Integrable (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) pathMeasure := by
    rw [hind]
    exact (integrable_const (v i)).indicator measurableSet_Ioo
  unfold finiteStepFunction
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hind]
  rw [integral_indicator measurableSet_Ioo]
  have he : pathMeasure.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) = volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (hs i)]
  rw [he,integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hz.monotone (Fin.castSucc_le_succ i))),smul_eq_mul]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteStep_tail_indicator {k : ℕ} (ζ : Fin (k+1) → ℝ) (hz : StrictMono ζ)
    (v : Fin k → ℝ) (d : Fin (k+1)) :
    (Ioi (ζ d)).indicator (finiteStepFunction ζ v) =
      finiteStepFunction ζ (fun i => if d ≤ i.castSucc then v i else 0) := by
  classical
  ext u
  rw [Set.indicator_apply]
  simp only [Set.mem_Ioi,finiteStepFunction]
  by_cases hd : ζ d < u
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ζ i.castSucc < u ∧ u < ζ i.succ
    · simp only [ite_eq_left hi]
      have hj : d ≤ i.castSucc := by
        by_contra h
        have hs : i.succ ≤ d := by
          change i.val+1 ≤ d.val
          simp only [Fin.le_def,Fin.val_castSucc] at h
          omega
        have H := hz.monotone hs
        linarith
      rw [ite_eq_left hj]
    · simp only [ite_eq_right hi]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : ζ i.castSucc < u ∧ u < ζ i.succ
    · rw [ite_eq_left hi]
      have hj : ¬d ≤ i.castSucc := fun h => hd ((hz.monotone h).trans_lt hi.1)
      rw [ite_eq_right hj]
    · rw [ite_eq_right hi]

lemma integral_finiteStep_tail {k : ℕ} (ζ : Fin (k+1) → ℝ) (hz : StrictMono ζ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) (d : Fin (k+1)) :
    (∫ u in Ioi (ζ d), finiteStepFunction ζ v u ∂pathMeasure) =
      ∑ i : Fin k, if d ≤ i.castSucc then (ζ i.succ-ζ i.castSucc)*v i else 0 := by
  rw [← integral_indicator measurableSet_Ioi,finiteStep_tail_indicator ζ hz,
    integral_finiteStepFunction ζ hz hz0 hz1]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







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

/-- Each spectral overlap component is a positive semidefinite Gram kernel. -/
lemma projectedOverlap_posSemidef {N m : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (σ : Fin m → Spin N) :
    Matrix.PosSemidef (fun i j => projectedOverlap U I (σ i) (σ j)) := by
  classical
  let A : Matrix (Fin m) (Fin N) ℝ := fun i k =>
    if k ∈ I then U (spinVector (σ i)) k else 0
  have hp := (Matrix.posSemidef_self_mul_conjTranspose A).smul
    (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
  have he : (fun i j : Fin m => projectedOverlap U I (σ i) (σ j)) =
      (N : ℝ)⁻¹ • (A * Aᴴ) := by
    ext i j
    change (N : ℝ)⁻¹ * (∑ k ∈ I, U (spinVector (σ i)) k * U (spinVector (σ j)) k) =
      (N : ℝ)⁻¹ * ∑ k, (if k ∈ I then U (spinVector (σ i)) k else 0) *
        (if k ∈ I then U (spinVector (σ j)) k else 0)
    congr 1
    simp only [ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.inter_self]
  rw [he]
  exact hp

/-- Full spectral overlap agrees with the ordinary spin overlap, because an
orthogonal rotation preserves the inner product. -/
lemma projectedOverlap_univ {N : ℕ} (U : Rotation N) (σ τ : Spin N) :
    projectedOverlap U Finset.univ σ τ =
      (N : ℝ)⁻¹ * ∑ i, spinValue (σ i) * spinValue (τ i) := by
  simp only [projectedOverlap]
  congr 1
  have h := U.inner_map_map (spinVector σ) (spinVector τ)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    spinVector_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using h

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
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability _root_.OAI.InvariantIsing.tensorLabeledReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) :
    Continuous (permuteSpectralArray (m := m) e) := by
  unfold permuteSpectralArray
  fun_prop

lemma disorderReplicaLaw_map_reindex {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (e : ℕ → ℕ) (he : Function.Injective e) :
    (disorderReplicaLaw P ν hν).map (Prod.map id (fun σ i => σ (e i))) =
      disorderReplicaLaw P ν hν := by
  unfold disorderReplicaLaw
  rw [← Measure.compProd_map (by fun_prop)]
  congr 1
  apply Kernel.ext
  intro ω
  rw [Kernel.map_apply _ (by fun_prop)]
  change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => σ (e i)) =
    Measure.infinitePi (fun _ : ℕ => ν ω)
  exact Measure.map_infinitePi_infinitePi_of_inj he

lemma spectralArrayLaw_map_reindex {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (e : ℕ → ℕ) (he : Function.Injective e) :
    (spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = spectralArrayLaw P U hU I n ν hν := by
  change ((disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n)).map _ = _
  rw [Measure.map_map (continuous_permuteSpectralArray e).measurable
    (measurable_spectralReplicaArray U hU I n)]
  have heq : permuteSpectralArray e ∘ spectralReplicaArray U I n =
      spectralReplicaArray U I n ∘ Prod.map id (fun σ i => σ (e i)) := rfl
  rw [heq, ← Measure.map_map (measurable_spectralReplicaArray U hU I n) (by fun_prop),
    disorderReplicaLaw_map_reindex P ν hν e he]
  rfl

lemma spectralArray_limit_reindex {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (e : ℕ → ℕ)
    (hE : ∀ k, (L k : Measure (SpectralArray m)).map (permuteSpectralArray e) = L k) :
    (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q := by
  have hc := (ProbabilityMeasure.continuous_map (continuous_permuteSpectralArray e)).tendsto Q
  have he : (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = L := by
    funext k
    exact Subtype.ext (hE k)
  have ht := hc.comp hL
  change Tendsto (fun k => (L k).map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) _ _ at ht
  rw [he] at ht
  have heq : Q.map (f := (permuteSpectralArray e)) (by first | (apply Continuous.aemeasurable; apply continuous_permuteSpectralArray <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = Q := tendsto_nhds_unique ht hL
  exact congrArg Subtype.val heq

lemma scalar_of_spectral_exchangeable {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (f : SpectralEntry m → ℝ) (hf : Measurable f) :
    WeaklyExchangeable (fun x i j => f (x (i,j))) (Q : Measure (SpectralArray m)) := by
  intro e _
  have hm : Measurable (fun x : SpectralArray m => fun i j => f (x (i,j))) := by fun_prop
  refine ⟨hm.aemeasurable, (hm.comp (continuous_permuteSpectralArray e).measurable).aemeasurable, ?_⟩
  calc
    _ = ((Q : Measure (SpectralArray m)).map (permuteSpectralArray e)).map
        (fun x i j => f (x (i,j))) :=
      congrArg (Measure.map (fun x i j => f (x (i,j)))) (hE e).symm
    _ = _ := Measure.map_map hm (continuous_permuteSpectralArray e).measurable

lemma isClosed_spectralGram (m : ℕ) : IsClosed {x : SpectralArray m | SpectralGram x} := by
  unfold SpectralGram
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun n =>
    (isClosed_setOf_posSemidef n).preimage (by unfold spectralCoordinateArray; fun_prop)

lemma spectralReplicaArray_gram {Ω : Type*} {N m : ℕ} (U : Ω → SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (p : Ω × (ℕ → Spin N × LabeledLeaf n)) : SpectralGram (spectralReplicaArray U I n p) := by
  intro a z
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_tree] using
      treeOverlap_posSemidef n (fun i : Fin z => (p.2 i).2)
  · simpa only [spectralCoordinateArray, spectralReplicaArray, spectralJointEntry_spectral] using
      projectedOverlap_posSemidef (specialRotation (U p.1)) (I j) (fun i : Fin z => (p.2 i).1)

lemma spectralArrayLaw_gram {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))), SpectralGram x := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n), SpectralGram x
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    (isClosed_spectralGram (m + 1)).measurableSet]
  exact ae_of_all _ (spectralReplicaArray_gram U I n)

lemma spectralArray_limit_gram {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray m)), SpectralGram x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x :=
  ae_closed_of_weak_limit hL (isClosed_spectralGram m) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGGGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_spectralLinearEntry {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearEntry w) := by
  unfold spectralLinearEntry
  fun_prop

lemma continuous_spectralLinearArray {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearArray w) := by
  unfold spectralLinearArray spectralLinearEntry
  fun_prop

lemma spectralGram_linear {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q w : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a)
    (hw : ∀ a, 0 ≤ w a) :
    GramDiagonal (∑ a, w a * q a) (spectralLinearArray w x) := by
  constructor
  · intro n
    have hp := Matrix.posSemidef_sum Finset.univ (fun a _ => (hG a n).smul (hw a))
    have he : (fun i j : Fin n => spectralLinearArray w x i j) =
        ∑ a : Fin m, w a • (fun i j : Fin n => spectralCoordinateArray a x i j) := by
      ext i j
      simp [spectralLinearArray, spectralLinearEntry, spectralCoordinateArray]
    rw [he]
    exact hp
  · intro i
    simp only [spectralLinearArray, spectralLinearEntry, hd]

lemma spectralGG_linear_ultrametric {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), IsUltrametricArray (spectralLinearArray w x) := by
  exact gg_ultrametric_ae (continuous_spectralLinearArray w).measurable
    (scalar_of_spectral_exchangeable hE (spectralLinearEntry w)
      (continuous_spectralLinearEntry w).measurable)
    (hgg.real_map (continuous_spectralLinearEntry w).measurable)
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hq a))
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_linear hx q w hdx hw)

/-- Nonnegative combinations of the actual spectral and tree coordinates have
ordered joint support. This is the finite-vector consequence used for the
manuscript's simultaneous overlap paths. -/
theorem spectralGG_support_ordered {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) :
    let ν := (Q : Measure (SpectralArray m)).map
      (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  have hsum := spectralGG_linear_ultrametric hgg hG q hq hd hE
    (w + z) (fun a => add_nonneg (hw a) (hz a))
  have he (x : SpectralArray m) : spectralLinearArray (w + z) x =
      fun i j => spectralLinearArray w x i j + spectralLinearArray z x i j := by
    funext i j
    simp only [spectralLinearArray, spectralLinearEntry, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [he] at hsum
  exact jointGG_support_ordered (continuous_spectralLinearArray w).measurable
    (continuous_spectralLinearArray z).measurable
    (hgg.map (f := fun x => (spectralLinearEntry w x, spectralLinearEntry z x))
      ((continuous_spectralLinearEntry w).prodMk (continuous_spectralLinearEntry z)).measurable)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE w hw)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE z hz) hsum
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q w hdx hw).symm)
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q z hdx hz).symm)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of weak limits of the actual perturbed tensor array laws. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma tensorPerturbedArrayLaw_gram {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      SpectralGram x := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_gram _ _ _ _ _ _ _

lemma tensorPerturbedArrayLaw_reindex {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (e : ℕ → ℕ) (he : Function.Injective e) :
    (tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))).map
      (permuteSpectralArray e) = tensorPerturbedArrayLaw μ eig c I u v t n b h := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_map_reindex _ _ _ _ _ _ _ e he

/-- The geometry is derived from the actual finite Gibbs samples, independently
of the subsequent concentration/minimization argument that enforces GG. -/
theorem tensorPerturbedArrayLaw_limit_geometry (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) :
    (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x) ∧
      ∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q := by
  constructor
  · exact spectralArray_limit_gram hL (fun k => tensorPerturbedArrayLaw_gram
      (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k))
  · intro e he
    exact spectralArray_limit_reindex hL e (fun k => tensorPerturbedArrayLaw_reindex
      (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k) e he)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorCascadeReplicaAverage
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.hyperplaneReflection_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.rotationMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma projectedOverlap_partition {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ) (σ τ : Spin N) :
    (∑ a, projectedOverlap U (I a) σ τ) = projectedOverlap U Finset.univ σ τ := by
  classical
  unfold projectedOverlap
  rw [← Finset.mul_sum]
  congr 1
  have hs := Finset.sum_biUnion (f := fun i => U (spinVector σ) i * U (spinVector τ) i)
    (show Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) I by simpa using hdis)
  rw [hcover] at hs
  exact hs.symm

lemma spectralSpinWeight_nonneg (m : ℕ) (a : Fin (m + 1)) : 0 ≤ spectralSpinWeight m a := by
  refine Fin.lastCases ?_ (fun _ => ?_) a <;> simp [spectralSpinWeight]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorArrayWard
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched array laws satisfy the normalized spectral block Ward bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma spectralSpinArray_joint {N m n : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (σ : ℕ → Spin N × LabeledLeaf n) (i j : ℕ) :
    spectralSpinArray (fun ij : ℕ × ℕ => spectralJointEntry U I n (σ ij.1) (σ ij.2)) i j =
      spinPairOverlap (σ i).1 (σ j).1 := by
  simp only [spectralSpinArray, spectralJointEntry_spectral]
  rw [projectedOverlap_partition U I hdis hcover, projectedOverlap_univ]
  rfl

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantilePaths
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous pair quantile laws of the actual spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralQuantilePath_law {m : ℕ} (Q : ProbabilityMeasure (SpectralArray m)) (w : Fin m → ℝ)
    (hs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.pathMeasure.map (spectralQuantilePath Q w hs) = spectralLinearLaw Q w := by
  exact quantileFunction_law (spectralLinearLaw_unit Q w hs)

/-- All pairs of required nonnegative linear overlap combinations have
simultaneous quantile laws. The total spin combination is included once its
unit bound is derived from the genuine spectral partition. -/
theorem spectralQuantilePath_pair_law {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a)
    (hws : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1)
    (hzs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray z x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.pathMeasure.map
      (fun s => (spectralQuantilePath Q w hws s, spectralQuantilePath Q z hzs s)) =
      (Q : Measure (SpectralArray m)).map
        (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)) := by
  let F := fun x : SpectralArray m => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)
  have hm : Measurable F := by unfold F spectralLinearArray spectralLinearEntry; fun_prop
  let ρ := (Q : Measure (SpectralArray m)).map F
  let : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [hws, hzs] with x hx hy
    exact ⟨hx, hy⟩
  have hfirst : ρ.map Prod.fst = spectralLinearLaw Q w := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_fst hm]
    rfl
  have hsecond : ρ.map Prod.snd = spectralLinearLaw Q z := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_snd hm]
    rfl
  have he := ordered_pair_quantile_law (spectralGG_support_ordered hgg hG q hq hd hE w z hw hz) hs
  rw [hfirst, hsecond] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReplicaProduct
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica products for the actual simultaneous spectral GG limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spectralSpinQuantilePath_law {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    pathMeasure.map (spectralSpinQuantilePath Q hP hn) =
      scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray := by
  have he := spectralQuantilePath_law Q (spectralSpinWeight m)
    (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn)
  simpa only [spectralSpinQuantilePath, spectralLinearLaw, scalarOverlapLaw,
    spectralLinearArray_spinWeight] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralTreeTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A synchronized spin/tree pair turns a tree-level contact test into an
upper tail of the spin quantile. Atoms at partition endpoints are retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma integral_pathMeasure_Ioi (p : OverlapPath) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ s in Ioi b, p s ∂pathMeasure) = pathTail p b := by
  have he : Ioi b ∩ Ioo (0 : ℝ) 1 = Ioo b 1 := by
    ext s
    constructor
    · intro hs; exact ⟨hs.1, hs.2.2⟩
    · intro hs; exact ⟨hs.1, hb.1.trans_lt hs.1, hs.2⟩
  rw [pathMeasure, Measure.restrict_restrict measurableSet_Ioi, he,
    pathTail, intervalIntegral.integral_of_le hb.2, integral_Ioc_eq_integral_Ioo]

theorem spectralPair_treeTail_integral {m n d : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (hlevel : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) (Fin.last m) : ℝ) ∈ treeLevels n)
    {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (htail : (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - b) :
    (∫ x, spectralSpinArray x 0 1 * treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = pathTail (spectralSpinQuantilePath Q hP hn) b := by
  classical
  let w : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  have hw : ∀ a, 0 ≤ w a := by
    intro a
    simp only [w, Pi.single_apply]
    split_ifs <;> norm_num
  have hsu : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralSpinWeight m) x 0 1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
  have htu : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using
      spectralCoordinate_unit hn (Fin.last m)
  have hm : Measurable (fun x : SpectralArray (m + 1) => spectralLinearArray w x 0 1) :=
    (continuous_spectralLinearEntry w).measurable.comp (measurable_pi_apply (0,1))
  have hms : Measurable (fun x : SpectralArray (m + 1) =>
      spectralLinearArray (spectralSpinWeight m) x 0 1) :=
    (continuous_spectralLinearEntry _).measurable.comp (measurable_pi_apply (0,1))
  have htL : ∀ᵐ s ∂spectralLinearLaw Q w, s ∈ treeLevels n := by
    change ∀ᵐ s ∂(Q : Measure _).map (fun x => spectralLinearArray w x 0 1), s ∈ treeLevels n
    apply (ae_map_iff hm.aemeasurable (isClosed_treeLevels n).measurableSet).mpr
    change ∀ᵐ x ∂(Q : Measure _), spectralLinearArray w x 0 1 ∈ treeLevels n
    filter_upwards [hlevel] with x hx
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using hx
  have htM : (∫ s, treeTail n d s ∂spectralLinearLaw Q w) = 1 - b := by
    rw [spectralLinearLaw, integral_map hm.aemeasurable
      (continuous_treeTail n d).aestronglyMeasurable]
    simpa only [w, spectralLinearArray_single, spectralCoordinateArray] using htail
  have htq := quantile_treeTail (spectralLinearLaw_unit Q w htu) htL htM
  have hp := spectralQuantilePath_pair_law hgg hG q hq hd hE
    (spectralSpinWeight m) w (spectralSpinWeight_nonneg m) hw hsu htu
  let F : ℝ × ℝ → ℝ := fun z => z.1 * treeTail n d z.2
  have hF : AEStronglyMeasurable F
      (pathMeasure.map (fun s => (spectralQuantilePath Q (spectralSpinWeight m) hsu s,
        spectralQuantilePath Q w htu s))) := by
    exact (continuous_fst.mul ((continuous_treeTail n d).comp continuous_snd)).aestronglyMeasurable
  have hi := integral_map
    ((spectralQuantilePath Q (spectralSpinWeight m) hsu).measurable.prodMk
      (spectralQuantilePath Q w htu).measurable).aemeasurable hF
  rw [hp] at hi
  have hiF : AEStronglyMeasurable F ((Q : Measure _).map
      (fun x => (spectralLinearArray (spectralSpinWeight m) x 0 1,
        spectralLinearArray w x 0 1))) := by
    exact (continuous_fst.mul ((continuous_treeTail n d).comp continuous_snd)).aestronglyMeasurable
  rw [integral_map (hms.prodMk hm).aemeasurable hiF] at hi
  have he : (∫ s, spectralSpinQuantilePath Q hP hn s *
      treeTail n d (spectralQuantilePath Q w htu s) ∂pathMeasure) =
      ∫ s in Ioi b, spectralSpinQuantilePath Q hP hn s ∂pathMeasure := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [htq] with s hs
    change _ * treeTail n d (quantileFunction (spectralLinearLaw Q w) s) = _
    rw [hs]
    by_cases hbs : b < s <;> simp [hbs]
  rw [integral_pathMeasure_Ioi _ hb] at he
  simpa only [F, spectralLinearArray_spinWeight, w, spectralLinearArray_single,
    spectralCoordinateArray, spectralSpinQuantilePath] using hi.trans he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorFieldTailBridge
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.spinValue_not
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact field directions are bounded continuous tests of the actual
spectral array, so their expectations pass to the synchronized limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_spectralSpinDepthTail {m : ℕ} (n j : ℕ) :
    Continuous (spectralSpinDepthTail (m := m) n j) := by
  unfold spectralSpinDepthTail
  exact (show Continuous (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) by
    unfold spectralSpinArray; fun_prop).mul
      ((continuous_depthTail n j).comp (by fun_prop))

lemma tensorNamespacedArrayLaw_field_tail {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N))
    (hdis : Set.PairwiseDisjoint (Set.univ : Set (Fin m)) I)
    (hcover : Finset.univ.biUnion I = Finset.univ)
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (b h : ℕ → ℝ)
    (r : Fin k → ℕ) (j : Fin (n + 1)) :
    (∫ x, spectralSpinDepthTail n j x
      ∂(tensorNamespacedArrayLaw μ eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) =
      tensorNamespacedReplicaAverage μ eig c I degree amp n b r h
        (fun _ => tensorFieldPairObservable (finiteFieldPath (Pi.single j 1))) := by
  classical
  refine tensorNamespacedArrayLaw_test μ eig c I degree amp n b r h _
    (continuous_spectralSpinDepthTail n j) _ ![1,0] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro U σ
    simp only [spectralSpinDepthTail, spectralSpinArray_joint (specialRotation U) I hdis hcover,
      spectralJointEntry_tree, tensorFieldPairObservable, spinPairOverlap,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [treeOverlap, depthTail_level, finiteFieldPath_single]

lemma spectralSpinDepthTail_weak_limit {m n : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q)) (j : ℕ) :
    Tendsto (fun k => ∫ x, spectralSpinDepthTail n j x ∂(L k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1))))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_spectralSpinDepthTail n j⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorLeafTail
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
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


lemma tensorGaussian_replicaMean_namespace {N m k r : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (T : LabeledTree n) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (D : (Fin r → Spin N × LabeledLeaf n) → ℝ) :
    (∫ z, referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorLeafCoefficients U I degree amp n v x) z) D ∂gaussianCoordinates) =
    (∫ z, referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
        cylinderField (tensorNamespacedCoefficients U I degree amp n v x) z) D ∂gaussianCoordinates) := by
  let ν := labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) T
  let H := fun x : Spin N × LabeledLeaf n => rotatedEnergy eig U x.1 + fieldEnergy c x.1
  let F := fun f : Spin N × LabeledLeaf n → ℝ => referenceReplicaMean ν (fun x => H x + f x) D
  have hν : Measurable (fun _ : (Spin N × LabeledLeaf n → ℝ) => ν) := measurable_const
  have : ∀ f : (Spin N × LabeledLeaf n → ℝ), IsProbabilityMeasure ((fun _ => ν) f) :=
    fun _ => inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) T))
  have hH : Measurable (fun p : (Spin N × LabeledLeaf n → ℝ) × (Spin N × LabeledLeaf n) =>
      H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (show Measurable (fun _ : (Spin N × LabeledLeaf n → ℝ) => H x) from
      measurable_const).add (measurable_pi_apply x)
  have hF : Measurable F := measurable_random_referenceReplicaMean hν hH
    ((measurable_of_countable D).comp measurable_snd)
  have hleft : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp n v x) z) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hright : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp n v x) z) :=
    Measurable.of_eval (fun _ => measurable_cylinderField _)
  have hL := integral_map (μ := gaussianCoordinates) hleft.aemeasurable hF.aestronglyMeasurable
  have hR := integral_map (μ := gaussianCoordinates) hright.aemeasurable hF.aestronglyMeasurable
  rw [tensorNamespacedFields_law] at hL
  exact hL.symm.trans hR


lemma measurable_tensorFlat_replicaMean {N m k r : ℕ}
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0)
    (D : (Fin r → Spin N × LabeledLeaf n) → ℝ) :
    Measurable (fun p : LabeledTree n × (ℕ → ℝ) =>
      referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
        (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
          cylinderField (tensorLeafCoefficients U I degree amp n v x) p.2) D) := by
  let ν : LabeledTree n × (ℕ → ℝ) → Measure (Spin N × LabeledLeaf n) := fun p =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1
  let H : (LabeledTree n × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) → ℝ := fun p =>
    rotatedEnergy eig U p.2.1 + fieldEnergy c p.2.1 +
      cylinderField (tensorLeafCoefficients U I degree amp n v p.2) p.1.2
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) p.1))
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst
  have hH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro x
    change Measurable (fun p : LabeledTree n × (ℕ → ℝ) =>
      (rotatedEnergy eig U x.1 + fieldEnergy c x.1) +
        cylinderField (tensorLeafCoefficients U I degree amp n v x) p.2)
    exact (show Measurable (fun _ : LabeledTree n × (ℕ → ℝ) =>
      rotatedEnergy eig U x.1 + fieldEnergy c x.1) from
      measurable_const).add ((measurable_cylinderField
        (tensorLeafCoefficients U I degree amp n v x)).comp measurable_snd)
  have hD : Measurable (fun p : (LabeledTree n × (ℕ → ℝ)) ×
      (Fin r → Spin N × LabeledLeaf n) => D p.2) :=
    (measurable_of_countable D).comp measurable_snd
  exact measurable_random_referenceReplicaMean hν hH hD


lemma tensorNamespacedReplicaAverage_leafPrefix {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hb : CascadeExponents n b) (hh : Monotone h) (h0 : 0 ≤ h 0) (d : Fin n) :
    tensorNamespacedReplicaAverage μ eig c I degree amp n b r h
      (fun _ => tensorLeafPrefixTest d) = 1 - b d := by
  let D := tensorLeafPrefixTest (N := N) d
  let ν := fun p : TensorFlatDisorder N n =>
    labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let F := fun p : TensorFlatDisorder N n => referenceReplicaMean (ν p)
    (tensorNamespacedHamiltonian eig c I degree amp n r h p) D
  have : ∀ p, IsProbabilityMeasure (ν p) := fun p =>
    inferInstanceAs (IsProbabilityMeasure (labeledSpinReference n
      (uniformSpinPrior N : Measure (Spin N)) p.1.2))
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n (uniformSpinPrior N : Measure (Spin N))).comp
      measurable_fst.snd
  have hF : Measurable F := measurable_random_referenceReplicaMean hν
    (measurable_tensorNamespacedHamiltonian eig c I degree amp n r h)
    ((measurable_of_countable D).comp measurable_snd)
  have hFb p : |F p| ≤ 1 := referenceReplicaMean_abs_le _ _ _
    (measurable_of_countable D) zero_le_one (tensorLeafPrefixTest_abs_le d)
  have hFi : Integrable F ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
      gaussianCoordinates) := integrable_of_measurable_abs_le hF hFb
  calc
    _ = ∫ p, F p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
        gaussianCoordinates := by
      unfold tensorNamespacedReplicaAverage
      apply integral_congr_ae
      filter_upwards [tensorNamespaced_exp_integrable_ae μ eig c I degree amp n b r h hh h0]
        with p hp
      exact referenceReplicaMean_gibbsProbability (ν p)
        (tensorNamespacedHamiltonian eig c I degree amp n r h p) hp D
    _ = ∫ p, ∫ z, F (p,z) ∂gaussianCoordinates
        ∂μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n)) := integral_prod _ hFi
    _ = ∫ U, ∫ T, ∫ z, F ((U,T),z) ∂gaussianCoordinates
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) ∂μ :=
      integral_prod _ hFi.integral_prod_left
    _ = ∫ _U, 1 - b d ∂μ := by
      apply integral_congr_ae
      refine ae_of_all _ fun U => ?_
      let v := tensorPathProfile I degree n r h
      let G := fun p : LabeledTree n × (ℕ → ℝ) =>
        referenceReplicaMean (labeledSpinReference n (uniformSpinPrior N : Measure (Spin N)) p.1)
          (fun x => rotatedEnergy eig (specialRotation U) x.1 + fieldEnergy c x.1 +
            cylinderField (tensorLeafCoefficients (specialRotation U) I degree amp n (fun i => v i) x) p.2) D
      have hG : Measurable G := measurable_tensorFlat_replicaMean eig
        (specialRotation U) c I degree amp n (fun i => v i) D
      have hGi : Integrable G ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
          gaussianCoordinates) := integrable_of_measurable_abs_le hG (fun _ =>
        referenceReplicaMean_abs_le _ _ D (measurable_of_countable D) zero_le_one
          (tensorLeafPrefixTest_abs_le d))
      calc
        _ = ∫ T, ∫ z, G (T,z) ∂gaussianCoordinates
            ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
          apply integral_congr_ae
          refine ae_of_all _ fun T => ?_
          exact (tensorGaussian_replicaMean_namespace eig (specialRotation U) c I degree amp
            n T (fun i => v i) D).symm
        _ = ∫ p, G p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates :=
          (integral_prod _ hGi).symm
        _ = 1 - b d := tensorFlat_leafPrefix_mean hN eig (specialRotation U) c I degree amp n b v hb d
    _ = _ := by simp only [integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorTreeLevels
attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.spinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_apply _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_apply _root_.OAI.InvariantIsing.cavitySpinSplit_left _root_.OAI.InvariantIsing.cavitySpinSplit_right _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tree coordinate of the actual tensor array remains on its finite
cascade levels after passage to a weak limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma spectralArrayLaw_treeLevels {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (n : ℕ)
    (ν : Ω → Measure (Spin N × LabeledLeaf n)) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (i j : ℕ) :
    ∀ᵐ x ∂(spectralArrayLaw P U hU I n ν hν : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  change ∀ᵐ x ∂(disorderReplicaLaw P ν hν).map (spectralReplicaArray U I n),
    (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n
  rw [ae_map_iff (measurable_spectralReplicaArray U hU I n).aemeasurable
    ((isClosed_treeLevels n).measurableSet.preimage (by fun_prop))]
  apply ae_of_all
  intro p
  simpa only [spectralReplicaArray, spectralJointEntry_tree] using
    treeOverlap_mem_levels n (p.2 i).2 (p.2 j).2

lemma tensorPerturbedArrayLaw_treeLevels {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (n : ℕ) (b h : ℕ → ℝ) (i j : ℕ) :
    ∀ᵐ x ∂(tensorPerturbedArrayLaw μ eig c I u v t n b h : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  unfold tensorPerturbedArrayLaw tensorNamespacedArrayLaw
  exact spectralArrayLaw_treeLevels _ _ _ _ _ _ _ i j

lemma tensorPerturbedArrayLaw_limit_treeLevels (N : ℕ → ℕ) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) (i j : ℕ) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (i,j) (Fin.last m) : ℝ) ∈ treeLevels n := by
  exact ae_closed_of_weak_limit hL ((isClosed_treeLevels n).preimage (by fun_prop))
    (fun k => tensorPerturbedArrayLaw_treeLevels (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k) i j)


lemma tensorNamespacedArrayLaw_treeTail {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hb : CascadeExponents n b) (hh : Monotone h) (h0 : 0 ≤ h 0) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(tensorNamespacedArrayLaw μ eig c I degree amp n b r h : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have he := tensorNamespacedArrayLaw_test μ eig c I degree amp n b r h
    (fun x => treeTail n d (x (0,1) (Fin.last m) : ℝ))
    ((continuous_treeTail n d).comp (by fun_prop))
    (fun _ => tensorLeafPrefixTest (N := N) d) ![1,0]
    (by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
    (by
      intro U σ
      simp only [spectralJointEntry_tree, tensorLeafPrefixTest,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact treeTail_overlap n d (σ 0).2 (σ 1).2)
  rw [he]
  exact tensorNamespacedReplicaAverage_leafPrefix hN μ eig c I degree amp n b r h hb hh h0 d

lemma tensorPerturbedArrayLaw_limit_treeTail (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (u : (k : ℕ) → Fin (N k) → ℝ) (v : ℕ → Fin m → ℝ) (t : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : CascadeExponents n b) (h : ℕ → ℕ → ℝ)
    (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (u k) (v k) (t k) n b (h k)) atTop (𝓝 Q)) (d : Fin n) :
    (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - b d := by
  have hi := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => treeTail n d (x (0,1) (Fin.last m) : ℝ),
        (continuous_treeTail n d).comp (by fun_prop)⟩)
  have he k := tensorNamespacedArrayLaw_treeTail (hN k) (μ k)
    (diagonalPerturbedEigenvalues (eig k) (I k) (v k) (t k)) (c k) (I k)
    (fun j => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude (N k) (u k))
    n b (fun j => enumeratedTreeDegree m j) (h k) hb (hh k) (h0 k) d
  have hconst : Tendsto (fun k => ∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k) (u k) (v k) (t k) n b (h k) :
        Measure (SpectralArray (m + 1)))) atTop (𝓝 (1 - b d)) := by
    simpa only [tensorPerturbedArrayLaw, he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - b d) atTop (𝓝 (1 - b d)))
  exact tendsto_nhds_unique hi hconst

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteTailOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact inequalities at trial-partition endpoints imply the full upper
 tail order. Monotone quantile tails lie above their interval chords. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma pathTail_chord (p : OverlapPath) {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    (b - s) * pathTail p a + (s - a) * pathTail p b ≤ (b - a) * pathTail p s := by
  have hleft : (∫ u in a..s, p u) ≤ ∫ _u in a..s, p s :=
    intervalIntegral.integral_mono_on has p.monotone.intervalIntegrable
    intervalIntegrable_const (fun u hu => p.monotone hu.2)
  have hright : (∫ _u in s..b, p s) ≤ ∫ u in s..b, p u :=
    intervalIntegral.integral_mono_on hsb intervalIntegrable_const
    p.monotone.intervalIntegrable (fun u hu => p.monotone hu.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hleft hright
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (p.monotone.intervalIntegrable (μ := volume) (a := a) (b := s))
    (p.monotone.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (p.monotone.intervalIntegrable (μ := volume) (a := s) (b := b))
    (p.monotone.intervalIntegrable (μ := volume) (a := b) (b := 1))
  have hL := mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hsb)
  have hR := mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr has)
  unfold pathTail
  nlinarith

lemma pathTail_chord_eq_of_const (q : OverlapPath) {a s b c : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) (hc : ∀ u ∈ Ioo a b, q u = c) :
    (b - s) * pathTail q a + (s - a) * pathTail q b = (b - a) * pathTail q s := by
  have hleft : (∫ u in a..s, q u) = (s - a) * c := by
    calc
      _ = ∫ _u in a..s, c := intervalIntegral.integral_congr_Ioo_of_le has
        (fun u hu => hc u ⟨hu.1, hu.2.trans_le hsb⟩)
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hright : (∫ u in s..b, q u) = (b - s) * c := by
    calc
      _ = ∫ _u in s..b, c := intervalIntegral.integral_congr_Ioo_of_le hsb
        (fun u hu => hc u ⟨has.trans_lt hu.1, hu.2⟩)
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (q.monotone.intervalIntegrable (μ := volume) (a := a) (b := s))
    (q.monotone.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (q.monotone.intervalIntegrable (μ := volume) (a := s) (b := b))
    (q.monotone.intervalIntegrable (μ := volume) (a := b) (b := 1))
  rw [hleft] at h1
  rw [hright] at h2
  unfold pathTail
  nlinarith

lemma pathTail_le_of_interval_endpoints (p q : OverlapPath) {a s b c : ℝ}
    (hab : a < b) (has : a ≤ s) (hsb : s ≤ b) (hc : ∀ u ∈ Ioo a b, q u = c)
    (ha : pathTail q a ≤ pathTail p a) (hb : pathTail q b ≤ pathTail p b) :
    pathTail q s ≤ pathTail p s := by
  have hp := pathTail_chord p has hsb
  have hq := pathTail_chord_eq_of_const q has hsb hc
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hsb)
  have h2 := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr has)
  nlinarith

lemma finite_cut_bracket {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 1), cut i.castSucc ≤ s ∧ s ≤ cut i.succ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (n + 1) => cut i.castSucc ≤ s)
  have hS : S.Nonempty := ⟨0, by simp only [S, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.castSucc_zero, hfirst]; exact hs.1⟩
  let i := S.max' hS
  have hiS : i ∈ S := Finset.max'_mem _ _
  have hi : cut i.castSucc ≤ s := (Finset.mem_filter.mp hiS).2
  refine ⟨i, hi, ?_⟩
  by_cases hin : i.val = n
  · have he : i.succ = Fin.last (n + 1) := by ext; simp only [Fin.val_succ, Fin.val_last]; omega
    rw [he, hlast]
    exact hs.2
  · by_contra hsb
    let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have he : j.castSucc = i.succ := by ext; rfl
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [he]; exact (lt_of_not_ge hsb).le⟩
    have hji : j ≤ i := Finset.le_max' S j hjS
    change j.val ≤ i.val at hji
    dsimp only [j] at hji
    omega

 theorem pathTail_order_of_finite_partition (p q : OverlapPath) {n : ℕ}
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (v : Fin (n + 1) → ℝ)
    (hq : ∀ i u, u ∈ Ioo (cut i.castSucc) (cut i.succ) → q u = v i)
    (hend : ∀ i, pathTail q (cut i) ≤ pathTail p (cut i)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s := by
  intro s hs
  obtain ⟨i, has, hsb⟩ := finite_cut_bracket cut hfirst hlast hs
  exact pathTail_le_of_interval_endpoints p q
    (hcut (by exact_mod_cast (show i.val < i.val + 1 by omega))) has hsb (hq i)
    (hend i.castSucc) (hend i.succ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralContactTails
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Synchronized field-contact tests include the root and identify every
partition-endpoint tail without excluding atoms at those endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralSpin_integral {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    (∫ x, spectralSpinArray x 0 1 ∂(Q : Measure (SpectralArray (m + 1)))) =
      pathTail (spectralSpinQuantilePath Q hP hn) 0 := by
  have hm : Measurable (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) := by
    unfold spectralSpinArray
    fun_prop
  have he := integral_map hm.aemeasurable
    (measurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun x : ℝ => x)
      (scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray))
  change (∫ x : ℝ, x ∂scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray) = _ at he
  rw [← spectralSpinQuantilePath_law Q hP hn,
    integral_map (μ := pathMeasure) (f := fun x : ℝ => x)
      (spectralSpinQuantilePath Q hP hn).measurable.aemeasurable
      measurable_id.aestronglyMeasurable] at he
  simp only [id_eq] at he
  rw [← he, pathTail, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  rfl

lemma spectralPair_depthTail_integral {m n : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (hlevel : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) (Fin.last m) : ℝ) ∈ treeLevels n)
    (cut : Fin (n + 2) → ℝ) (hfirst : cut 0 = 0)
    (hb : ∀ i, cut i ∈ Icc (0 : ℝ) 1)
    (htail : ∀ d : Fin n, (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - cut d.succ.castSucc)
    (j : Fin (n + 1)) :
    (∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1)))) =
      pathTail (spectralSpinQuantilePath Q hP hn) (cut j.castSucc) := by
  refine Fin.cases ?_ (fun d => ?_) j
  · simpa only [Fin.val_zero, Fin.castSucc_zero, hfirst, spectralSpinDepthTail,
      depthTail, ite_true, if_true, mul_one] using spectralSpin_integral Q hP hn
  · simpa only [spectralSpinDepthTail, Fin.val_succ, depthTail,
      Nat.succ_ne_zero, ite_false, if_false, Nat.add_sub_cancel] using
      spectralPair_treeTail_integral Q hgg hG q hq hd hE hP hn hlevel
        (hb d.succ.castSucc) (htail d)

lemma contact_partition_tail_order {n : ℕ} (p trial : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (v : Fin (n + 1) → ℝ)
    (hv : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = v i)
    (hcontact : ∀ j : Fin (n + 1),
      (∑ i, ((cut i.succ - cut i.castSucc) * v i) *
        finiteFieldPath (Pi.single j 1) i) ≤ pathTail p (cut j.castSucc)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail p s := by
  apply pathTail_order_of_finite_partition p trial cut hc hfirst hlast v hv
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [hlast, pathTail, intervalIntegral.integral_same, le_refl]
  · have he : (∫ s in Ioi (cut i.castSucc), trial s ∂pathMeasure) =
        ∑ k, if i.val ≤ k.val then (cut k.succ - cut k.castSucc) * v k else 0 := by
      have hstep : finiteStepFunction cut v =ᵐ[pathMeasure] trial := by
        let : NullSingletonClass pathMeasure := by unfold pathMeasure; infer_instance
        have hne : ∀ᵐ s ∂pathMeasure, ∀ k, s ≠ cut k :=
          ae_all_iff.mpr (fun k => Measure.ae_ne pathMeasure (cut k))
        filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with s hs hns
        obtain ⟨k, hlo, hhi⟩ := finite_partition_cell cut
          (by simpa only [hfirst] using hs.1.le)
          (by simpa only [hlast] using hs.2)
        have hk : s ∈ Ioo (cut k.castSucc) (cut k.succ) :=
          ⟨lt_of_le_of_ne hlo (hns k.castSucc).symm, hhi⟩
        rw [finiteStepFunction_on_cell hc v hk]
        exact (hv k s hk).symm
      rw [← integral_congr_ae hstep.restrict]
      have ht := integral_finiteStep_tail cut hc hfirst hlast v i.castSucc
      change (∫ s in Ioi (cut i.castSucc), finiteStepFunction cut v s ∂pathMeasure) = _ at ht
      simpa only [Fin.le_def, Fin.val_castSucc] using ht
    have hb : cut i.castSucc ∈ Icc (0 : ℝ) 1 :=
      ⟨by rw [← hfirst]; exact hc.monotone (Fin.zero_le _),
       by rw [← hlast]; exact hc.monotone (Fin.le_last _)⟩
    rw [integral_pathMeasure_Ioi trial hb] at he
    rw [he]
    simpa only [finiteFieldPath_single, mul_ite, mul_one, mul_zero] using hcontact i

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_TensorContactTailOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual joint minima enforce upper-tail order at their synchronized
GG limit. All finite field directions are taken at those same minima. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem tensorContact_limit_tail_order_oai
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m n : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (eig c : (k : ℕ) → Fin (N k) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (cut : Fin (n + 2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (trial : OverlapPath) (values : Fin (n + 1) → ℝ)
    (hvalues : ∀ i s, s ∈ Ioo (cut i.castSucc) (cut i.succ) → trial s = values i)
    (S : ℝ) (V : ℝ → ℝ) (H : ℝ)
    (p : (k : ℕ) → TensorContactParameter (N k) m n)
    (hp : ∀ k, p k ∈ tensorContactRegion (N k) m n H)
    (hmin : ∀ k q, q ∈ tensorContactRegion (N k) m n H →
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V (p k) ≤
      tensorContactObjective (μ k) (eig k) (c k) (I k) (chainExponent cut)
        (fun i => (cut i.succ - cut i.castSucc) * values i) S V q)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hL : Tendsto (fun k => tensorPerturbedArrayLaw (μ k) (eig k) (c k) (I k)
      (p k).2.2.1 (p k).2.2.2 (p k).1 n (chainExponent cut) (finiteFieldPath (p k).2.1))
      atTop (𝓝 Q))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail trial s ≤ pathTail (spectralSpinQuantilePath Q hP hn) s := by
  classical
  have hb := chainExponent_admissible hc hfirst hlast
  have hh k := monotone_finiteFieldPath (tensorContactRegion_bounds (hp k)).2.1
  have h0 k := finiteFieldPath_nonneg (tensorContactRegion_bounds (hp k)).2.1 0
  have hgeom := tensorPerturbedArrayLaw_limit_geometry N m n μ eig c I
    (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
    (chainExponent cut) (fun k => finiteFieldPath (p k).2.1) Q hL
  have hlevels := tensorPerturbedArrayLaw_limit_treeLevels N m n μ eig c I
    (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
    (chainExponent cut) (fun k => finiteFieldPath (p k).2.1) Q hL 0 1
  have htails (d : Fin n) :
      (∫ x, treeTail n d (x (0,1) (Fin.last m) : ℝ)
        ∂(Q : Measure (SpectralArray (m + 1)))) = 1 - cut d.succ.castSucc := by
    have he := tensorPerturbedArrayLaw_limit_treeTail N hN m n μ eig c I
      (fun k => (p k).2.2.1) (fun k => (p k).2.2.2) (fun k => (p k).1)
      (chainExponent cut) hb (fun k => finiteFieldPath (p k).2.1) hh h0 Q hL d
    rw [chainExponent_apply cut d.isLt] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (fun a => 1 - cut a)
    exact Fin.ext rfl
  have hcut (j) : cut j ∈ Icc (0 : ℝ) 1 :=
    ⟨by rw [← hfirst]; exact hc.monotone (Fin.zero_le _),
     by rw [← hlast]; exact hc.monotone (Fin.le_last _)⟩
  apply contact_partition_tail_order _ trial cut hc hfirst hlast values hvalues
  intro j
  have hlim := spectralSpinDepthTail_weak_limit hL (n := n) j
  have hineq : (∑ i, ((cut i.succ - cut i.castSucc) * values i) *
      finiteFieldPath (Pi.single j 1) i) ≤
      ∫ x, spectralSpinDepthTail n j x ∂(Q : Measure (SpectralArray (m + 1))) := by
    apply ge_of_tendsto' hlim
    intro k
    have he := tensorNamespacedArrayLaw_field_tail (μ k)
      (diagonalPerturbedEigenvalues (eig k) (I k) (p k).2.2.2 (p k).1) (c k) (I k)
      (hdis k) (hcover k) (fun r => enumeratedSpectralDegree m r)
      (tensorPerturbationAmplitude (N k) (p k).2.2.1) (chainExponent cut)
      (finiteFieldPath (p k).2.1) (fun r => enumeratedTreeDegree m r) j
    have hcdir := tensorContact_minimum_field_cone (hN k) (μ k) (eig k) (c k) (I k)
      (chainExponent cut) (fun i => (cut i.succ - cut i.castSucc) * values i)
      S V H (p k) (hp k) (hmin k) (hcap k) (Pi.single j 1)
      (fun i => by simp only [Pi.single_apply]; split_ifs <;> norm_num)
    exact hcdir.trans_eq he.symm
  rwa [spectralPair_depthTail_integral Q hgg hgeom.1 q hq hd
    (fun e => hgeom.2 e e.injective) hP hn hlevels cut hfirst hcut htails j] at hineq

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.tensorContact_limit_tail_order_oai := @OAI.InvariantIsing.tensorContact_limit_tail_order_oai
