-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:37:52.932113+00:00
-- url     : https://prove2.me/submissions/c507e8ce-733b-4e6e-996b-9ddba240189f

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_compactGG_freshLog_control
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_expectedPressure_lower_smooth
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceCountExpectedLog_fresh
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceNegativeContact_field_interior
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceNegativeContact_positive_density
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_monomial_tendsto
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_control_order_along
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_density
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_exists
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_zeroField_original_compare

section
-- module Solutions.OAIQ061_PF.Compat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CountableGaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma gaussianCoordinatePrefix_measurePreserving (n : ℕ) :
    MeasurePreserving (gaussianCoordinatePrefix n) countableGaussianLaw
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  refine ⟨by unfold gaussianCoordinatePrefix; fun_prop,?_⟩
  change Measure.map (fun g : ℕ → ℝ => fun i : Fin n => g i.val)
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)=_
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

variable {S : Type*}

lemma finiteGaussian_exp_integrable (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    Integrable (fun g : Fin n → ℝ => Real.exp (t*∑ i, g i*a i))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := Integrable.fintype_prod (fun i : Fin n =>
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t*a i))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext g
  rw [Finset.mul_sum,Real.exp_sum]
  congr 1
  ext i
  congr 1
  ring

lemma finiteGaussian_exp_integral (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (∫ g : Fin n → ℝ, Real.exp (t*∑ i, g i*a i)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      Real.exp (t^2*(∑ i, a i^2)/2) := by
  have he : (fun g : Fin n → ℝ => Real.exp (t*∑ i, g i*a i))=
      fun g => ∏ i, Real.exp ((t*a i)*g i) := by
    funext g
    rw [Finset.mul_sum,Real.exp_sum]
    congr 1
    ext i
    congr 1
    ring
  rw [he,integral_fintype_prod_eq_prod (fun i : Fin n => fun x => Real.exp ((t*a i)*x))]
  have hi (i : Fin n) : (∫ x, Real.exp ((t*a i)*x) ∂gaussianReal 0 1)=
      Real.exp ((t*a i)^2/2) := by
    have hh := mgf_gaussianReal (X := fun x : ℝ => x) (p := gaussianReal 0 1)
      (μ := 0) (v := 1) (by simp) (t*a i)
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using hh
  simp_rw [hi]
  rw [← Real.exp_sum,Finset.mul_sum,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gaussianPrefixField_exp_integrable (v : ℕ → S → ℝ) (n : ℕ) (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*gaussianPrefixField v n g x)) countableGaussianLaw := by
  exact (gaussianCoordinatePrefix_measurePreserving n).integrable_comp_of_integrable
    (finiteGaussian_exp_integrable n (fun i => v i.val x) t)

lemma gaussianPrefixField_exp_integral (v : ℕ → S → ℝ) (n : ℕ) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*gaussianPrefixField v n g x) ∂countableGaussianLaw)=
      Real.exp (t^2*(∑ i : Fin n, v i.val x^2)/2) := by
  rw [← finiteGaussian_exp_integral n (fun i => v i.val x) t]
  have hm := gaussianCoordinatePrefix_measurePreserving n
  conv_rhs => rw [← hm.map_eq]
  rw [integral_map hm.measurable.aemeasurable (by
    rw [hm.map_eq]
    exact (finiteGaussian_exp_integrable n (fun i => v i.val x) t).aestronglyMeasurable)]
  rfl

lemma countableGaussianField_exp_integrable (v : ℕ → S → ℝ) (L : S → ℕ) (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*countableGaussianField v L g x)) countableGaussianLaw :=
  gaussianPrefixField_exp_integrable v (L x) x t

lemma countableGaussianField_exp_integral (v : ℕ → S → ℝ) (L : S → ℕ) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianField v L g x) ∂countableGaussianLaw)=
      Real.exp (t^2*(∑ i : Fin (L x), v i.val x^2)/2) :=
  gaussianPrefixField_exp_integral v (L x) x t

lemma sum_range_cutoff (a : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range n, if i < m then a i else 0)=∑ i ∈ Finset.range (min n m), a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      by_cases h : n < m
      · have hn : min n m=n := min_eq_left (by omega)
        have hn' : min (n+1) m=n+1 := min_eq_left (by omega)
        rw [hn,hn',ite_eq_left h,Finset.sum_range_succ]
      · have hn : min n m=m := min_eq_right (by omega)
        have hn' : min (n+1) m=m := min_eq_right (by omega)
        rw [hn,hn',ite_eq_right h,add_zero]

lemma countableGaussianField_exp_integral_le (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianField v L g x) ∂countableGaussianLaw) ≤
      Real.exp (t^2*D/2) := by
  rw [countableGaussianField_exp_integral]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hD x) (sq_nonneg t)) (by norm_num))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianFieldAlgebra
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*}

lemma countableGaussianField_add (v w : ℕ → S → ℝ) (L : S → ℕ) (g : ℕ → ℝ) (x : S) :
    countableGaussianField (fun i x => v i x+w i x) L g x =
      countableGaussianField v L g x+countableGaussianField w L g x := by
  simp only [countableGaussianField,gaussianPrefixField,mul_add,Finset.sum_add_distrib]

lemma countableGaussianField_smul (a : ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (x : S) :
    countableGaussianField (fun i x => a*v i x) L g x = a*countableGaussianField v L g x := by
  simp only [countableGaussianField,gaussianPrefixField,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gaussianTailCoefficient_sq_le (w : ℕ → S → ℝ) (n i : ℕ) (x : S) :
    gaussianTailCoefficient w n i x^2 ≤ w i x^2 := by
  unfold gaussianTailCoefficient
  split_ifs <;> simp [sq_nonneg]

lemma gaussianCombinedCoefficient_sq_bound (v w : ℕ → S → ℝ) (L : S → ℕ)
    {D E : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (a b : ℝ) (n : ℕ) (x : S) :
    (∑ i : Fin (L x), (a*v i.val x+b*gaussianTailCoefficient w n i.val x)^2) ≤
      2*a^2*D+2*b^2*E := by
  calc
    _ ≤ ∑ i : Fin (L x), (2*a^2*v i.val x^2+2*b^2*w i.val x^2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := gaussianTailCoefficient_sq_le w n i.val x
      have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*b^2)
      nlinarith [sq_nonneg (a*v i.val x-b*gaussianTailCoefficient w n i.val x)]
    _ = 2*a^2*(∑ i : Fin (L x), v i.val x^2)+
        2*b^2*(∑ i : Fin (L x), w i.val x^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hD x) (by positivity))
      (mul_le_mul_of_nonneg_left (hE x) (by positivity))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

end Tilt

lemma replicaPotential_measurable {S : Type*} [MeasurableSpace S]
    {v : S → ℝ} (hv : Measurable v) (n : ℕ) : Measurable (replicaPotential v n) := by
  exact Finset.measurable_sum _ fun i _ => hv.comp (measurable_pi_apply i)

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.instNullSingletonClassElemRealTimeTimeLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

lemma gaussianReplicaTest_apply {ι : Type*} [Fintype ι] (f : ℝ →ᵇ ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianReplicaTest f z = ∏ i, f (z i) := by simp [gaussianReplicaTest]

open TopologicalSpace

lemma compact_array_law_subsequence {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [CompactSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ℕ → ProbabilityMeasure (CompactArray K)) :
    ∃ ν : ProbabilityMeasure (CompactArray K), ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  obtain ⟨ν, -, s, hs, hμ⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  exact ⟨ν,s,hs,hμ⟩

lemma weak_limit_closed_full {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [HasOuterApproxClosed K]
    {μ : ℕ → ProbabilityMeasure K} {ν : ProbabilityMeasure K}
    (hμ : Tendsto μ atTop (𝓝 ν)) {F : Set K} (hF : IsClosed F)
    (hfull : ∀ n, μ n F = 1) : ν F = 1 := by
  apply le_antisymm (ProbabilityMeasure.apply_le_one _ _)
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hF
  have hf (n : ℕ) : (μ n : Measure K) F = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hfull n,ENNReal.coe_one]
  simp only [hf,limsup_const] at h
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at h
  exact_mod_cast h

lemma compactGGDefect_continuous {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray K) => compactGGDefect μ n i f g) := by
  let f' : CompactArray K →ᵇ ℝ := f.compContinuous ⟨compactBlock n,compactBlock_continuous n⟩
  let g' (i j : ℕ) : CompactArray K →ᵇ ℝ := g.compContinuous ⟨fun Q => Q i j,by fun_prop⟩
  have hf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f'
  have hg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (g' i j)
  have hfg (i j : ℕ) := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f' * g' i j)
  exact (continuous_const.mul (hfg i n) |>.sub (hf.mul (hg 0 1))).sub
    (continuous_finsetSum _ fun j _ => hfg i j)

lemma compactGGDefect_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K] {μ : ℕ → ProbabilityMeasure (CompactArray K)}
    {ν : ProbabilityMeasure (CompactArray K)} (hμ : Tendsto μ atTop (𝓝 ν))
    (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ)
    (hdef : Tendsto (fun k => compactGGDefect (μ k) n i f g) atTop (𝓝 0)) :
    compactGGDefect ν n i f g = 0 :=
  tendsto_nhds_unique ((compactGGDefect_continuous n i f g).continuousAt.tendsto.comp hμ) hdef

lemma compactGG_joint_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) {n : ℕ} (hn : 0 < n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ), compactGGDefect μ n i f g = 0) :
    (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i n)) =
      ((n : ℝ≥0)⁻¹) •
        (((μ : Measure (CompactArray K)).map (compactBlock n)).prod
            ((μ : Measure (CompactArray K)).map (fun Q => Q 0 1)) +
          ∑ j ∈ Finset.univ.erase i,
            (μ : Measure (CompactArray K)).map (fun Q => (compactBlock n Q, Q i j))) := by
  classical
  have hb := (compactBlock_continuous (K := K) n).measurable
  have he (k l : ℕ) : Measurable (fun Q : CompactArray K => Q k l) := by fun_prop
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : (CompactBlock K n × K) →ᵇ ℝ :=
    (f.compContinuous ⟨Prod.fst,continuous_fst⟩) * (g.compContinuous ⟨Prod.snd,continuous_snd⟩)
  have hF : ∀ ρ : Measure (CompactBlock K n × K), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ hρ
    exact F.integrable ρ
  change ∫ p, F p ∂_ = ∫ p, F p ∂_
  rw [integral_smul_nnreal_measure,integral_add_measure (hF _ inferInstance) (hF _ inferInstance),
    integral_finsetSum_measure]
  · simp_rw [integral_map (hb.prodMk (he _ _)).aemeasurable F.continuous.aestronglyMeasurable]
    simp only [F,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,NNReal.smul_def,NNReal.coe_inv,NNReal.coe_natCast,smul_eq_mul]
    rw [integral_prod_mul,integral_map hb.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map (he 0 1).aemeasurable g.continuous.aestronglyMeasurable]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := hGG f g
    unfold compactGGDefect at h
    apply (mul_right_inj' hn').mp
    rw [←mul_assoc,mul_inv_cancel₀ hn',one_mul]
    linarith [h]
  · intro j hj
    exact hF _ inferInstance

open scoped Polynomial

lemma integral_continuous_tendsto_of_moments {a b : ℝ}
    (μ : ℕ → Measure (Icc a b)) (ν : Measure (Icc a b))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, (x.val)^k ∂μ n) atTop
      (𝓝 (∫ x, (x.val)^k ∂ν))) (f : C(Icc a b, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hi (ρ : Measure (Icc a b)) [IsFiniteMeasure ρ] (p : ℝ[X]) :
      Integrable (fun x : Icc a b => p.eval x.val) ρ :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : ℝ[X]) : Tendsto (fun n => ∫ x, p.eval x.val ∂μ n) atTop
      (𝓝 (∫ x, p.eval x.val ∂ν)) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add,integral_add (hi _ p) (hi _ q)] using hp.add hq
    | monomial k c =>
      simpa only [Polynomial.eval_monomial,integral_const_mul] using tendsto_const_nhds.mul (h k)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hpε⟩ := exists_polynomial_near_continuousMap a b f (ε/3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hp p)) (ε/3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbnd (ρ : Measure (Icc a b)) [IsProbabilityMeasure ρ] :
      |(∫ x, p.eval x.val ∂ρ) - ∫ x, f x ∂ρ| < ε/3 := by
    rw [← integral_sub (hi ρ p) (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    · calc
        |∫ x, p.eval x.val - f x ∂ρ| ≤ ‖p.toContinuousMapOn (Icc a b)-f‖ := by
          simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs,ContinuousMap.sub_apply,Polynomial.toContinuousMapOn_apply,Polynomial.toContinuousMap_apply] using
            (norm_integral_le_of_norm_le_const (μ := ρ)
              (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm
                (p.toContinuousMapOn (Icc a b)-f) x))
        _ < ε/3 := hpε
  have h₁ := hbnd (μ n)
  have h₂ := hbnd ν
  have h₃ := hN n hn
  rw [Real.dist_eq] at h₃ ⊢
  calc
    |(∫ x, f x ∂μ n) - ∫ x, f x ∂ν| ≤
        |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
        |(∫ x, p.eval x.val ∂μ n) - ∫ x, p.eval x.val ∂ν| +
        |(∫ x, p.eval x.val ∂ν) - ∫ x, f x ∂ν| := by
          calc
            _ ≤ |(∫ x, f x ∂μ n) - ∫ x, p.eval x.val ∂μ n| +
                |(∫ x, p.eval x.val ∂μ n) - ∫ x, f x ∂ν| := abs_sub_le _ _ _
            _ ≤ _ := by
              linarith [abs_sub_le (∫ x, p.eval x.val ∂μ n)
                (∫ x, p.eval x.val ∂ν) (∫ x, f x ∂ν)]
    _ < ε := by rw [abs_sub_comm (∫ x, f x ∂μ n)] ; linarith

lemma trial_integrable (m : Trial) : Integrable m timeLaw := by
  change Integrable m (volume : Measure Time)
  apply (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (m.nonneg t)]
    exact m.le_one t

lemma tailIntegral_mono {m n : Trial} (h : ∀ t, m t ≤ n t) (t : Time) :
    tailIntegral m t ≤ tailIntegral n t :=
  integral_mono (trial_integrable m).integrableOn (trial_integrable n).integrableOn h

lemma entropy_antitone {m n : Trial} (h : ∀ t, m t ≤ n t) : entropy n ≤ entropy m := by
  apply ENNReal.div_le_div_right
  apply lintegral_mono
  intro t
  exact tsub_le_tsub_right (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (tailIntegral_mono h t))) _

lemma le_upperRoundedTrial (m : Trial) (n : ℕ) (t : Time) : m t ≤ upperRoundedTrial m n t := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  simpa only [mul_comm] using (Nat.le_ceil (((n+1 : ℕ) : ℝ)*m t))

lemma upperRoundedTrial_sub_le (m : Trial) (n : ℕ) (t : Time) :
    upperRoundedTrial m n t - m t ≤ 1/((n+1 : ℕ) : ℝ) := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ)*m t from mul_nonneg (by positivity) (m.nonneg t))
  change (⌈((n+1 : ℕ) : ℝ)*m t⌉₊ : ℝ) / (n+1 : ℕ) - m t ≤ _
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma upperRoundedTrial_finite_range (m : Trial) (n : ℕ) :
    (Set.range (upperRoundedTrial m n)).Finite := by
  apply (Set.finite_Iic (n+1)).image (fun k : ℕ => (k : ℝ)/((n+1 : ℕ) : ℝ)) |>.subset
  rintro _ ⟨t,rfl⟩
  refine ⟨⌈((n+1 : ℕ) : ℝ)*m t⌉₊, ?_, rfl⟩
  exact Nat.ceil_le.mpr (by nlinarith [m.le_one t])

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem controlValue_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : controlValue P f m ≤ ‖f‖ := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem zero_payoff_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    (∫ ω, f (brownianEval 1 ω) ∂P) ≤ controlValue P f m := by
  apply le_csSup (controlPayoffs_bddAbove P f m)
  exact ⟨fun _ _ => 0, progressive_zero P, by simp, by simp⟩

theorem neg_norm_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : -‖f‖ ≤ controlValue P f m := by
  exact (abs_le.mp (abs_integral_reward_le P f (brownianEval 1))).1.trans
    (zero_payoff_le_controlValue P f m)

lemma continuous_patternField {α : ℝ} {N : ℕ} (a : Fin (patternCount α N)) :
    Continuous (fun p : Patterns α N × Spin N => patternField p.1 a p.2) := by
  unfold patternField
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp ((continuous_apply a).comp
    (continuous_fst : Continuous (fun p : Patterns α N × Spin N => p.1)))).mul
    ((EuclideanSpace.proj i).continuous.comp
      (continuous_snd : Continuous (fun p : Patterns α N × Spin N => p.2)))

lemma continuous_hamiltonian (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun p : Patterns α N × Spin N => hamiltonian α φ N p.1 p.2) := by
  unfold hamiltonian
  apply continuous_finsetSum
  intro a _
  exact φ.continuous.comp (continuous_patternField a)

lemma abs_hamiltonian_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |hamiltonian α φ N g x| ≤ (patternCount α N : ℝ) * ‖φ‖ := by
  unfold hamiltonian
  calc
    |∑ a, φ (patternField g a x)| ≤ ∑ a, |φ (patternField g a x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (patternCount α N), ‖φ‖ :=
      Finset.sum_le_sum fun a _ => φ.norm_coe_le_norm _
    _ = _ := by simp

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

lemma abs_energy_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |β * hamiltonian α φ N g x| ≤ |β| * (patternCount α N : ℝ) * ‖φ‖ := by
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le α φ N g x) (abs_nonneg β)

lemma integrable_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Integrable (fun x => Real.exp (β * hamiltonian α φ (N + 1) g x))
      (sphereLaw (N + 1)) := by
  apply (integrable_const (Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))).mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)

lemma partition_bounds (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)) ≤
      (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ∧
    (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ≤
      Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖) := by
  constructor
  · calc
      _ = ∫ _ : Spin (N + 1), Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
          ∂sphereLaw (N + 1) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_partition α β φ N g)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).1))
  · calc
      _ ≤ ∫ _ : Spin (N + 1), Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)
          ∂sphereLaw (N + 1) := integral_mono (integrable_partition α β φ N g)
        (integrable_const _)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2))
      _ = _ := by simp

lemma partition_pos (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    0 < ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1) :=
  (Real.exp_pos _).trans_le (partition_bounds α β φ N g).1

lemma continuous_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun g : Patterns α (N + 1) =>
      ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) := by
  apply continuous_of_dominated (bound := fun _ =>
    Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
  · intro g
    exact (integrable_partition α β φ N g).aestronglyMeasurable
  · intro g
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_id.prodMk continuous_const)))

lemma continuous_pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (pressure α β φ (N + 1)) := by
  unfold pressure
  apply Continuous.div_const
  exact (continuous_partition α β φ N).log (fun g => ne_of_gt (partition_pos α β φ N g))

lemma abs_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    |pressure α β φ (N + 1) g| ≤
      |β| * (patternCount α (N + 1) : ℝ) * ‖φ‖ / (N + 1 : ℝ) := by
  have hp := partition_pos α β φ N g
  have hb := partition_bounds α β φ N g
  have hlo := Real.log_le_log (Real.exp_pos _) hb.1
  have hhi := Real.log_le_log hp hb.2
  rw [Real.log_exp] at hlo hhi
  have hd : 0 ≤ (N + 1 : ℝ) := by positivity
  unfold pressure
  rw [abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right
    (abs_le.mpr ⟨hlo, hhi⟩) hd

section ProductVariance
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y] in
lemma continuous_integral_of_bounded {F : X × Y → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : ∀ p, |F p| ≤ K) :
    Continuous (fun x => ∫ y, F (x, y) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => K)
  · intro x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => hK (x, y))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun y =>
      hF.comp (continuous_id.prodMk continuous_const)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] in
lemma abs_integral_of_bounded {F : X × Y → ℝ} {K : ℝ} (hK : ∀ p, |F p| ≤ K)
    (x : X) : |∫ y, F (x, y) ∂ν| ≤ K := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (f := fun y => F (x, y))
    (Filter.Eventually.of_forall fun y => hK (x, y))

lemma variance_prod_le {F : X × Y → ℝ} (hF : Continuous F)
    {K A B : ℝ} (hK : ∀ p, |F p| ≤ K)
    (hA : ∀ x, variance (fun y => F (x, y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x, y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A + B := by
  have hp : MemLp F 2 (μ.prod ν) :=
    MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
  have hs (x : X) : MemLp (fun y => F (x, y)) 2 ν :=
    MemLp.of_bound (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      K (Filter.Eventually.of_forall fun y => hK (x, y))
  have hh : MemLp (fun x => ∫ y, F (x, y) ∂ν) 2 μ :=
    MemLp.of_bound (continuous_integral_of_bounded ν hF hK).aestronglyMeasurable K
      (Filter.Eventually.of_forall (abs_integral_of_bounded ν hK))
  have hi : (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + ∫ x, (∫ y, F (x, y) ∂ν) ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x, (A + (∫ y, F (x, y) ∂ν) ^ 2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using (sub_le_iff_le_add.mp hv)
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  simpa only [Pi.pow_apply] using sub_le_iff_le_add.mpr (by linarith :
    (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + B + (∫ x, ∫ y, F (x, y) ∂ν ∂μ) ^ 2)

end ProductVariance

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [SecondCountableTopology X] in
lemma variance_le_of_oscillation {F : X → ℝ} (hF : Continuous F) {c : ℝ}
    (hosc : ∀ x y, |F x - F y| ≤ c) : variance F μ ≤ c ^ 2 := by
  let x₀ : X := Classical.choice ‹Nonempty X›
  have hbound : ∀ᵐ x ∂μ, F x ∈ Icc (F x₀ - c) (F x₀ + c) := by
    apply Filter.Eventually.of_forall
    intro x
    have hh := abs_le.mp (hosc x x₀)
    constructor <;> linarith
  have hv := variance_le_sq_of_bounded hbound hF.measurable.aemeasurable
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma continuous_fin_cons {n : ℕ} :
    Continuous (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous (fun p : X × (Fin n → X) => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp
      (continuous_snd : Continuous (fun p : X × (Fin n → X) => p.2))

omit [BorelSpace X] [Nonempty X] in
lemma measurePreserving_fin_cons (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma measurableEmbedding_fin_cons (n : ℕ) :
    MeasurableEmbedding (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurableEmbedding
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

theorem variance_pi_le_of_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
    (hF : Continuous F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
    (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
    variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2 := by
  classical
  induction n with
  | zero =>
      rw [Measure.pi_of_empty]
      simp
  | succ n ih =>
      let ν := Measure.pi fun _ : Fin n => μ
      let G : X × (Fin n → X) → ℝ := fun p => F (Fin.cons (α := fun _ => X) p.1 p.2)
      have hG : Continuous G := hF.comp continuous_fin_cons
      have hGK (p) : |G p| ≤ K := hK _
      have hA (x : X) : variance (fun y => G (x, y)) ν ≤ (n : ℝ) * c ^ 2 := by
        apply ih (hG.comp (continuous_const.prodMk continuous_id)) (fun y => hGK (x,y))
        intro y i z
        simpa only [G, Function.comp_apply, id_eq, Fin.cons_update] using hdiff (Fin.cons x y) i.succ z
      have hHc : Continuous (fun x => ∫ y, G (x, y) ∂ν) :=
        continuous_integral_of_bounded ν hG hGK
      have hHosc (x x' : X) :
          |(∫ y, G (x, y) ∂ν) - ∫ y, G (x', y) ∂ν| ≤ c := by
        have hi (x : X) : Integrable (fun y => G (x, y)) ν :=
          (integrable_const K).mono'
            (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => hGK (x, y))
        rw [← integral_sub (hi x) (hi x')]
        have hh : ∀ y, |G (x, y) - G (x', y)| ≤ c := by
          intro y
          have hu : Function.update (Fin.cons x' y) 0 x = Fin.cons (α := fun _ => X) x y := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [G, hu] using hdiff (Fin.cons x' y) 0 x
        simpa using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun y => G (x,y) - G (x',y))
          (Filter.Eventually.of_forall hh)
      have hv := variance_prod_le μ ν hG hGK hA
        (variance_le_of_oscillation μ hHc hHosc)
      have hpF : MemLp F 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
        MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
      have hpG : MemLp G 2 (μ.prod ν) :=
        MemLp.of_bound hG.aestronglyMeasurable K (Filter.Eventually.of_forall hGK)
      rw [variance_eq_sub hpG] at hv
      rw [variance_eq_sub hpF]
      have hmean := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) F
      have hsquare := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) (fun x => F x ^ 2)
      change (∫ x, G x ∂μ.prod ν) = _ at hmean
      change (∫ x, G x ^ 2 ∂μ.prod ν) = _ at hsquare
      simp only [Pi.pow_apply] at hv ⊢
      rw [hsquare, hmean] at hv
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_ControlDrift
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma abs_hamiltonian_update_sub_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (a : Fin (patternCount α N)) (y : Fin N → ℝ) (x : Spin N) :
    |hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x| ≤ 2 * ‖φ‖ := by
  classical
  have heq : hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x =
      φ (patternField (Function.update g a y) a x) - φ (patternField g a x) := by
    unfold hamiltonian
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      simp [patternField, Function.update_of_ne hba]
    · simp
  rw [heq]
  calc
    _ ≤ |φ (patternField (Function.update g a y) a x)| + |φ (patternField g a x)| :=
      abs_sub _ _
    _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _)
    _ = _ := by ring

lemma abs_pressure_update_sub_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) (a : Fin (patternCount α (N + 1))) (y : Fin (N + 1) → ℝ) :
    |pressure α β φ (N + 1) (Function.update g a y) - pressure α β φ (N + 1) g| ≤
      (2 * |β| * ‖φ‖) / (N + 1 : ℝ) := by
  have hh := abs_log_integral_exp_sub_le (sphereLaw (N + 1))
    (integrable_partition α β φ N (Function.update g a y)) (integrable_partition α β φ N g)
    (partition_pos α β φ N (Function.update g a y)) (partition_pos α β φ N g)
    (c := 2 * |β| * ‖φ‖) (fun x => by
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ |β| * (2 * ‖φ‖) := mul_le_mul_of_nonneg_left
          (abs_hamiltonian_update_sub_le α φ (N + 1) g a y x) (abs_nonneg β)
        _ = _ := by ring)
  unfold pressure
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right hh
    (show 0 ≤ (N + 1 : ℝ) by positivity)

lemma variance_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 := by
  exact variance_pi_le_of_bounded_differences (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    (patternCount α (N + 1)) (continuous_pressure α β φ N)
    (abs_pressure_le α β φ N) (abs_pressure_update_sub_le α β φ N)

lemma variance_pressure_le_rate (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ) := by
  have hM : (patternCount α (N + 1) : ℝ) ≤ α * (N + 1 : ℝ) := by
    simpa [patternCount] using Nat.floor_le
      (mul_nonneg hα (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity))
  calc
    _ ≤ (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      variance_pressure_le α β φ N
    _ ≤ (α * (N + 1 : ℝ)) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    _ = _ := by
      have hn : (N + 1 : ℝ) ≠ 0 := by positivity
      field_simp

lemma pressure_deviation_le (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} ≤
    ENNReal.ofReal ((α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) := by
  have : IsProbabilityMeasure (patternLaw α (N + 1)) := by
    unfold patternLaw
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hp : MemLp (pressure α β φ (N + 1)) 2 (patternLaw α (N + 1)) :=
    MemLp.of_bound (continuous_pressure α β φ N).aestronglyMeasurable _
      (Filter.Eventually.of_forall (abs_pressure_le α β φ N))
  calc
    _ ≤ patternLaw α (N + 1)
        {g | ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} :=
      by
        apply measure_mono
        intro g hg
        change ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)| at hg
        change ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|
        exact le_of_lt hg
    _ ≤ ENNReal.ofReal (variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) / ε ^ 2) :=
      meas_ge_le_variance_div_sq hp hε
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (variance_pressure_le_rate α β hα φ N) (sq_nonneg _))

theorem pressure_concentrates (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|})
      atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ =>
      (α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const
        (ε ^ 2)
  have he := ENNReal.tendsto_ofReal hr
  simp only [ENNReal.ofReal_zero] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => bot_le) (fun N => pressure_deviation_le α β hα φ N ε hε)

theorem pressure_probability_of_expected_limit (α β : ℝ) (hα : 0 ≤ α)
    (φ : ℝ →ᵇ ℝ) (p : ℝ)
    (hp : Tendsto (fun N : ℕ => expectedPressure α β φ (N+1)) atTop (𝓝 p))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => patternLaw α (N+1)
      {g | ε < |pressure α β φ (N+1) g - p|}) atTop (𝓝 0) := by
  have he : ∀ᶠ N in atTop, |expectedPressure α β φ (N+1) - p| < ε/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hp (ε/2) (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (pressure_concentrates α β hα φ (ε/2) (by positivity))
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [he] with N hN
    apply measure_mono
    intro g hg
    change ε/2 < |pressure α β φ (N+1) g - expectedPressure α β φ (N+1)|
    change ε < |pressure α β φ (N+1) g - p| at hg
    have hh := abs_sub_le (pressure α β φ (N+1) g) (expectedPressure α β φ (N+1)) p
    linarith

lemma brownianEval_measurable (t : ℝ≥0) : Measurable (brownianEval t) :=
  (continuous_eval_const t).measurable

lemma usualBrownianSigma_le_completion (P : Measure BrownianPath) (t : Time) :
    usualBrownianSigma P t ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) := by
  unfold usualBrownianSigma
  refine (iInf_le _ (⟨2, lt_of_le_of_lt t.property.2 (by norm_num)⟩ :
    {s : ℝ≥0 // (t : ℝ) < s})).trans ?_
  apply sup_le
  · apply iSup_le
    intro r
    exact (brownianEval_measurable r.val).comap_le.trans
      (fun _ hs => hs.nullMeasurableSet)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact NullMeasurableSet.of_null hs

lemma progressive_joint_complete (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    Measurable (fun p : Time × NullMeasurableSpace BrownianPath P => v p.1 p.2) := by
  have h := (hv 1).mono (show MeasurableSpace.prod inferInstance (usualBrownianSigma P 1) ≤
      MeasurableSpace.prod inferInstance
        (inferInstance : MeasurableSpace (NullMeasurableSpace BrownianPath P)) from
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (usualBrownianSigma_le_completion P 1))) le_rfl
  have hf : Measurable (fun p : Time × NullMeasurableSpace BrownianPath P =>
      (⟨p.1, p.1.property.2⟩ : Set.Iic (1 : Time))) := measurable_fst.subtype_mk
  exact h.comp (hf.prodMk measurable_snd)

lemma progressive_time_measurable (P : Measure BrownianPath)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (ω : BrownianPath) :
    Measurable (fun t : Time => v t ω) :=
  (progressive_joint_complete P hv).comp (measurable_id.prodMk measurable_const)

lemma drift_sq_le_cost (m : Trial) (v : Time → ℝ) (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    (∫ t, m t * v t ∂timeLaw) ^ 2 ≤
      (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw).toReal := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  have hi : Integrable (fun t => m t * v t) timeLaw := by
    apply (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    change |m t * v t| ≤ m t * v t ^ 2 + m t
    rw [abs_mul, abs_of_nonneg (m.nonneg t)]
    have h := sq_nonneg (|v t| - 1)
    have habs : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_abs (v t)]
    calc
      _ ≤ m t * (v t ^ 2 + 1) := mul_le_mul_of_nonneg_left habs (m.nonneg t)
      _ = _ := by ring
  let D := ∫ t, m t * v t ∂timeLaw
  have hnon : 0 ≤ ∫ t, (m t * v t ^ 2 - 2 * D * (m t * v t) + D^2 * m t) ∂timeLaw := by
    apply integral_nonneg
    intro t
    change 0 ≤ m t * v t ^ 2 - 2 * D * (m t * v t) + D^2 * m t
    nlinarith [mul_nonneg (m.nonneg t) (sq_nonneg (v t - D))]
  have hs : Integrable (fun t => m t * v t ^ 2 - 2 * D * (m t * v t)) timeLaw :=
    hq.sub (hi.const_mul (2*D))
  rw [integral_add hs (hm.const_mul (D^2)),
    integral_sub hq (hi.const_mul (2*D)), integral_const_mul, integral_const_mul] at hnon
  have hmone : (∫ t, m t ∂timeLaw) ≤ 1 := by
    calc
      _ ≤ ∫ _ : Time, (1 : ℝ) ∂timeLaw := integral_mono hm (integrable_const _) m.le_one
      _ = _ := by simp
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
    hq.aestronglyMeasurable]
  change D ^ 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hmone (sq_nonneg D)]

lemma controlDrift_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (controlDrift m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => controlDrift m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      (progressive_joint_complete P hv)).stronglyMeasurable.integral_prod_left'.measurable
  exact (show NullMeasurable (controlDrift m v) P from h).aemeasurable

lemma pathControlCost_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (pathControlCost m v) P := by
  have h : Measurable (fun ω : NullMeasurableSpace BrownianPath P => pathControlCost m v ω) :=
    ((m.measurable.comp measurable_fst).mul
      ((progressive_joint_complete P hv).pow_const 2)).ennreal_ofReal.lintegral_prod_left'
  exact (show NullMeasurable (pathControlCost m v) P from h).aemeasurable

lemma controlDrift_sq_integrable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    Integrable (fun ω => controlDrift m v ω ^ 2) P := by
  have hm := pathControlCost_aemeasurable P m hv
  have hfin : ∀ᵐ ω ∂P, pathControlCost m v ω < ∞ := ae_lt_top' hm hc.ne
  apply (integrable_toReal_of_lintegral_ne_top hm hc.ne).mono'
    ((controlDrift_aemeasurable P m hv).pow_const 2).aestronglyMeasurable
  filter_upwards [hfin] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact drift_sq_le_cost m (fun t => v t ω) (progressive_time_measurable P hv ω) hω

lemma integral_controlDrift_sq_le (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    (∫ ω, controlDrift m v ω ^ 2 ∂P) ≤ (controlCost P m v).toReal := by
  have hm := pathControlCost_aemeasurable P m hv
  have hfin : ∀ᵐ ω ∂P, pathControlCost m v ω < ∞ := ae_lt_top' hm hc.ne
  calc
    _ ≤ ∫ ω, (pathControlCost m v ω).toReal ∂P := by
      apply integral_mono_ae (controlDrift_sq_integrable P m hv hc)
        (integrable_toReal_of_lintegral_ne_top hm hc.ne)
      filter_upwards [hfin] with ω hω
      exact drift_sq_le_cost m (fun t => v t ω) (progressive_time_measurable P hv ω) hω
    _ = _ := integral_toReal hm hfin

lemma brownianEval_one_sq_integral (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) : (∫ ω, brownianEval 1 ω ^ 2 ∂P) = 1 := by
  have hm := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  have h := hB.covariance_eval 1 1
  rw [covariance_eq_sub hm hm, hB.integral_eval, zero_mul, sub_zero] at h
  simpa only [sq, min_self, NNReal.coe_one, Pi.mul_apply] using h

lemma controlledTerminal_sq_integral_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    (∫ ω, (brownianEval 1 ω + controlDrift m v ω)^2 ∂P) ≤
      2 + 2 * (controlCost P m v).toReal := by
  have hb := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  have hd := (memLp_two_iff_integrable_sq
    (controlDrift_aemeasurable P m hv).aestronglyMeasurable).mpr
    (controlDrift_sq_integrable P m hv hc)
  calc
    _ ≤ ∫ ω, (2 * brownianEval 1 ω ^ 2 + 2 * controlDrift m v ω ^ 2) ∂P := by
      apply integral_mono (hb.add hd).integrable_sq
        ((hb.integrable_sq.const_mul 2).add (hd.integrable_sq.const_mul 2))
      intro ω
      change (brownianEval 1 ω + controlDrift m v ω)^2 ≤
        2 * brownianEval 1 ω ^ 2 + 2 * controlDrift m v ω ^ 2
      nlinarith [sq_nonneg (brownianEval 1 ω - controlDrift m v ω)]
    _ = 2 + 2 * ∫ ω, controlDrift m v ω ^ 2 ∂P := by
      rw [integral_add (hb.integrable_sq.const_mul 2) (hd.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul, brownianEval_one_sq_integral P hB]
      ring
    _ ≤ _ := by linarith [integral_controlDrift_sq_le P m hv hc]

lemma controlledTerminal_aemeasurable (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) :
    AEMeasurable (fun ω => brownianEval 1 ω + controlDrift m v ω) P :=
  (brownianEval_measurable 1).aemeasurable.add (controlDrift_aemeasurable P m hv)

lemma controlReward_integrable (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) :
    Integrable (fun ω => f (brownianEval 1 ω + controlDrift m v ω)) P := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp_aemeasurable
      (controlledTerminal_aemeasurable P m hv)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _

lemma controlPayoff_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    |controlPayoff P f m v - controlPayoff P g m v| ≤
      ε + (2 * K / R^2) * (2 + 2 * (controlCost P m v).toReal) := by
  let X := fun ω => brownianEval 1 ω + controlDrift m v ω
  have hfI := controlReward_integrable P f m hv
  have hgI := controlReward_integrable P g m hv
  have hX : Integrable (fun ω => X ω ^ 2) P := by
    have hb := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
    have hd := (memLp_two_iff_integrable_sq
      (controlDrift_aemeasurable P m hv).aestronglyMeasurable).mpr
      (controlDrift_sq_integrable P m hv hc)
    exact (hb.add hd).integrable_sq
  have hconst : 0 ≤ 2 * K / R ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
  have hbound (x : ℝ) : |f x - g x| ≤ ε + (2*K/R^2)*x^2 := by
    by_cases hx : |x| ≤ R
    · exact (hnear x hx).trans (le_add_of_nonneg_right (mul_nonneg hconst (sq_nonneg _)))
    · have habs : |f x - g x| ≤ 2*K := by
        calc
          _ ≤ |f x| + |g x| := abs_sub _ _
          _ ≤ K + K := add_le_add ((f.norm_coe_le_norm x).trans hf)
            ((g.norm_coe_le_norm x).trans hg)
          _ = _ := by ring
      have hsq : R^2 ≤ x^2 := by nlinarith [sq_abs x, lt_of_not_ge hx]
      have hr : R^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hR)
      have heq : (2*K/R^2)*R^2 = 2*K := div_mul_cancel₀ _ hr
      have hb := mul_le_mul_of_nonneg_left hsq hconst
      rw [heq] at hb
      exact habs.trans (hb.trans (le_add_of_nonneg_left hε))
  have heq : controlPayoff P f m v - controlPayoff P g m v =
      ∫ ω, (f (X ω) - g (X ω)) ∂P := by
    rw [integral_sub hfI hgI]
    unfold controlPayoff controlDrift
    ring
  rw [heq]
  calc
    _ ≤ ∫ ω, |f (X ω) - g (X ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + (2*K/R^2)*X ω^2) ∂P :=
      integral_mono (hfI.sub hgI).abs ((integrable_const ε).add (hX.const_mul _))
        (fun ω => hbound (X ω))
    _ = ε + (2*K/R^2) * ∫ ω, X ω^2 ∂P := by
      rw [integral_add (integrable_const ε) (hX.const_mul _), integral_const_mul]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (controlledTerminal_sq_integral_le P hB m hv hc) hconst)

lemma controlValue_le_of_cost_cutoff (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (K b : ℝ) (hf : ‖f‖ ≤ K)
    (hb : -K ≤ b)
    (hsmall : ∀ v : Time → BrownianPath → ℝ, Progressive P v →
      controlCost P m v < ∞ → (controlCost P m v).toReal ≤ 4*K+2 →
      controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  by_cases hcost : (controlCost P m v).toReal ≤ 4*K+2
  · exact hsmall v hv hc hcost
  · have hr := (abs_le.mp (abs_integral_reward_le P f
      (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))).2
    unfold controlPayoff
    linarith [lt_of_not_ge hcost]

lemma controlValue_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) :
    |controlValue P f m - controlValue P g m| ≤
      ε + (2 * K / R^2) * (2 + 2 * (4*K+2)) := by
  let δ := ε + (2*K/R^2)*(2+2*(4*K+2))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hfg : controlValue P f m ≤ controlValue P g m + δ := by
    apply controlValue_le_of_cost_cutoff P f m K _ hf
    · linarith [neg_norm_le_controlValue P g m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).2
      have hp : controlPayoff P g m v ≤ controlValue P g m :=
        le_csSup (controlPayoffs_bddAbove P g m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  have hgf : controlValue P g m ≤ controlValue P f m + δ := by
    apply controlValue_le_of_cost_cutoff P g m K _ hg
    · linarith [neg_norm_le_controlValue P f m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).1
      have hp : controlPayoff P f m v ≤ controlValue P f m :=
        le_csSup (controlPayoffs_bddAbove P f m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma controlValue_uniform_of_compact (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f : ℝ →ᵇ ℝ) (fseq : ℕ → ℝ →ᵇ ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hf : ‖f‖ ≤ K) (hseq : ∀ n, ‖fseq n‖ ≤ K)
    (hcomp : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ R → |fseq n x - f x| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m : Trial,
      |controlValue P (fseq n) m - controlValue P f m| < ε := by
  intro ε hε
  let C := 2*K*(2+2*(4*K+2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Q := C / (ε/2)
  have hQ : 0 ≤ Q := div_nonneg hC (by positivity)
  let R := Q+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hQR : Q < R^2 := by dsimp [R]; nlinarith [sq_nonneg Q]
  have hCQ : C = (ε/2)*Q := by dsimp [Q]; field_simp
  have htail : C/R^2 < ε/2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
    rw [hCQ]
    exact mul_lt_mul_of_pos_left hQR (by positivity)
  obtain ⟨N,hN⟩ := hcomp R hR (ε/2) (by positivity)
  refine ⟨N, fun n hn m => ?_⟩
  have hb := controlValue_compact_bound P hB (fseq n) f K R (ε/2) hK hR
    (by positivity) (hseq n) hf (hN n hn) m
  have heq : (2*K/R^2)*(2+2*(4*K+2)) = C/R^2 := by dsimp [C]; ring
  rw [heq] at hb
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_TerminalVariational
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma variationalValue_eq_terminal (P : Measure BrownianPath) (α β : ℝ) (φ : ℝ →ᵇ ℝ) :
    variationalValue P α β φ = terminalVariational P α (β • φ) := rfl

lemma terminalVariational_bounds (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((-α*‖f‖ : ℝ) : EReal) ≤ terminalVariational P α f ∧
      terminalVariational P α f ≤ ((α*‖f‖ : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro m
    have hcv : -α*‖f‖ ≤ α*controlValue P f m := by
      nlinarith [mul_le_mul_of_nonneg_left (neg_norm_le_controlValue P f m) hα]
    exact (EReal.coe_le_coe_iff.mpr hcv).trans
      (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
  · calc
      _ ≤ ((α*controlValue P f oneTrial : ℝ) : EReal) + (entropy oneTrial).toEReal :=
        iInf_le _ oneTrial
      _ ≤ ((α*‖f‖ : ℝ) : EReal) := by
        simp only [entropy_oneTrial, EReal.coe_ennreal_zero, add_zero]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (controlValue_le_norm P f _) hα)

lemma terminalVariational_coe_toReal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((terminalVariational P α f).toReal : EReal) = terminalVariational P α f := by
  obtain ⟨hlo,hhi⟩ := terminalVariational_bounds P α hα f
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)

lemma terminalVariational_toReal_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, controlValue P f m - controlValue P g m ≤ δ) :
    (terminalVariational P α f).toReal - (terminalVariational P α g).toReal ≤ α*δ := by
  have hbound : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
      terminalVariational P α g := by
    apply le_iInf
    intro m
    have h : terminalVariational P α f ≤
        ((α*controlValue P f m : ℝ) : EReal) + (entropy m).toEReal := iInf_le _ m
    have hh : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
        ((α*controlValue P f m - α*δ : ℝ) : EReal) + (entropy m).toEReal := by
      have hs := add_le_add_right h ((-α*δ : ℝ) : EReal)
      rw [← terminalVariational_coe_toReal P α hα f] at hs
      convert hs using 1 <;> simp only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] <;>
        push_cast <;> simp only [neg_mul, add_assoc, add_comm]
    apply hh.trans
    apply add_le_add_left
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hfg m) hα]
  rw [← terminalVariational_coe_toReal P α hα g, EReal.coe_le_coe_iff] at hbound
  linarith

lemma terminalVariational_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, |controlValue P f m - controlValue P g m| ≤ δ) :
    |(terminalVariational P α f).toReal - (terminalVariational P α g).toReal| ≤ α*δ := by
  have h₁ := terminalVariational_toReal_sub_le P α hα f g δ
    (fun m => (abs_le.mp (hfg m)).2)
  have h₂ := terminalVariational_toReal_sub_le P α hα g f δ
    (fun m => by have hh := (abs_le.mp (hfg m)).1; linarith)
  exact abs_le.mpr ⟨by linarith, h₁⟩

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

lemma controlCost_clip_le (P : Measure BrownianPath) (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) : controlCost P m (clipControl L v) ≤ controlCost P m v :=
  lintegral_mono fun ω => pathControlCost_clip_le m hL v ω

lemma weightedTime_integrable (m : Trial) {v : Time → ℝ} (hv : Measurable v)
    (hc : (∫⁻ t, ENNReal.ofReal (m t * v t ^ 2) ∂timeLaw) < ∞) :
    Integrable (fun t => m t * v t ^ 2) timeLaw ∧
      Integrable (fun t => m t * v t) timeLaw := by
  have hm : Integrable m timeLaw :=
    (integrable_const (1 : ℝ)).mono' m.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simpa [abs_of_nonneg (m.nonneg t)] using m.le_one t)
  have hq : Integrable (fun t => m t * v t ^ 2) timeLaw :=
    ⟨(m.measurable.mul (hv.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
        mul_nonneg (m.nonneg t) (sq_nonneg _))).mpr hc⟩
  refine ⟨hq, (hq.add hm).mono' (m.measurable.mul hv).aestronglyMeasurable ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  change |m t * v t| ≤ m t * v t ^ 2 + m t
  rw [abs_mul, abs_of_nonneg (m.nonneg t)]
  have h : |v t| ≤ v t ^ 2 + 1 := by nlinarith [sq_nonneg (|v t| - 1), sq_abs (v t)]
  nlinarith [mul_le_mul_of_nonneg_left h (m.nonneg t)]

lemma integral_pathControlCost (P : Measure BrownianPath) (m : Trial)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    (∫ ω, (pathControlCost m v ω).toReal ∂P) = (controlCost P m v).toReal :=
  integral_toReal (pathControlCost_aemeasurable P m hv)
    (ae_lt_top' (pathControlCost_aemeasurable P m hv) hc.ne)

lemma clipping_drift_gain (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    {v : Time → BrownianPath → ℝ} (ω : BrownianPath)
    (hv : Measurable (fun t => v t ω)) (hc : pathControlCost m v ω < ∞) :
    L * |controlDrift m v ω - controlDrift m (clipControl L v) ω| ≤
      ((pathControlCost m v ω).toReal - (pathControlCost m (clipControl L v) ω).toReal)/2 := by
  have hw : Measurable (fun t => clipControl L v t ω) := measurable_const.max (measurable_const.min hv)
  have hcv := weightedTime_integrable m hv hc
  have hcw := weightedTime_integrable m hw ((pathControlCost_clip_le m hL v ω).trans_lt hc)
  have hev : (∫ t, m t * v t ω ^ 2 ∂timeLaw) = (pathControlCost m v ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcv.1.aestronglyMeasurable
  have hew : (∫ t, m t * clipControl L v t ω ^ 2 ∂timeLaw) =
      (pathControlCost m (clipControl L v) ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hcw.1.aestronglyMeasurable
  unfold controlDrift
  rw [← integral_sub hcv.2 hcw.2]
  calc
    _ ≤ L * ∫ t, |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = ∫ t, L * |m t * v t ω - m t * clipControl L v t ω| ∂timeLaw :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ t, (m t * v t ω ^ 2 - m t * clipControl L v t ω ^ 2)/2 ∂timeLaw := by
      apply integral_mono ((hcv.2.sub hcw.2).abs.const_mul L) ((hcv.1.sub hcw.1).div_const 2)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (m.nonneg t)]
      have h := mul_le_mul_of_nonneg_left (clip_cost_gain hL (v t ω)) (m.nonneg t)
      dsimp [clipControl]
      nlinarith
    _ = _ := by rw [integral_div, integral_sub hcv.1 hcw.1, hev, hew]

lemma controlPayoff_le_clipControl (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hc : controlCost P m v < ∞) :
    controlPayoff P f m v ≤ controlPayoff P f m (clipControl L v) := by
  let w := clipControl L v
  have hw : Progressive P w := progressive_clipControl P hv L
  have hcw : controlCost P m w < ∞ := (controlCost_clip_le P m L.coe_nonneg v).trans_lt hc
  have hpv := pathControlCost_aemeasurable P m hv
  have hpw := pathControlCost_aemeasurable P m hw
  have hcvI := integrable_toReal_of_lintegral_ne_top hpv hc.ne
  have hcwI := integrable_toReal_of_lintegral_ne_top hpw hcw.ne
  have hineq : (∫ ω, (f (brownianEval 1 ω + controlDrift m v ω) -
        f (brownianEval 1 ω + controlDrift m w ω)) ∂P) ≤
      (∫ ω, ((pathControlCost m v ω).toReal - (pathControlCost m w ω).toReal)/2 ∂P) := by
    apply integral_mono_ae ((controlReward_integrable P f m hv).sub (controlReward_integrable P f m hw))
      ((hcvI.sub hcwI).div_const 2)
    filter_upwards [ae_lt_top' hpv hc.ne] with ω hω
    have hLip := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
      (brownianEval 1 ω + controlDrift m w ω)
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hLip
    exact (le_abs_self _).trans (hLip.trans
      (clipping_drift_gain m L.coe_nonneg ω (progressive_time_measurable P hv ω) hω))
  rw [integral_sub (controlReward_integrable P f m hv) (controlReward_integrable P f m hw),
    integral_div, integral_sub hcvI hcwI, integral_pathControlCost P m hv hc,
    integral_pathControlCost P m hw hcw] at hineq
  unfold controlPayoff
  change _ ≤ _
  dsimp only [controlDrift, w] at hineq
  linarith

lemma controlValue_le_of_bounded_controls (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) (b : ℝ)
    (hb : ∀ v : Time → BrownianPath → ℝ, Progressive P v → controlCost P m v < ∞ →
      (∀ t ω, |v t ω| ≤ L) → controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  exact (controlPayoff_le_clipControl P f m L hf hv hc).trans
    (hb (clipControl L v) (progressive_clipControl P hv L)
      ((controlCost_clip_le P m L.coe_nonneg v).trans_lt hc)
      (fun t ω => abs_clip_le L.coe_nonneg (v t ω)))

lemma pathControlCost_le_bound (m : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath) :
    pathControlCost m v ω ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _t : Time, ENNReal.ofReal ((L : ℝ)^2) ∂timeLaw := by
      apply lintegral_mono
      intro t
      apply ENNReal.ofReal_le_ofReal
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      exact (mul_le_mul_of_nonneg_right (m.le_one t) (sq_nonneg _)).trans (by simpa using hx)
    _ = _ := by simp

lemma controlCost_le_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (m : Trial) (L : ℝ≥0) {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) :
    controlCost P m v ≤ ENNReal.ofReal ((L : ℝ)^2) := by
  calc
    _ ≤ ∫⁻ _ω : BrownianPath, ENNReal.ofReal ((L : ℝ)^2) ∂P :=
      lintegral_mono fun ω => pathControlCost_le_bound m L hv ω
    _ = _ := by simp

lemma trial_abs_sub_integrable (m n : Trial) :
    Integrable (fun t => |m t - n t|) timeLaw := by
  apply (integrable_const (2 : ℝ)).mono'
    ((m.measurable.sub n.measurable).abs.aestronglyMeasurable)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg (m.nonneg t), abs_of_nonneg (n.nonneg t)]; linarith [m.le_one t,n.le_one t])

lemma bounded_drift_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |controlDrift m v ω - controlDrift n v ω| ≤ (L : ℝ) * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  rw [controlDrift, controlDrift, ← integral_sub hm.2 hn.2]
  calc
    _ ≤ ∫ t, |m t * v t ω - n t * v t ω| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ) * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.2.sub hn.2).abs ((trial_abs_sub_integrable m n).const_mul L)
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv t ω) (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma bounded_pathCost_trial_diff (m n : Trial) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : ∀ t ω, |v t ω| ≤ L) (ω : BrownianPath)
    (hmv : Measurable (fun t => v t ω)) :
    |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ≤
      (L : ℝ)^2 * ∫ t, |m t - n t| ∂timeLaw := by
  have hm := weightedTime_integrable m hmv ((pathControlCost_le_bound m L hv ω).trans_lt (by finiteness))
  have hn := weightedTime_integrable n hmv ((pathControlCost_le_bound n L hv ω).trans_lt (by finiteness))
  have hem : (pathControlCost m v ω).toReal = ∫ t, m t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (m.nonneg t) (sq_nonneg _))
      hm.1.aestronglyMeasurable).symm
  have hen : (pathControlCost n v ω).toReal = ∫ t, n t * v t ω ^ 2 ∂timeLaw :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_nonneg (n.nonneg t) (sq_nonneg _))
      hn.1.aestronglyMeasurable).symm
  rw [hem, hen, ← integral_sub hm.1 hn.1]
  calc
    _ ≤ ∫ t, |m t * v t ω ^ 2 - n t * v t ω ^ 2| ∂timeLaw := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L : ℝ)^2 * |m t - n t| ∂timeLaw := by
      apply integral_mono (hm.1.sub hn.1).abs ((trial_abs_sub_integrable m n).const_mul ((L : ℝ)^2))
      intro t
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (v t ω))]
      have hx : v t ω ^ 2 ≤ (L : ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v t ω)) L.coe_nonneg).mpr (hv t ω)
      nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg (m t - n t))]
    _ = _ := integral_const_mul _ _

lemma controlPayoff_trial_diff_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hbound : ∀ t ω, |v t ω| ≤ L) :
    |controlPayoff P f m v - controlPayoff P f n v| ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  let D := ∫ t, |m t-n t| ∂timeLaw
  have hcm : controlCost P m v < ∞ := (controlCost_le_bound P m L hbound).trans_lt (by finiteness)
  have hcn : controlCost P n v < ∞ := (controlCost_le_bound P n L hbound).trans_lt (by finiteness)
  have hm := controlReward_integrable P f m hv
  have hn := controlReward_integrable P f n hv
  have hrew : |(∫ ω, f (brownianEval 1 ω + controlDrift m v ω) ∂P) -
      (∫ ω, f (brownianEval 1 ω + controlDrift n v ω) ∂P)| ≤ (L : ℝ)^2 * D := by
    rw [← integral_sub hm hn]
    calc
      _ ≤ ∫ ω, |f (brownianEval 1 ω + controlDrift m v ω) -
          f (brownianEval 1 ω + controlDrift n v ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono (hm.sub hn).abs (integrable_const _)
        intro ω
        have hh := hf.dist_le_mul (brownianEval 1 ω + controlDrift m v ω)
          (brownianEval 1 ω + controlDrift n v ω)
        rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub] at hh
        have hb := mul_le_mul_of_nonneg_left
          (bounded_drift_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)) L.coe_nonneg
        exact hh.trans (by dsimp only [D]; nlinarith [hb])
      _ = _ := by simp
  have hcost : |(controlCost P m v).toReal - (controlCost P n v).toReal| ≤ (L : ℝ)^2 * D := by
    rw [← integral_pathControlCost P m hv hcm, ← integral_pathControlCost P n hv hcn,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne)
        (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)]
    calc
      _ ≤ ∫ ω, |(pathControlCost m v ω).toReal - (pathControlCost n v ω).toReal| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _ω : BrownianPath, (L : ℝ)^2 * D ∂P := by
        apply integral_mono
          ((integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P m hv) hcm.ne).sub
            (integrable_toReal_of_lintegral_ne_top (pathControlCost_aemeasurable P n hv) hcn.ne)).abs
          (integrable_const _)
        intro ω
        exact bounded_pathCost_trial_diff m n L hbound ω (progressive_time_measurable P hv ω)
      _ = _ := by simp
  apply abs_le.mpr
  obtain ⟨hrewlo,hrewhi⟩ := abs_le.mp hrew
  obtain ⟨hcostlo,hcosthi⟩ := abs_le.mp hcost
  dsimp only [controlPayoff, controlDrift] at *
  constructor <;> linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma controlValue_trial_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m n : Trial) (L : ℝ≥0) (hf : LipschitzWith L f) :
    controlValue P f m - controlValue P f n ≤
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw := by
  suffices controlValue P f m ≤ controlValue P f n +
      (3/2 : ℝ) * (L : ℝ)^2 * ∫ t, |m t-n t| ∂timeLaw by linarith
  apply controlValue_le_of_bounded_controls P f m L hf
  intro v hv _ hbound
  have hpay : controlPayoff P f n v ≤ controlValue P f n :=
    le_csSup (controlPayoffs_bddAbove P f n) ⟨v, hv,
      (controlCost_le_bound P n L hbound).trans_lt (by finiteness), rfl⟩
  have hd := (abs_le.mp (controlPayoff_trial_diff_bound P f m n L hf hv hbound)).2
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_FiniteTerminal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial

lemma le_terminalTrial (m : Trial) (r t : Time) : m t ≤ terminalTrial m r t := by
  change m t ≤ if r ≤ t then 1 else m t
  split_ifs; exact m.le_one t; exact le_rfl

lemma terminalTrial_finite_range (m : Trial) (r : Time) (h : (Set.range m).Finite) :
    (Set.range (terminalTrial m r)).Finite := by
  apply (h.insert 1).subset
  rintro _ ⟨t,rfl⟩
  change (if r ≤ t then 1 else m t) ∈ _
  split_ifs
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_range_self t)

lemma terminalTrial_tail (m : Trial) {r t : Time} (hrt : r ≤ t) :
    tailIntegral (terminalTrial m r) t = 1 - (t : ℝ) := by
  have he : (fun s : Time => terminalTrial m r s) =ᵐ[timeLaw.restrict (Ici t)] (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    simp only [terminalTrial, ite_eq_left (hrt.trans hs)]
  rw [tailIntegral,integral_congr_ae he]
  simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr t.property.2]

lemma tailIntegral_antitone (m : Trial) : Antitone (tailIntegral m) := by
  intro s t hst
  apply setIntegral_mono_set (trial_integrable m).integrableOn
    (Eventually.of_forall fun x => m.nonneg x)
  exact Filter.Eventually.of_forall (fun x hx => hst.trans hx)

lemma terminalTrial_entropy_finite (m : Trial) {r : Time} (hr : (r : ℝ) < 1) :
    entropy (terminalTrial m r) < ∞ := by
  have hbound : (∫⁻ t, (ENNReal.ofReal (tailIntegral (terminalTrial m r) t))⁻¹ -
      (ENNReal.ofReal (1-(t : ℝ)))⁻¹ ∂timeLaw) ≤ (ENNReal.ofReal (1-(r : ℝ)))⁻¹ := by
    calc
      _ ≤ ∫⁻ _t : Time, (ENNReal.ofReal (1-(r : ℝ)))⁻¹ ∂timeLaw := by
        apply lintegral_mono
        intro t
        dsimp only
        by_cases ht : r ≤ t
        · rw [terminalTrial_tail m ht,tsub_self]
          exact bot_le
        · have htr : t ≤ r := le_of_not_ge ht
          have hd := tailIntegral_antitone (terminalTrial m r) htr
          rw [terminalTrial_tail m le_rfl] at hd
          exact (tsub_le_self).trans (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hd))
      _ = _ := by simp
  unfold entropy
  apply ENNReal.div_lt_top _ (by norm_num)
  exact (hbound.trans_lt (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr)))).ne

lemma terminalTrial_L1_le (m : Trial) (r : Time) :
    (∫ t, |terminalTrial m r t - m t| ∂timeLaw) ≤ 1-(r : ℝ) := by
  calc
    _ ≤ ∫ t, (Ici r).indicator (fun _ => (1 : ℝ)) t ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        ((integrable_const (1 : ℝ)).indicator measurableSet_Ici)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_terminalTrial m r t))]
      by_cases ht : r ≤ t
      · simp only [terminalTrial,ite_eq_left ht,Set.indicator_of_mem (show t ∈ Ici r from ht)]
        linarith [m.nonneg t]
      · simp only [terminalTrial,ite_eq_right ht,Set.indicator_of_notMem (show t ∉ Ici r from ht),sub_self]
        exact le_rfl
    _ = 1-(r : ℝ) := by
      rw [integral_indicator measurableSet_Ici]
      simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr r.property.2]

lemma upperRoundedTrial_L1_le (m : Trial) (n : ℕ) :
    (∫ t, |upperRoundedTrial m n t - m t| ∂timeLaw) ≤ 1/((n+1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∫ _t : Time, (1 : ℝ)/((n+1 : ℕ) : ℝ) ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs (integrable_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_upperRoundedTrial m n t))]
      exact upperRoundedTrial_sub_le m n t
    _ = _ := by simp

lemma exists_finite_terminal_trial_approx (m : Trial) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Trial, (Set.range q).Finite ∧ (∃ r : Time, (r : ℝ) < 1 ∧ ∀ t, r ≤ t → q t = 1) ∧
      (∀ t, m t ≤ q t) ∧ entropy q ≤ entropy m ∧ entropy q < ∞ ∧
      (∫ t, |q t-m t| ∂timeLaw) < ε := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (half_pos hε)
  let r : Time := ⟨1-min (ε/2) (1/2),by constructor <;> linarith [min_le_left (ε/2) (1/2),min_le_right (ε/2) (1/2),lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2)]⟩
  have hr : (r : ℝ) < 1 := by dsimp [r]; exact sub_lt_self _ (lt_min (half_pos hε) (by norm_num))
  let q := terminalTrial (upperRoundedTrial m n) r
  have hmq (t : Time) : m t ≤ q t := (le_upperRoundedTrial m n t).trans (le_terminalTrial _ r t)
  refine ⟨q,terminalTrial_finite_range _ r (upperRoundedTrial_finite_range m n),
    ⟨r,hr,fun t ht => by simp [q,terminalTrial,ht]⟩,hmq,entropy_antitone hmq,
    terminalTrial_entropy_finite _ hr,?_⟩
  calc
    _ ≤ (∫ t, |q t-upperRoundedTrial m n t| + |upperRoundedTrial m n t-m t| ∂timeLaw) :=
      integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        (((trial_integrable _).sub (trial_integrable _)).abs.add
          ((trial_integrable _).sub (trial_integrable _)).abs) (fun t => abs_sub_le _ _ _)
    _ = (∫ t, |q t-upperRoundedTrial m n t| ∂timeLaw) +
        ∫ t, |upperRoundedTrial m n t-m t| ∂timeLaw :=
      integral_add ((trial_integrable _).sub (trial_integrable _)).abs ((trial_integrable _).sub (trial_integrable _)).abs
    _ ≤ 1-(r : ℝ)+1/((n+1 : ℕ) : ℝ) := add_le_add (terminalTrial_L1_le _ r) (upperRoundedTrial_L1_le m n)
    _ < ε := by
      have hn' : 1/((n+1 : ℕ) : ℝ) < ε/2 := by simpa only [Nat.cast_add,Nat.cast_one] using hn
      dsimp [r]
      linarith [min_le_left (ε/2) (1/2)]

open scoped ContDiff

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_IndexedVertices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianMarks
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FiniteGaussianRow
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {K : Type*} [Fintype K]

lemma finiteGaussianRow_key {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) (k : K) :
    finiteGaussianRow key a (key k) = a k := by
  classical
  simp [finiteGaussianRow,hk.eq_iff]

lemma finiteGaussianRow_zero {key : K → ℕ} (a : K → ℝ) (i : ℕ)
    (hi : ∀ k, key k ≠ i) : finiteGaussianRow key a i = 0 := by
  simp [finiteGaussianRow,hi]

lemma finiteGaussianRow_key_lt (key : K → ℕ) (k : K) :
    key k < finiteGaussianRowLength key :=
  Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))

lemma finiteGaussianRow_tail (key : K → ℕ) (a : K → ℝ) (i : ℕ)
    (hi : finiteGaussianRowLength key ≤ i) : finiteGaussianRow key a i = 0 := by
  apply finiteGaussianRow_zero a i
  intro k
  have h := finiteGaussianRow_key_lt key k
  omega

lemma finiteGaussianRow_sum {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ)
    (F : ℕ → ℝ → ℝ) (hF : ∀ i, F i 0 = 0) :
    (∑ i : Fin (finiteGaussianRowLength key), F i.val (finiteGaussianRow key a i.val)) =
      ∑ k, F (key k) (a k) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i => F i (finiteGaussianRow key a i))]
  have hs : Finset.univ.image key ⊆ Finset.range (finiteGaussianRowLength key) := by
    intro i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finiteGaussianRow_key_lt key k)
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_image hk.injOn]
    simp_rw [finiteGaussianRow_key hk]
  · intro i hi hi'
    rw [finiteGaussianRow_zero a i,hF]
    intro k hki
    exact hi' (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,hki⟩)

lemma finiteGaussianRow_norm {key : K → ℕ} (hk : Function.Injective key) (a : K → ℝ) :
    (∑ i : Fin (finiteGaussianRowLength key), finiteGaussianRow key a i.val^2) = ∑ k, a k^2 :=
  finiteGaussianRow_sum hk a (fun _ x => x^2) (fun _ => by norm_num)

end
variable {I : Type} [Fintype I]

lemma indexedGaussianRowKey_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedGaussianRowKey (I := I) n l) := by
  intro a b hab
  have h := countableCoordinate_injective hab
  exact Prod.ext (indexedLeafSharedVertex_injective n l (congrArg Prod.fst h)) (congrArg (fun q : SharedVertex n × I => q.2) h)

variable {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) =
      ∑ i : I, (∑ d : Fin (n+1), B d i^2) * V x.1 i^2 := by
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => B p.1 p.2 * V x.1 p.2) i.val^2) = _
  rw [finiteGaussianRow_norm (indexedGaussianRowKey_injective n x.2),Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_pow]
  rw [Finset.sum_mul]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_norm_le (n : ℕ) (B : Fin (n+1) → I → ℝ) (V : S → EuclideanSpace ℝ I)
    {C D : ℝ} (hC : ∀ i, (∑ d, B d i^2) ≤ C) (hC0 : 0 ≤ C)
    (hD : ∀ x, (∑ i, V x i^2) ≤ D) (x : S×IndexedLeaf n) :
    (∑ i : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V i.val x^2) ≤ C*D := by
  rw [indexedGaussianRow_norm]
  calc
    _ ≤ ∑ i, C*V x.1 i^2 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)
    _ = C*∑ i, V x.1 i^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ C*D := mul_le_mul_of_nonneg_left (hD x.1) hC0

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedDiagonalField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction

lemma sourceEnrichedFeature_norm (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (x : NormalizedSpin N) : ‖sourceEnrichedFeature N p u x‖=enrichedFeatureBound N u := by
  rw [sourceEnrichedFeature,enrichedFeature_norm,Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedUniformBounds
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

lemma profileGaussian_coefficient_squares {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (i : I) :
    (∑ l : Fin (k+1), hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2) =
      q (Fin.last k) i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (by simp [Fin.le_iff_val_le_val])))
  simp_rw [he]
  exact finite_profile_telescope (fun l => q l i)

lemma enrichedCoordinateLevel_nonneg {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : ∀ l, 0 ≤ h l) (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    0 ≤ enrichedCoordinateLevel p d h l i := by
  cases i with
  | inl i => exact mul_nonneg (by norm_num) (hh l)
  | inr i => exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma enrichedCoordinateLevel_monotone {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : Monotone h) (i : EnrichedIndex N N p) :
    Monotone (fun l => enrichedCoordinateLevel p d h l i) := by
  intro a b hab
  cases i with
  | inl i => exact mul_le_mul_of_nonneg_left (hh hab) (by norm_num)
  | inr i =>
    apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg _)

lemma enrichedCoordinateLevel_le {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} {H : ℝ} (hH : 0 ≤ H) (hh : ∀ l, h l ≤ H)
    (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    enrichedCoordinateLevel p d h l i ≤ 2*H+1 := by
  cases i with
  | inl i => dsimp [enrichedCoordinateLevel]; linarith [hh l]
  | inr i =>
    have ht : ((l.val:ℝ)/(k+1:ℕ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast l.isLt.le
    have ht0 : 0 ≤ ((l.val:ℝ)/(k+1:ℕ)) := by positivity
    exact (pow_le_one₀ ht0 ht).trans (by linarith)

lemma sourceGaussianRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ}
    (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H) (x : NormalizedSpin N × IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianRow p d h u i.val x^2) ≤ (2*H+1)*(enrichedFeatureBound N u:ℝ)^2 := by
  apply indexedGaussianRow_norm_le
  · intro i
    rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
      (enrichedCoordinateLevel_monotone p d hh)]
    exact enrichedCoordinateLevel_le p d hH hhH _ i
  · positivity
  · intro y
    have he := congrArg (fun t : ℝ => t^2) (sourceEnrichedFeature_norm N p u y)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBoltzmann
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma integrable_prod_of_nonneg_uniform_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [SFinite ν] {F : X×Y → ℝ} {C : ℝ}
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hi : ∀ x, Integrable (fun y => F (x,y)) ν)
    (hb : ∀ x, (∫ y, F (x,y) ∂ν) ≤ C) : Integrable F (μ.prod ν) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  apply (integrable_const C).mono' hF.aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_of_nonneg (hpos _)]
    rw [abs_of_nonneg (integral_nonneg fun y => hpos (x,y))]
    exact hb x

end
variable {S : Type*} [MeasurableSpace S]

lemma countableGaussianHamiltonian_measurable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianHamiltonian W v L)) :=
  (hW.comp measurable_snd).add (countableGaussianField_measurable hv hL)

variable (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L)
variable {A D : ℝ} (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)

omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integrable (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*countableGaussianHamiltonian W v L g x)) countableGaussianLaw := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add]
  exact (countableGaussianField_exp_integrable v L x t).const_mul _

include hA hD in
omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integral_bound (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw) ≤
      Real.exp (|t| * A+t^2*D/2) := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add,integral_const_mul]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t))
  · exact countableGaussianField_exp_integral_le v L hD x t
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · exact (Real.exp_pos _).le

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_exp_joint_integrable (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1))
      (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap).const_mul t).exp
    (fun _ => (Real.exp_pos _).le)
    (fun x => countableGaussianHamiltonian_exp_integrable x t)
  exact fun x => countableGaussianHamiltonian_exp_integral_bound hA hD x t

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianCoupling
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section
variable {S : Type*} [MeasurableSpace S]
variable (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_integrable_of_integer_endpoints {H Y : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ k : ℕ, Integrable (fun x => Real.exp (H x+(k:ℝ)*Y x)) μ ∧
      Integrable (fun x => Real.exp (H x-(k:ℝ)*Y x)) μ) (a : ℝ) :
    Integrable (fun x => Real.exp (H x+a*Y x)) μ := by
  obtain ⟨k,hk⟩ := exists_nat_gt |a|
  refine ((he k).1.add (he k).2).mono' ((hH.add (hY.const_mul a)).exp.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hy : 0 ≤ Y x
  · have ha : a ≤ (k:ℝ) := (le_abs_self a).trans hk.le
    exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_right ha hy) _)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have ha : -(k:ℝ) ≤ a := by linarith [neg_abs_le a]
    have hh : H x+a*Y x ≤ H x-(k:ℝ)*Y x := by
      have h := mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)
      nlinarith
    exact (Real.exp_le_exp.mpr hh).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
include hW hv hw hL hA hD hE

lemma countableGaussian_coupling_exp_ae (a : ℝ) :
    ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)) μ := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2) ≤ 2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  have he := (countableGaussianHamiltonian_exp_joint_integrable μ hW hm hL hA hb 1).prod_left_ae
  filter_upwards [he] with g hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [one_mul,countableGaussianHamiltonian,countableGaussianField_add,
    countableGaussianField_smul]
  congr 1
  ring

end

lemma enrichedIndexedBoundedEnergy_bound (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :
    |enrichedIndexedBoundedEnergy n M k f a h x| ≤ (M:ℝ)*‖f‖+|(n+1:ℕ)*h (Fin.last k)| :=
  (abs_sub _ _).trans (add_le_add (normalizedPatternEnergy_bound (n+1) M f a x.1) le_rfl)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedAncestry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma indexedLeafVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin n) :
    indexedVertexDepth n (indexedLeafVertex n l i) = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [indexedLeafVertex,Fin.cases_succ,indexedVertexDepth] using congrArg Fin.succ (ih l.2.2 i)

lemma indexedLeafSharedVertex_depth (n : ℕ) (l : IndexedLeaf n) (i : Fin (n+1)) :
    indexedSharedVertexDepth n (indexedLeafSharedVertex n l i) = i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simpa only [indexedLeafSharedVertex,Fin.cases_succ,indexedSharedVertexDepth] using
      congrArg Fin.succ (indexedLeafVertex_depth n l i)

lemma indexedLeafVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin n) :
    indexedLeafVertex n l i=indexedLeafVertex n m i ↔ i.val< (indexedCommonDepth n l m).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    by_cases he : l.1=m.1 ∧ l.2.1=m.2.1
    · rcases he with ⟨h1,h2⟩
      rw [indexedCommonDepth,ite_eq_left ⟨h1,h2⟩]
      induction i using Fin.cases with
      | zero => simp [indexedLeafVertex,h1,h2]
      | succ i =>
        simpa [indexedLeafVertex,h1,h2] using ih l.2.2 m.2.2 i
    · rw [indexedCommonDepth,ite_eq_right he]
      induction i using Fin.cases <;> simp_all [indexedLeafVertex,Prod.mk.injEq]

lemma indexedLeafSharedVertex_eq_iff (n : ℕ) (l m : IndexedLeaf n) (i : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m i ↔ i ≤ indexedCommonDepth n l m := by
  induction i using Fin.cases with
  | zero => simp [indexedLeafSharedVertex]
  | succ i =>
    simpa only [indexedLeafSharedVertex,Fin.cases_succ,Sum.inr.injEq,
      Fin.le_iff_val_le_val,Fin.val_succ,Nat.succ_le_iff] using indexedLeafVertex_eq_iff n l m i

lemma indexedLeafSharedVertex_eq_iff_pair (n : ℕ) (l m : IndexedLeaf n) (i j : Fin (n+1)) :
    indexedLeafSharedVertex n l i=indexedLeafSharedVertex n m j ↔ i=j ∧ i ≤ indexedCommonDepth n l m := by
  constructor
  · intro h
    have he : i=j := by
      have hh := congrArg (indexedSharedVertexDepth n) h
      simpa only [indexedLeafSharedVertex_depth] using hh
    subst j
    exact ⟨rfl,(indexedLeafSharedVertex_eq_iff n l m i).mp h⟩
  · rintro ⟨rfl,h⟩
    exact (indexedLeafSharedVertex_eq_iff n l m i).mpr h

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma gaussianPrefixCovariance_eventually_eq (v w : ℕ → S → ℝ) (L : S → ℕ) (x y : S) :
    ∀ᶠ n in atTop, gaussianPrefixCovariance v w L n x y=countableGaussianCovariance v w L x y := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn
  unfold gaussianPrefixCovariance countableGaussianCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) n]
  have he (i : ℕ) : maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y =
      if i<L x then w i x*maskedGaussianCoefficient v L i y else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_range_cutoff,min_eq_right hn]
  unfold gaussianPrefixCovariance
  rw [Fin.sum_univ_eq_sum_range (fun i => maskedGaussianCoefficient w L i x*maskedGaussianCoefficient v L i y) (L x)]
  simp_rw [he,sum_range_cutoff,min_self]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedGaussianCovariance
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedLeafProbability_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LocalMaxSecondDerivNonpos
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_log_partition_bound {H : S → ℝ} (hH : Measurable H)
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) :
    |Real.log (tiltPartition μ H 1)| ≤ A := by
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hi : Integrable (fun x => Real.exp (H x)) μ := by
    simpa only [one_mul,mul_one] using tilt_integrable μ (F := fun _ => 1) hH measurable_const hA (by norm_num : (0:ℝ) ≤ 1) hHA (fun _ => by norm_num) 1
  have hlo : Real.exp (-A) ≤ tiltPartition μ H 1 := by
    calc
      _ = ∫ _ : S, Real.exp (-A) ∂μ := by simp
      _ ≤ _ := by simpa only [tiltPartition,one_mul] using integral_mono (integrable_const _) hi (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).1)
  have hhi : tiltPartition μ H 1 ≤ Real.exp A := by
    calc
      _ ≤ ∫ _ : S, Real.exp A ∂μ := by simpa only [tiltPartition,one_mul] using integral_mono hi (integrable_const _) (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).2)
      _ = _ := by simp
  exact abs_le.mpr ⟨by simpa using Real.log_le_log (Real.exp_pos (-A)) hlo,by simpa using Real.log_le_log hp hhi⟩

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UnboundedContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A)
variable {W : A → S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable (Function.uncurry W)) (hv : ∀ i, Measurable (v i))
variable (hw : ∀ i, Measurable (w i)) (hL : Measurable L)
variable {B : A → ℝ} {D E : ℝ} (hB : ∀ a x, |W a x| ≤ B a)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)

include hW hv hw hL

lemma kernelGaussian_coupling_joint_measurable (r : ℝ) :
    Measurable (fun a : (A × (ℕ → ℝ)) × S =>
      countableGaussianHamiltonian (W a.1.1) v L a.1.2 a.2+
        r*countableGaussianField w L a.1.2 a.2) := by
  apply (hW.comp (measurable_fst.fst.prodMk measurable_snd) |>.add
    ((countableGaussianField_measurable hv hL).comp (measurable_fst.snd.prodMk measurable_snd))).add
  exact ((countableGaussianField_measurable hw hL).comp
    (measurable_fst.snd.prodMk measurable_snd)).const_mul r

include hB hD hE

lemma kernelGaussian_coupling_exp_ae (r : ℝ) :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  let κ' : Kernel (A × (ℕ → ℝ)) S := κ.comap (Prod.fst : A × (ℕ → ℝ) → A) measurable_fst
  have hm : MeasurableSet {a : A × (ℕ → ℝ) | Integrable
      (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ' a)} :=
    measurableSet_kernel_integrable (kernelGaussian_coupling_joint_measurable hW hv hw hL r).exp.stronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact ae_of_all _ fun a => countableGaussian_coupling_exp_ae (κ a)
    (hW.comp (measurable_const.prodMk measurable_id)) hv hw hL (hB a) hD hE r

lemma kernelGaussian_all_coupling_exp_ae :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  have hp := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (j:ℝ))
  have hn := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (-(j:ℝ)))
  filter_upwards [hp,hn] with a hp hn r
  apply coupling_integrable_of_integer_endpoints (κ a.1)
    ((hW.comp (measurable_const.prodMk measurable_id)).add
      ((countableGaussianField_measurable hv hL).comp (measurable_const.prodMk measurable_id)))
    ((countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)) _ r
  intro j
  exact ⟨hp j,by simpa only [neg_mul,sub_eq_add_neg,Function.comp_apply,Function.uncurry_apply_pair,
    id_eq,Pi.add_apply,countableGaussianHamiltonian] using hn j⟩

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_general {H F : S → ℝ} (hH : Measurable H) (hF : Measurable F)
    {t C : ℝ} (hC : 0 ≤ C) (hFC : ∀ x, |F x| ≤ C) :
    |tiltMean μ H F t| ≤ C := by
  by_cases hi : Integrable (fun x => Real.exp (t*H x)) μ
  · exact tiltMean_bound_of_integrable μ hH hF hi hFC
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,abs_zero]
    exact hC

lemma replica_exp_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    Integrable (fun x : Fin n → S => Real.exp (t*replicaPotential H n x))
      (Measure.pi fun _ : Fin n => μ) := by
  simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  exact Integrable.fintype_prod (fun _ => hi)

omit [IsProbabilityMeasure μ] in
lemma tilt_law_apply_of_integrable {H : S → ℝ} {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ H t s = (ENNReal.ofReal (tiltPartition μ H t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * H x) ∂μ) := by
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi_of_integrable {H : S → ℝ} (hH : Measurable H) {t : ℝ}
    (hi : Integrable (fun x => Real.exp (t*H x)) μ) (n : ℕ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential H n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ H t) := by
  let := tilt_law_probability_of_integrable μ hi
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply_of_integrable _ (replica_exp_integrable μ hi n) (MeasurableSet.univ_pi hs),
    replica_partition μ hH n,ENNReal.ofReal_pow (tilt_partition_pos_of_integrable μ hi).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential H n x) =
      ∏ i, Real.exp (t * H (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * H x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply_of_integrable μ hi (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma gibbsReplicaMean_integral_of_integrable {H : S → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (n : ℕ) (G : (Fin n → S) → ℝ) :
    gibbsReplicaMean μ H n G = ∫ x, G x ∂Measure.pi (fun _ : Fin n => tiltLaw μ H 1) := by
  rw [← tilt_law_pi_of_integrable μ hH (by simpa only [one_mul] using hi),
    tilt_law_integral_of_integrable _ (replicaPotential_measurable hH n)
      (replica_exp_integrable μ (by simpa only [one_mul] using hi) n)]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ReplicaIBP
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelCarrierIndexedCascadeBaseIndexedLeafIndexedLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdEnrichedMarkHAddNatOfNatCarrierDecoratedCascadeEnrichedDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdForallNatForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedRowsDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureProdNatForallForallFinHAddOfNatRealEnrichedMarkCarrierDecoratedCascadeEnrichedPoissonDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGaussianTestRow_measurable {N k : ℕ} (p d : Fin N → ℕ)
    (h : Fin (k+1) → ℝ) (j : Fin N) (i : ℕ) :
    Measurable (sourceGaussianTestRow p d h j i) :=
  indexedGaussianRow_measurable _ _ (enrichedFeature_continuous _ _ _ _ _).measurable i

lemma sourceGaussianTestRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ} (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H)
    (j : Fin N) (x : NormalizedSpin N×IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianTestRow p d h j i.val x^2) ≤ 2*H+1 := by
  have hb (y : NormalizedSpin N) : (∑ i, sourceGaussianTestFeature N p j y i^2) ≤ (1:ℝ) := by
    have he := enrichedFeature_norm_sq N N p 0 (Pi.single j 1) y
    have hsum : (∑ i : Fin N, ((Pi.single j (1:ℝ) : Fin N → ℝ) i)^2) = (1:ℝ) := by
      classical
      simp [Pi.single_apply]
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,hsum] at he
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,sourceGaussianTestFeature] using he.le
  have ht := indexedGaussianRow_norm_le k
    (hierarchyRowCoefficients k (profileGaussianRoot (enrichedCoordinateLevel p d h))
      (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceGaussianTestFeature N p j)
    (C := 2*H+1) (D := 1)
    (fun i => by
      rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
        (enrichedCoordinateLevel_monotone p d hh)]
      exact enrichedCoordinateLevel_le p d hH hhH _ i)
    (by positivity) hb x
  simpa only [mul_one,sourceGaussianTestRow] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EnrichedMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma normalizedPatternEnergy_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) (x : NormalizedSpin (n+1)) :
    normalizedPatternEnergy (n+1) (patternCount α (n+1)) (β • φ) g x=
      β*hamiltonian α φ (n+1) g (Real.sqrt (n+1:ℕ) • x.val) := by
  have hn : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have he (a : Fin (patternCount α (n+1))) :
      patternField g a (Real.sqrt (n+1:ℕ) • x.val) = ∑ i, g a i*x.val i := by
    unfold patternField
    simp only [PiLp.smul_apply,smul_eq_mul]
    have hs : (∑ i, g a i*(Real.sqrt (n+1:ℕ)*x.val i)) =
        (∑ i, g a i*x.val i)*Real.sqrt (n+1:ℕ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs,mul_div_cancel_right₀ _ hn]
  simp only [normalizedPatternEnergy,BoundedContinuousFunction.coe_smul,smul_eq_mul,
    hamiltonian,he,Finset.mul_sum]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CouplingKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkDisorderLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceCoupling_all_exp_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x+
        r*sourceCouplingEnergy n k p d h j a x)) (sourceSpinLeafKernel n k a.1) := by
  have he := kernelGaussian_all_coupling_exp_ae (sourceSpinLeafKernel n k) (sourceBaseDataLaw n k z t)
    (sourceBaseEnergy_measurable n k f h) (sourceGaussianRow_measurable p d h u)
    (sourceGaussianTestRow_measurable p d h j) (indexedGaussianRowLength_measurable k)
    (fun a => enrichedIndexedBoundedEnergy_bound n a.1 k f (patternPrefix (n+1) a.1 a.2.1) h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
    (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)) j)
  filter_upwards [he] with a ha r
  simpa only [sourceCouplingHamiltonian,enrichedIndexedHamiltonian,sourceBaseEnergy,
    sourceCouplingEnergy,mul_assoc] using ha (r*perturbationAmplitude (n+1) (fun _ => 1) j)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_ContactGGRate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelInfiniteReplica
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma infiniteReplica_prefix_preserving (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i : Fin r => x i.val)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin r => μ)) := by
  let e : (Finset.range r) ≃ Fin r :=
    { toFun := fun i => ⟨i.val,Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val,Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : MeasurePreserving ((Finset.range r).restrict : (ℕ → S) → (Finset.range r) → S)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : (Finset.range r) => μ)) :=
    ⟨by fun_prop,Measure.infinitePi_map_restrict _⟩
  have he := measurePreserving_piCongrLeft (fun _ : Fin r => μ) e
  exact he.comp hp

lemma kernelInfiniteReplica_prefix_integral (a : A) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) :
    (∫ x, G (fun i => x i.val) ∂kernelInfiniteReplica κ ℕ a) =
      ∫ x, G x ∂Measure.pi (fun _ : Fin r => κ a) := by
  have hp := infiniteReplica_prefix_preserving (κ a) r
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))

lemma annealedInfiniteReplica_prefix_integral (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) ∂P := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val)) :=
    hG.comp (by fun_prop)
  have hi : Integrable (fun a : A × (ℕ → S) => G (fun i : Fin r => a.2 i.val))
      (annealedInfiniteReplicaMeasure κ P H hH) :=
    (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hGB (fun i => a.2 i.val))
  rw [annealedInfiniteReplicaMeasure,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => kernelInfiniteReplica_prefix_integral _ a r hG

lemma annealedInfiniteReplica_gibbs_prefix (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hGB : ∀ x, |G x|≤B) :
    (∫ a, G (fun i => a.2 i.val) ∂annealedInfiniteReplicaMeasure κ P H hH) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P := by
  rw [annealedInfiniteReplica_prefix_integral κ P H hH r hG hGB]
  apply integral_congr_ae
  filter_upwards [hexp] with a ha
  exact gibbsProbabilityKernel_replica_integral κ H hH a ha r G

end

lemma sourceGibbsArray_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : CompactArray CompactJointOverlap → ℝ} (hF : Measurable F) :
    (∫ Q, F Q ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, F (sourceJointArray a.2) ∂annealedInfiniteReplicaMeasure (sourceFullSpinLeafKernel n k)
        ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
        (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) := by
  exact integral_map ((sourceJointArray_measurable (n+1) k).comp measurable_snd).aemeasurable hF.aestronglyMeasurable

lemma sourceGibbsArray_block_integral (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (r : ℕ)
    {F : CompactBlock CompactJointOverlap r → ℝ} (hF : Measurable F)
    {B : ℝ} (hFB : ∀ Q, |F Q|≤B) :
    (∫ Q, F (compactBlock r Q) ∂sourceGibbsArrayLaw n k f p d h u z t) =
      ∫ a, gibbsReplicaMean (sourceFullSpinLeafKernel n k a)
        (sourceCouplingHamiltonian n k f p d h u a) r
        (fun x => F (fun i j => sourceJointOverlap (x i) (x j)))
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw := by
  rw [sourceGibbsArray_integral n k f p d h u z t (F:=fun Q => F (compactBlock r Q))
    (hF.comp (compactBlock_continuous r).measurable)]
  have he := sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t
  have he0 : ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
    filter_upwards [he] with a ha
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  exact annealedInfiniteReplica_gibbs_prefix (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) _
    (sourceCouplingHamiltonian_measurable n k f p d h u) he0 r
    (hF.comp (Measurable.of_eval fun row => Measurable.of_eval fun column =>
      (sourceJointOverlap_measurable (n+1) k).comp
        ((measurable_pi_apply row).prodMk (measurable_pi_apply column))))
    (fun x => hFB _)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma countableGaussianCovariance_posSemidef {S : Type*} [MeasurableSpace S]
    (v : ℕ → S → ℝ) (L : S → ℕ) (r : ℕ) (x : Fin r → S) :
    Matrix.PosSemidef (fun i j => countableGaussianCovariance v v L (x i) (x j)) := by
  classical
  have he : ∀ᶠ n in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (x i) (x j) = countableGaussianCovariance v v L (x i) (x j) := by
    simp only [Filter.eventually_all]
    exact fun i j => gaussianPrefixCovariance_eventually_eq v v L (x i) (x j)
  obtain ⟨n,hn⟩ := he.exists
  let A : Matrix (Fin n) (Fin r) ℝ := fun a i => maskedGaussianCoefficient v L a.val (x i)
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  have hm : (fun i j => countableGaussianCovariance v v L (x i) (x j)) = Aᴴ * A := by
    funext i j
    rw [← hn i j]
    simp only [gaussianPrefixCovariance,A]
    rfl
  rw [hm]
  exact hp

lemma sourceSpinArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).1:ℝ)) := by
  exact Matrix.posSemidef_gram ℝ (fun i : Fin r => (x i).1.val)

lemma sourceTreeArray_posSemidef {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r => ((sourceJointArray x i j).2:ℝ)) := by
  let q : Fin (k+1) → Fin 1 → ℝ := fun l _ => (l.val:ℝ)/(k+1:ℕ)
  let V : NormalizedSpin N → EuclideanSpace ℝ (Fin 1) := fun _ => WithLp.toLp 2 (fun _ => 1)
  let v := indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V
  have hq : ∀ i, Monotone (fun l => q l i) := by
    intro i a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  have he (i j : Fin r) : countableGaussianCovariance v v
      (indexedGaussianRowLength (I := Fin 1) k) (x i) (x j) = ((sourceJointArray x i j).2:ℝ) := by
    rw [profileGaussianRow_covariance q (by intro; simp [q]) hq V V]
    simp [q,V,sourceJointArray,sourceJointOverlap]
  have hp := countableGaussianCovariance_posSemidef v
    (indexedGaussianRowLength (I := Fin 1) k) r (fun i => x i)
  simpa only [he] using hp

lemma sourceJointArray_diagonal {N k : ℕ} (x : ℕ → NormalizedSpin N×IndexedLeaf k) (i : ℕ) :
    ((sourceJointArray x i i).1:ℝ) = 1 := by
  change inner ℝ (x i).1.val (x i).1.val = 1
  have hx : ‖(x i).1.val‖=1 := by simp
  simp [hx]

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma infinite_iid_reindex_preserving (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun x : ℕ → S => fun i => x (e i))
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have he : (fun x : ℕ → S => fun i => x (e i)) = MeasurableEquiv.piCongrLeft (fun _ : ℕ => S) e.symm := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact ⟨(MeasurableEquiv.piCongrLeft _ e.symm).measurable,
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => μ) e.symm⟩

end

lemma annealedInfiniteReplica_reindex {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
    (H : A → S → ℝ) (hH : Measurable (Function.uncurry H)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (fun a : A×(ℕ→S) => (a.1,fun i => a.2 (e i)))
      (annealedInfiniteReplicaMeasure κ P H hH) (annealedInfiniteReplicaMeasure κ P H hH) := by
  let : IsMarkovKernel (gibbsProbabilityKernel κ H) := gibbsProbabilityKernel_markov κ H hH
  have hm : Measurable (fun x : ℕ→S => fun i => x (e i)) := by fun_prop
  have he : (kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map (fun x i => x (e i)) =
      kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ := by
    ext a s hs
    rw [Kernel.map_apply _ hm _]
    exact congrArg (fun μ : Measure (ℕ→S) => μ s)
      (infinite_iid_reindex_preserving (gibbsProbabilityKernel κ H a) e).map_eq
  refine ⟨by fun_prop, ?_⟩
  change (P ⊗ₘ kernelInfiniteReplica (gibbsProbabilityKernel κ H) ℕ).map
    (Prod.map id (fun x i => x (e i))) = _
  rw [← Measure.compProd_map hm,he]
  rfl

lemma compactRelabel_continuous {K : Type*} [TopologicalSpace K] (e : Equiv.Perm ℕ) :
    Continuous (compactRelabel (K:=K) e) := by unfold compactRelabel; fun_prop

lemma sourceGibbsArray_exchangeable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _)
      (sourceGibbsArrayLaw n k f p d h u z t : Measure _) := by
  have hr := annealedInfiniteReplica_reindex (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u) e
  have hm : Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) :=
    (sourceJointArray_measurable (n+1) k).comp measurable_snd
  refine ⟨(compactRelabel_continuous e).measurable, ?_⟩
  change Measure.map _ (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
    (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ∘
    (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => (a.1,fun i => a.2 (e i)))) _ = _
  rw [← Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

lemma compact_exchangeability_limit {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    {μ : ℕ → ProbabilityMeasure (CompactArray K)} {ν : ProbabilityMeasure (CompactArray K)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (e : Equiv.Perm ℕ)
    (he : ∀ n, MeasurePreserving (compactRelabel (K:=K) e) (μ n : Measure _) (μ n : Measure _)) :
    MeasurePreserving (compactRelabel (K:=K) e) (ν : Measure _) (ν : Measure _) := by
  have hc := compactRelabel_continuous (K:=K) e
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hc
  have he' (n : ℕ) : (μ n).map hc.measurable.aemeasurable = μ n := by
    apply Subtype.ext
    exact (he n).map_eq
  simp_rw [he'] at hmap
  have hv := tendsto_nhds_unique hmap hμ
  exact ⟨hc.measurable,congrArg Subtype.val hv⟩

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactJointMonomials
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma compactJointMonomial_zero : compactJointMonomial 0 0 = 1 := by ext x; simp

lemma compactJointMonomial_add (p d p' d' : ℕ) :
    compactJointMonomial (p+p') (d+d') = compactJointMonomial p d * compactJointMonomial p' d' := by
  ext x
  simp only [compactJointMonomial_apply,BoundedContinuousFunction.mul_apply,pow_add]
  ring

lemma compactJointMonomial_separates (x y : CompactJointOverlap) (h : x≠y) :
    ∃ p d, compactJointMonomial p d x ≠ compactJointMonomial p d y := by
  by_contra hn
  push Not at hn
  apply h
  apply Prod.ext <;> apply Subtype.ext
  · simpa using hn 1 0
  · simpa using hn 0 1

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGDensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

lemma compactGGTestCLM_apply {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K)) (n : ℕ) (i : Fin n)
    (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ) :
    compactGGTestCLM μ n i f g = compactGGDefect μ n i f g := by
  classical
  simp [compactGGTestCLM,compactGGDefect,boundedTestIntegral]

lemma compactJoint_monomials_total (L : (CompactJointOverlap →ᵇ ℝ) →L[ℝ] ℝ)
    (hL : ∀ p d, L (compactJointMonomial p d)=0) : L=0 := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact CompactJointOverlap ℝ ℝ
  let L' := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  let m (a : ℕ×ℕ) : C(CompactJointOverlap,ℝ) := (compactJointMonomial a.1 a.2).toContinuousMap
  have hm0 : m 0=1 := by ext x; simp [m]
  have hmadd (a b : ℕ×ℕ) : m (a+b)=m a*m b := by
    ext x
    exact congrArg (fun f : CompactJointOverlap →ᵇ ℝ => f x) (compactJointMonomial_add _ _ _ _)
  let M : Submonoid C(CompactJointOverlap,ℝ) :=
    { carrier := Set.range m
      one_mem' := ⟨0,hm0⟩
      mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hmadd a b⟩ }
  let A := Algebra.adjoin ℝ (M : Set C(CompactJointOverlap,ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p,d,hpd⟩ := compactJointMonomial_separates x y hxy
    have hmem : m (p,d) ∈ A :=
      Algebra.subset_adjoin (show m (p,d) ∈ M from ⟨(p,d),rfl⟩)
    exact ⟨m (p,d),⟨m (p,d),hmem,rfl⟩,hpd⟩
  have hA : (A : Set C(CompactJointOverlap,ℝ)) ⊆ (L'.ker : Set C(CompactJointOverlap,ℝ)) := by
    have hspan : Submodule.span ℝ (M : Set C(CompactJointOverlap,ℝ)) ≤ L'.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨p,d⟩,rfl⟩
      change L (e ((compactJointMonomial p d).toContinuousMap)) = 0
      have he : e ((compactJointMonomial p d).toContinuousMap) = compactJointMonomial p d := by
        ext x; rfl
      rw [he]
      exact hL p d
    intro f hf
    apply hspan
    change f ∈ A.toSubmodule at hf
    simpa only [A,Algebra.adjoin_eq_span,Submonoid.closure_eq] using hf
  have hclosed := L'.isClosed_ker
  have hc := closure_minimal hA hclosed
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hall (f : C(CompactJointOverlap,ℝ)) : L' f=0 := by
    apply hc
    change f ∈ A.topologicalClosure
    rw [htop]
    trivial
  ext g
  have h := hall (e.symm g)
  simpa [L'] using h

lemma compactGG_of_joint_monomials (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
    (h : ∀ p d, compactGGDefect μ n i f (compactJointMonomial p d)=0)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect μ n i f g=0 := by
  have hz := compactJoint_monomials_total (compactGGTestCLM μ n i f)
    (fun p d => (compactGGTestCLM_apply μ n i f _).trans (h p d))
  rw [← compactGGTestCLM_apply,hz]
  rfl

end

lemma compactGGDefect_one (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    compactGGDefect μ r i G 1=0 := by
  have hr : 1 ≤ r := by have := i.isLt; omega
  simp only [compactGGDefect,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one,
    integral_const,probReal_univ,smul_eq_mul,Finset.sum_const,Finset.card_erase_of_mem
    (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_sub hr,Nat.cast_one]
  ring

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ) (z : Fin k→ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ→ℝ≥0) (h : ℕ→Fin (k+1)→ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n, u n∈Icc (fun _=>1) (fun _=>2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j=>p j.val) (fun j=>d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1)=>1) (fun _=>2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_limit_joint_gg
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (fun a=>p a.val) (fun a=>d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (g : CompactJointOverlap →ᵇ ℝ) : compactGGDefect ν r i G g=0 := by
  apply compactGG_of_joint_monomials ν r i G
  intro a b
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    subst a b
    simpa only [compactJointMonomial_zero] using compactGGDefect_one ν r i G
  obtain ⟨j,hp,hd⟩ := hcover a b (by omega)
  apply compactGGDefect_limit hlim
  simpa only [hp,hd,Function.comp_def] using
    (source_contact_monomial_tendsto k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht j r i G).comp hs.tendsto_atTop

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapBlock
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

section Positivity

variable {Ω : Type*} [MeasurableSpace Ω]

lemma negativeMatrices_measurable (n : ℕ) (δ : ℝ) :
    MeasurableSet (negativeMatrices n δ) := by
  unfold negativeMatrices
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _h
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i)) measurable_const

omit [MeasurableSpace Ω] in
lemma negativeClique_succ (R : Ω → ℕ → ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    negativeClique R (n + 1) δ = negativeClique R n δ ∩
      ⋂ i : Fin n, {ω | R ω i n < -δ} := by
  ext ω
  simp only [mem_inter_iff, mem_iInter, mem_ofPred]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact h i.castSucc j.castSucc (by exact hij)
    · intro i
      exact h i.castSucc (Fin.last n) (by simp)
  · rintro ⟨hold, hnew⟩ i j hij
    by_cases hj : j.val < n
    · exact hold ⟨i, lt_trans hij hj⟩ ⟨j, hj⟩ hij
    · have jeq : (j : ℕ) = n := by omega
      have hi : (i : ℕ) < n := by omega
      simpa only [overlapBlock, jeq] using hnew ⟨i, hi⟩

omit [MeasurableSpace Ω] in
lemma negativeClique_two (R : Ω → ℕ → ℕ → ℝ) (δ : ℝ) :
    negativeClique R 2 δ = {ω | R ω 0 1 < -δ} := by
  ext ω
  constructor
  · intro h
    exact h 0 1 (by decide)
  · intro h i j hij
    have hi : (i : ℕ) = 0 := by omega
    have hj : (j : ℕ) = 1 := by omega
    change R ω 0 1 < -δ at h
    simpa only [overlapBlock, hi, hj] using h

lemma measureReal_inter_iInter_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {E : Set Ω} {T : ι → Set Ω}
    (hT : ∀ i, MeasurableSet (T i)) :
    μ.real E - ∑ i, μ.real (E \ T i) ≤ μ.real (E ∩ ⋂ i, T i) := by
  classical
  have hu : E \ (⋂ i, T i) = ⋃ i ∈ (Finset.univ : Finset ι), E \ T i := by
    ext ω
    simp
  have hbound : μ.real (E \ ⋂ i, T i) ≤ ∑ i, μ.real (E \ T i) := by
    rw [hu]
    exact measureReal_biUnion_finset_le _ _
  have hsum := measureReal_inter_add_sdiff (μ := μ) (s := E) (MeasurableSet.iInter hT)
  linarith

lemma gg_negativeClique_extension (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hGG : GhirlandaGuerra μ R) {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) :
    μ.real {ω | R ω 0 1 < -δ} * μ.real (negativeClique R n δ) ≤
      μ.real (negativeClique R (n + 1) δ) := by
  classical
  let b := μ.real {ω | R ω 0 1 < -δ}
  let p := μ.real (negativeClique R n δ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htail (i : Fin n) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) = p * (b + (n - 1)) / n := by
    have h := hGG n hn i (negativeMatrices n δ) (negativeMatrices_measurable n δ)
      (Iio (-δ)) measurableSet_Iio
    have hpair (j : Fin n) (hji : j ≠ i) :
      μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ}) = p := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hsym] with ω hω
      apply propext
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        change R ω i j < -δ
        rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
        · exact h i j hij
        · rw [hω i j]
          exact h j i hij
    change μ.real (negativeClique R n δ ∩ {ω | R ω i n < -δ}) =
      p * b / n + (∑ j ∈ Finset.univ.erase i,
        μ.real (negativeClique R n δ ∩ {ω | R ω i j < -δ})) / n at h
    rw [Finset.sum_congr rfl (fun j hj => hpair j (Finset.ne_of_mem_erase hj))] at h
    have hcard : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
    rw [h]
    ring
  have hbad (i : Fin n) :
      μ.real (negativeClique R n δ \ {ω | R ω i n < -δ}) = p * (1 - b) / n := by
    have h := measureReal_inter_add_sdiff (μ := μ) (s := negativeClique R n δ)
      (t := {ω | R ω i n < -δ}) (measurableSet_lt (hR i n) measurable_const)
    rw [htail i] at h
    change _ + _ = p at h
    apply (eq_div_iff (ne_of_gt hnpos)).mpr
    field_simp at h
    nlinarith
  rw [negativeClique_succ]
  have h := measureReal_inter_iInter_lower μ (E := negativeClique R n δ)
    (T := fun i : Fin n => {ω | R ω i n < -δ})
    (fun i => measurableSet_lt (hR i n) measurable_const)
  simp_rw [hbad] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have he : p - (n : ℝ) * (p * (1 - b) / n) = b * p := by
    field_simp
    ring
  rwa [he] at h

lemma negative_gram_sum_bound {n : ℕ} {Q : Fin n → Fin n → ℝ} {δ : ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i ≤ 1)
    (hneg : ∀ i j, i < j → Q i j < -δ) :
    (∑ i, ∑ j, Q i j) ≤ (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) := by
  classical
  have hrow (i : Fin n) : (∑ j, Q i j) ≤ 1 - δ * ((n : ℝ) - 1) := by
    have hpair (j : Fin n) (hji : j ≠ i) : Q i j ≤ -δ := by
      rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hij
      · exact (hneg i j hij).le
      · rw [hsym i j]
        exact (hneg j i hij).le
    have hs : (∑ j ∈ Finset.univ.erase i, Q i j) ≤
        ∑ _j ∈ Finset.univ.erase i, -δ :=
      Finset.sum_le_sum fun j hj => hpair j (Finset.ne_of_mem_erase hj)
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by have := i.isLt; omega)]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    have ht := Finset.sum_erase_add Finset.univ (Q i) (Finset.mem_univ i)
    nlinarith [hdiag i]
  calc
    _ ≤ ∑ _i : Fin n, (1 - δ * ((n : ℝ) - 1)) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; ring

lemma negativeClique_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ}
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 1 < δ * ((n : ℝ) - 1)) :
    μ (negativeClique R n δ) = 0 := by
  have hnot : ∀ᵐ ω ∂μ, ω ∉ negativeClique R n δ := by
    filter_upwards [hsym, hdiag, hpos n] with ω hωs hωd hωp
    intro hωn
    have hb := negative_gram_sum_bound
      (Q := fun i j : Fin n => R ω i j)
      (fun i j => hωs i j) (fun i => hωd i) hωn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : (n : ℝ) * (1 - δ * ((n : ℝ) - 1)) < 0 :=
      mul_neg_of_pos_of_neg hn' (by linarith)
    linarith
  simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hnot

theorem gg_negative_threshold_null (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | R ω 0 1 < -δ} = 0 := by
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra hb
  have hbpos : 0 < μ.real {ω | R ω 0 1 < -δ} := lt_of_not_ge hb
  have hcpos (k : ℕ) : 0 < μ.real (negativeClique R (k + 2) δ) := by
    induction k with
    | zero => simpa only [zero_add, negativeClique_two] using hbpos
    | succ k hk =>
      have he := gg_negativeClique_extension μ hR hsym hGG (n := k + 2) (by omega) δ
      exact (mul_pos hbpos hk).trans_le he
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  have hkδ : 1 < (k : ℝ) * δ := (div_lt_iff₀ hδ).mp hk
  have he : 1 < δ * (((k + 2 : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  have hz := negativeClique_null μ hsym hdiag hpos (n := k + 2) (by omega) he
  have hz' : μ.real (negativeClique R (k + 2) δ) = 0 := (measureReal_eq_zero_iff (μ := μ)).mpr hz
  linarith [hcpos k]

theorem gg_overlap_nonnegative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℕ → ℝ} (hR : ∀ i j, Measurable (fun ω => R ω i j))
    (hsym : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hdiag : ∀ᵐ ω ∂μ, ∀ i, R ω i i ≤ 1)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂μ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, R ω i j)
    (hGG : GhirlandaGuerra μ R) :
    ∀ᵐ ω ∂μ, 0 ≤ R ω 0 1 := by
  have ht (k : ℕ) : ∀ᵐ ω ∂μ, -(1 / ((k : ℝ) + 1)) ≤ R ω 0 1 := by
    rw [ae_iff]
    simpa only [not_le] using gg_negative_threshold_null μ hR hsym hdiag hpos hGG
      (δ := 1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr ht] with ω hω
  have hlim : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  exact le_of_tendsto hlim (Eventually.of_forall hω)

end Positivity

lemma gg_star_growth_impossible {a : ℕ → ℝ} {N ζ : ℝ}
    (hN : 2 ≤ N) (hζ : 0 < ζ) (ha : ∀ k, 0 ≤ a k) (hzero : 0 < a 0)
    (hrec : ∀ k, (N + k) * a (k + 1) = (N + k - 1 + ζ) * a k)
    (hbound : ∀ k : ℕ, (k + 1 : ℝ) * a k ≤ 1) : False := by
  let b : ℕ → ℝ := fun k => (N + k - 1) * a k
  have hbzero : 0 < b 0 := by dsimp [b]; nlinarith
  have hdiff (k : ℕ) : b (k + 1) = b k + ζ * a k := by
    dsimp [b]
    push_cast
    nlinarith [hrec k]
  have hbmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hdiff]
    exact le_add_of_nonneg_right (mul_nonneg hζ.le (ha k))
  have hblower (k : ℕ) : b 0 ≤ b k := hbmono (Nat.zero_le k)
  have hbupper (k : ℕ) : b k ≤ N := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc
      b k ≤ N * ((k + 1 : ℝ) * a k) := by
        dsimp [b]
        have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
      _ ≤ N := by nlinarith [hbound k]
  have hsum (k : ℕ) : ζ * ∑ j ∈ Finset.range k, a j = b k - b 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, mul_add, ih, hdiff]; ring
  have hasum : Summable a := by
    apply summable_of_sum_range_le ha (c := N / ζ)
    intro k
    apply (le_div_iff₀ hζ).mpr
    nlinarith [hsum k, hbupper k]
  have hdom (k : ℕ) : (1 / (k + 1 : ℝ)) ≤ (N / b 0) * a k := by
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [div_le_iff₀ hk]
    have : b 0 ≤ N * ((k + 1 : ℝ) * a k) := by
      calc b 0 ≤ b k := hblower k
           _ ≤ N * ((k + 1 : ℝ) * a k) := by
             dsimp [b]
             have hknonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
             have : N + (k : ℝ) - 1 ≤ N * (k + 1) := by nlinarith
             nlinarith [mul_le_mul_of_nonneg_right this (ha k)]
    have hn : N * ((k + 1 : ℝ) * a k) / b 0 ≥ 1 :=
      (le_div_iff₀ hbzero).mpr (by simpa using this)
    calc 1 ≤ N * ((k + 1 : ℝ) * a k) / b 0 := hn
         _ = (N / b 0) * a k * (k + 1 : ℝ) := by ring
  have hharm : Summable (fun k : ℕ => 1 / (k + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom (hasum.mul_left (N / b 0))
  have hharm' : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hharm
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hharm')

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_OverlapArray
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma copyBlock_measurable (r j : ℕ) : Measurable (copyBlock r j) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma copyEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (j : ℕ) : MeasurableSet (copyEvent r s j) :=
  hs.preimage (copyBlock_measurable r j)

lemma copyIndex_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (i : Fin (r + 1)) :
    π (copyIndex r j i) = copyIndex r (π j) i := by
  by_cases hi : i.val = r
  · simp [copyIndex, hi]
  · simp only [copyIndex, ite_eq_right hi]
    exact hπ i (by omega)

lemma copyBlock_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (Q : OverlapArray) :
    copyBlock r j (relabelArray π Q) = copyBlock r (π j) Q := by
  ext a b
  simp only [copyBlock, relabelArray, copyIndex_relabel r j π hπ]

lemma copyEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (s : Set (OverlapBlock (r + 1))) :
    relabelArray π ⁻¹' copyEvent r s j = copyEvent r s (π j) := by
  ext Q
  simp only [copyEvent, mem_preimage, copyBlock_relabel r j π hπ]

lemma uniqueEvent_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    MeasurableSet (uniqueEvent A i) := by
  simp only [uniqueEvent, ofPred_and, ofPred_forall]
  exact (hA i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hA j).compl)

lemma uniqueEvent_disjoint {Ω ι : Type*} (A : ι → Set Ω) :
    Pairwise (fun i j => Disjoint (uniqueEvent A i) (uniqueEvent A j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hi.2 j hij.symm hj.1

lemma uniqueEvent_probability_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (i₀ : ι)
    (hsame : ∀ i, μ.real (uniqueEvent A i) = μ.real (uniqueEvent A i₀)) :
    Fintype.card ι * μ.real (uniqueEvent A i₀) ≤ 1 := by
  have h := sum_measureReal_le_measureReal_univ (μ := μ) (s := Finset.univ)
    (t := uniqueEvent A) (fun i _ => uniqueEvent_measurable A hA i)
    (fun i _ j _ hij => uniqueEvent_disjoint A hij)
  simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa [Measure.real] using h

lemma uniqueEvent_preimage {Ω ι : Type*} {f : Ω → Ω} (A : ι → Set Ω)
    (e : Equiv.Perm ι) (h : ∀ j, f ⁻¹' A j = A (e j)) (i : ι) :
    f ⁻¹' uniqueEvent A i = uniqueEvent A (e i) := by
  ext ω
  have hm (j : ι) : f ω ∈ A j ↔ ω ∈ A (e j) := by
    change ω ∈ f ⁻¹' A j ↔ ω ∈ A (e j)
    rw [h]
  constructor
  · intro hw
    refine ⟨(hm i).mp hw.1, ?_⟩
    intro j hji hj
    apply hw.2 (e.symm j) (fun heq => hji (by rw [← e.apply_symm_apply j, heq]))
    exact (hm _).mpr (by simpa using hj)
  · intro hw
    refine ⟨(hm i).mpr hw.1, ?_⟩
    intro j hji hj
    exact hw.2 (e j) (fun h' => hji (e.injective h')) ((hm j).mp hj)

lemma uniqueCopy_probability_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r k : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) :
    (k + 1 : ℝ) * μ.real (uniqueEvent
      (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) ≤ 1 := by
  let A : Fin (k + 1) → Set OverlapArray := fun j => copyEvent r s (r + j)
  have hA (j) : MeasurableSet (A j) := copyEvent_measurable r hs _
  have hsame (i : Fin (k + 1)) : μ.real (uniqueEvent A i) = μ.real (uniqueEvent A 0) := by
    let e : Equiv.Perm (Fin (k + 1)) := Equiv.swap i 0
    let π : Equiv.Perm ℕ := Equiv.swap (r + i) (r + (0 : Fin (k + 1)))
    have hfix : ∀ a < r, π a = a := by
      intro a ha
      exact Equiv.swap_apply_of_ne_of_ne (by omega) (by simp; omega)
    have hinj : Function.Injective (fun j : Fin (k + 1) => r + j.val) := by
      intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel hab
    have hmap (j : Fin (k + 1)) : relabelArray π ⁻¹' A j = A (e j) := by
      dsimp [A]
      rw [copyEvent_relabel r _ π hfix]
      congr 1
      exact (hinj.map_swap i 0 j).symm
    have he : e 0 = i := Equiv.swap_apply_right _ _
    rw [← he, ← uniqueEvent_preimage A e hmap]
    exact (hEx _ _).measureReal_preimage (uniqueEvent_measurable A hA 0).nullMeasurableSet
  have h := uniqueEvent_probability_bound μ A hA 0 hsame
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using h

lemma prefixBlock_measurable {n m : ℕ} (h : n ≤ m) : Measurable (prefixBlock h) := by
  exact Measurable.of_eval fun firstIndex => Measurable.of_eval fun secondIndex =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma starMatrices_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (k : ℕ) : MeasurableSet (starMatrices r s t k) := by
  simp only [starMatrices, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter (hs.preimage (prefixBlock_measurable _))
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply _)) measurable_const

lemma starEvent_preimage (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    overlapBlock id (r + 1 + k) ⁻¹' starMatrices r s t k = starEvent r s t k := by
  ext Q
  have hprefix : prefixBlock (Nat.le_add_right (r + 1) k)
      (overlapBlock id (r + 1 + k) Q) = copyBlock r r Q := by
    ext a b
    simp [prefixBlock, overlapBlock, copyBlock]
  simp only [mem_preimage, starMatrices, mem_ofPred_eq, hprefix, starEvent,
    copyEvent, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hj hne => h' ⟨j, hj⟩ hne⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun j hne => h' j j.isLt hne⟩

lemma starEvent_succ (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ) (k : ℕ) :
    starEvent r s t (k + 1) =
      starEvent r s t k ∩ {Q | Q r (r + 1 + k) < t} := by
  ext Q
  constructor
  · rintro ⟨hA, hQ⟩
    exact ⟨⟨hA, fun j hj hne => hQ j (by omega) hne⟩,
      hQ (r + 1 + k) (by omega) (by omega)⟩
  · rintro ⟨⟨hA, hQ⟩, hn⟩
    refine ⟨hA, ?_⟩
    intro j hj hne
    by_cases hlt : j < r + 1 + k
    · exact hQ j hlt hne
    · have heq : j = r + 1 + k := by omega
      simpa only [mem_ofPred_eq, heq] using hn

lemma starEvent_zero (r : ℕ) (s : Set (OverlapBlock (r + 1))) (t : ℝ)
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    starEvent r s t 0 = copyEvent r s r := by
  ext Q
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun j hj hne => hrow Q h j (by omega)⟩

lemma gg_star_recurrence (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hGG : GhirlandaGuerra μ id) {r : ℕ} (hr : 1 ≤ r)
    {s : Set (OverlapBlock (r + 1))} (hs : MeasurableSet s) (t : ℝ) (k : ℕ) :
    ((r + 1 + k : ℕ) : ℝ) * μ.real (starEvent r s t (k + 1)) =
      (((r + 1 + k : ℕ) : ℝ) - 1 + μ.real {Q | Q 0 1 < t}) *
        μ.real (starEvent r s t k) := by
  classical
  let m := r + 1 + k
  let i : Fin m := ⟨r, by dsimp [m]; omega⟩
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := hGG m hm i (starMatrices r s t k) (starMatrices_measurable r hs t k)
    (Iio t) measurableSet_Iio
  rw [starEvent_preimage] at h
  change μ.real (starEvent r s t k ∩ {Q | Q r m < t}) =
    μ.real (starEvent r s t k) * μ.real {Q | Q 0 1 < t} / m +
    (∑ j ∈ Finset.univ.erase i,
      μ.real (starEvent r s t k ∩ {Q | Q r j < t})) / m at h
  have hpair (j : Fin m) (hne : j ≠ i) :
      starEvent r s t k ∩ {Q | Q r j < t} = starEvent r s t k := by
    apply inter_eq_left.mpr
    intro Q hQ
    exact hQ.2 j j.isLt (fun heq => hne (Fin.ext heq))
  rw [Finset.sum_congr rfl (fun j hj => congrArg μ.real
    (hpair j (Finset.ne_of_mem_erase hj)))] at h
  have hcard : ((Finset.univ.erase i).card : ℝ) = (m : ℝ) - 1 := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at h
  rw [← starEvent_succ] at h
  have hmul := congrArg (fun x : ℝ => (m : ℝ) * x) h
  field_simp at hmul
  dsimp [m] at hmul
  nlinarith [hmul]

lemma duplicateEvent_measurable (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ) (j : ℕ) : MeasurableSet (duplicateEvent r s t j) :=
  ((copyEvent_measurable r hs r).inter (copyEvent_measurable r hs j)).inter
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply r)) measurable_const)

lemma duplicateEvent_relabel (r j : ℕ) (π : Equiv.Perm ℕ)
    (hπ : ∀ a < r, π a = a) (hr : π r = r)
    (s : Set (OverlapBlock (r + 1))) (t : ℝ) :
    relabelArray π ⁻¹' duplicateEvent r s t j = duplicateEvent r s t (π j) := by
  ext Q
  simp only [duplicateEvent, copyEvent, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    copyBlock_relabel r r π hπ, copyBlock_relabel r j π hπ, hr, relabelArray]

lemma duplicateEvent_null_future (μ : Measure OverlapArray)
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) {j : ℕ} (hj : r + 1 ≤ j) :
    μ (duplicateEvent r s t j) = 0 := by
  let π : Equiv.Perm ℕ := Equiv.swap (r + 1) j
  have hfix : ∀ a ≤ r, π a = a := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  calc
    μ (duplicateEvent r s t j) = μ (relabelArray π ⁻¹' duplicateEvent r s t (r + 1)) := by
      rw [duplicateEvent_relabel r (r + 1) π (fun a ha => hfix a ha.le) (hfix r le_rfl)]
      simp only [π, Equiv.swap_apply_left]
    _ = μ (duplicateEvent r s t (r + 1)) :=
      (hEx _ _).measure_preimage (duplicateEvent_measurable r hs t (r + 1)).nullMeasurableSet
    _ = 0 := hzero

lemma star_unique_bound_of_no_duplication (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (r : ℕ) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hzero : μ (duplicateEvent r s t (r + 1)) = 0) (k : ℕ) :
    (k + 1 : ℝ) * μ.real (starEvent r s t k) ≤ 1 := by
  have hnul (j : Fin (k + 1)) : ∀ᵐ Q ∂μ, j ≠ 0 → Q ∉ duplicateEvent r s t (r + j) := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hz : μ (duplicateEvent r s t (r + j)) = 0 :=
        duplicateEvent_null_future μ hEx r hs t hzero (by
          have : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with Q hQ
      exact fun _ => hQ
  have hae : starEvent r s t k ≤ᵐ[μ]
      uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0 := by
    filter_upwards [ae_all_iff.mpr hnul] with Q hQ
    intro hstar
    refine ⟨by simpa using hstar.1, ?_⟩
    intro j hj hmem
    apply hQ j hj
    refine ⟨⟨hstar.1, hmem⟩, ?_⟩
    exact hstar.2 (r + j) (by have := j.isLt; omega) (by
      have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega)
  have hle : μ.real (starEvent r s t k) ≤ μ.real
      (uniqueEvent (fun j : Fin (k + 1) => copyEvent r s (r + j)) 0) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans
    (uniqueCopy_probability_bound μ hEx r k hs)

lemma edge_probability_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    (a b i j : ℕ) (t : ℝ) :
    μ.real {Q | Q (Equiv.swap a b i) (Equiv.swap a b j) < t} =
      μ.real {Q | Q i j < t} := by
  exact (hEx a b).measureReal_preimage
    (measurableSet_lt ((measurable_pi_apply j).comp (measurable_pi_apply i))
      measurable_const).nullMeasurableSet

theorem gg_duplicate_last (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (copyEvent r s r))
    (hrow : ∀ Q ∈ copyEvent r s r, ∀ j < r, Q r j < t) :
    0 < μ.real (duplicateEvent r s t (r + 1)) := by
  by_contra hbad
  have hz : μ (duplicateEvent r s t (r + 1)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (le_antisymm (not_lt.mp hbad) (measureReal_nonneg))
  have heq : μ.real {Q | Q r 0 < t} = μ.real {Q | Q 0 1 < t} := by
    have h₁ := edge_probability_swap μ hEx 1 r 1 0 t
    have h₂ := edge_probability_swap μ hEx 0 1 0 1 t
    have hr0 : (0 : ℕ) ≠ r := by omega
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : ℕ) ≠ 1) hr0] at h₁ h₂
    exact h₁.trans h₂
  have hζ : 0 < μ.real {Q | Q 0 1 < t} := by
    rw [← heq]
    refine hA.trans_le (measureReal_mono ?_)
    exact fun Q hQ => hrow Q hQ 0 (by omega)
  apply gg_star_growth_impossible (a := fun k => μ.real (starEvent r s t k))
    (N := (r + 1 : ℕ)) (ζ := μ.real {Q | Q 0 1 < t})
    (by exact_mod_cast (by omega : 2 ≤ r + 1)) hζ (fun _ => measureReal_nonneg)
  · rwa [starEvent_zero r s t hrow]
  · intro k
    simpa only [Nat.cast_add] using gg_star_recurrence μ hGG hr hs t k
  · exact star_unique_bound_of_no_duplication μ hEx r hs t hz

lemma relabelBlock_measurable {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Measurable (relabelBlock e) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma fin_swap_val {n : ℕ} (p q a : Fin n) :
    (Equiv.swap p q a).val = Equiv.swap p.val q.val a.val :=
  Fin.val_injective.map_swap p q a

lemma relabelBlock_swap {n : ℕ} (p q : Fin n) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q) (overlapBlock id n Q) =
      overlapBlock id n (relabelArray (Equiv.swap p.val q.val) Q) := by
  ext a b
  simp only [relabelBlock, overlapBlock, id_eq, relabelArray, fin_swap_val]

lemma relabelArray_swap_swap (p q : ℕ) (Q : OverlapArray) :
    relabelArray (Equiv.swap p q) (relabelArray (Equiv.swap p q) Q) = Q := by
  ext a b
  simp [relabelArray]

lemma replaceBlock_last (r j : ℕ) (Q : OverlapArray) :
    replaceBlock (Fin.last r) j Q = copyBlock r j Q := by
  have h (a : Fin (r + 1)) : replaceIndex (Fin.last r) j a = copyIndex r j a := by
    simp [replaceIndex, copyIndex, Fin.ext_iff]
  ext a b
  simp only [replaceBlock, copyBlock, h]

lemma replaceBlock_swap {n : ℕ} (p q : Fin n) {j : ℕ} (hj : n ≤ j) (Q : OverlapArray) :
    relabelBlock (Equiv.swap p q)
      (replaceBlock q j (relabelArray (Equiv.swap p.val q.val) Q)) =
        replaceBlock p j Q := by
  have h (a : Fin n) : Equiv.swap p.val q.val (replaceIndex q j (Equiv.swap p q a)) =
      replaceIndex p j a := by
    by_cases ha : a = p
    · subst a
      simp only [Equiv.swap_apply_left, replaceIndex, ↓reduceIte]
      exact Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by have := q.isLt; omega)
    · have he : Equiv.swap p q a ≠ q := by
        intro h
        apply ha
        have := congrArg (Equiv.swap p q) h
        simpa using this
      simp only [replaceIndex, ite_eq_right he, ite_eq_right ha, fin_swap_val,
        Equiv.swap_apply_self]
  ext a b
  exact congrArg₂ Q (h a) (h b)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PatternMatrices
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma block_event_swap (μ : Measure OverlapArray) (hEx : OverlapSwapInvariant μ)
    {n : ℕ} (p q : Fin n) {s : Set (OverlapBlock n)} (hs : MeasurableSet s) :
    μ.real (overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s)) =
      μ.real (overlapBlock id n ⁻¹' s) := by
  have heq : overlapBlock id n ⁻¹' (relabelBlock (Equiv.swap p q) ⁻¹' s) =
      relabelArray (Equiv.swap p.val q.val) ⁻¹' (overlapBlock id n ⁻¹' s) := by
    ext Q
    change relabelBlock (Equiv.swap p q) (overlapBlock id n Q) ∈ s ↔ _
    rw [relabelBlock_swap]
    rfl
  rw [heq]
  exact (hEx _ _).measureReal_preimage
    (hs.preimage (Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _))).nullMeasurableSet

theorem gg_duplicate_index (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    {r : ℕ} (hr : 1 ≤ r) (p : Fin (r + 1)) {s : Set (OverlapBlock (r + 1))}
    (hs : MeasurableSet s) (t : ℝ)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' s))
    (hrow : ∀ Q ∈ overlapBlock id (r + 1) ⁻¹' s,
      ∀ j : Fin (r + 1), j ≠ p → Q p j < t) :
    0 < μ.real ((overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
      {Q | Q p (r + 1) < t}) := by
  let q : Fin (r + 1) := Fin.last r
  let e := Equiv.swap p q
  let π := Equiv.swap p.val q.val
  let s' := relabelBlock e ⁻¹' s
  have hs' : MeasurableSet s' := hs.preimage (relabelBlock_measurable e)
  have hbase : copyEvent r s' r = overlapBlock id (r + 1) ⁻¹' s' := by
    ext Q
    change copyBlock r r Q ∈ s' ↔ overlapBlock id (r + 1) Q ∈ s'
    have hb : copyBlock r r Q = overlapBlock id (r + 1) Q := by
      ext a b
      simp [copyBlock, overlapBlock]
    rw [hb]
  have hA' : 0 < μ.real (copyEvent r s' r) := by
    rw [hbase]
    exact (block_event_swap μ hEx p q hs).symm ▸ hA
  have hrow' : ∀ Q ∈ copyEvent r s' r, ∀ j < r, Q r j < t := by
    intro Q hQ j hj
    have hmem : relabelArray π Q ∈ overlapBlock id (r + 1) ⁻¹' s := by
      rw [hbase] at hQ
      change relabelBlock e (overlapBlock id (r + 1) Q) ∈ s at hQ
      rwa [relabelBlock_swap] at hQ
    let a : Fin (r + 1) := ⟨j, by omega⟩
    have hne : e a ≠ p := by
      intro h
      have h' := congrArg e h
      have haq : a = q := by simpa [e] using h'
      have := congrArg Fin.val haq
      dsimp [a, q] at this
      omega
    have h := hrow (relabelArray π Q) hmem (e a) hne
    have hp : π p.val = r := by simp [π, q]
    have ha : π (e a).val = j := by simp [π, e, fin_swap_val, a]
    simpa only [relabelArray, hp, ha] using h
  have hD := gg_duplicate_last μ hEx hGG hr hs' t hA' hrow'
  have hset : relabelArray π ⁻¹' duplicateEvent r s' t (r + 1) =
      (overlapBlock id (r + 1) ⁻¹' s) ∩ replaceEvent p s (r + 1) ∩
        {Q | Q p (r + 1) < t} := by
    ext Q
    have hfirst : copyBlock r r (relabelArray π Q) ∈ s' ↔
        overlapBlock id (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r r (relabelArray π Q)) ∈ s ↔ _
      have hb : copyBlock r r (relabelArray π Q) =
          overlapBlock id (r + 1) (relabelArray π Q) := by
        ext a b
        simp [copyBlock, overlapBlock]
      rw [hb, relabelBlock_swap, relabelArray_swap_swap]
    have hsecond : copyBlock r (r + 1) (relabelArray π Q) ∈ s' ↔
        replaceBlock p (r + 1) Q ∈ s := by
      change relabelBlock e (copyBlock r (r + 1) (relabelArray π Q)) ∈ s ↔ _
      rw [← replaceBlock_last]
      change relabelBlock (Equiv.swap p q)
        (replaceBlock q (r + 1) (relabelArray (Equiv.swap p.val q.val) Q)) ∈ s ↔ _
      rw [replaceBlock_swap p q (le_refl _)]
    have hp : π r = p.val := by exact Equiv.swap_apply_right _ _
    have hnew : π (r + 1) = r + 1 :=
      Equiv.swap_apply_of_ne_of_ne (by have := p.isLt; omega) (by dsimp [q]; omega)
    change ((copyBlock r r (relabelArray π Q) ∈ s' ∧
      copyBlock r (r + 1) (relabelArray π Q) ∈ s') ∧
      Q (π r) (π (r + 1)) < t) ↔ ((overlapBlock id (r + 1) Q ∈ s ∧
        replaceBlock p (r + 1) Q ∈ s) ∧ Q p (r + 1) < t)
    rw [hfirst, hsecond, hp, hnew]
  rw [← hset]
  rwa [(hEx _ _).measureReal_preimage
    (duplicateEvent_measurable r hs' t (r + 1)).nullMeasurableSet]

lemma patternMatrices_measurable {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) :
    MeasurableSet (patternMatrices labels C) := by
  simp only [patternMatrices, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (hC _ _).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma pattern_append_of_duplicate {κ : Type*} {n : ℕ} (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (p : Fin n) (t : ℝ) (hdiag : C (labels p) (labels p) = Iio t)
    (Q : OverlapArray) (hSym : ∀ i j, Q i j = Q j i)
    (hA : overlapBlock id n Q ∈ patternMatrices labels C)
    (hB : replaceBlock p n Q ∈ patternMatrices labels C) (hedge : Q p n < t) :
    overlapBlock id (n + 1) Q ∈ patternMatrices (appendLabel labels (labels p)) C := by
  intro i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro j
    refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) j
    by_cases hb : b = p
    · subst b
      simpa [overlapBlock, hdiag, hSym n p] using hedge
    · have h := hB p b (Ne.symm hb)
      simpa [replaceBlock, replaceIndex, hb, overlapBlock] using h
  · intro j
    refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) j
    · by_cases ha : a = p
      · subst a
        simpa [overlapBlock, hdiag] using hedge
      · have h := hB a p ha
        simpa [replaceBlock, replaceIndex, ha, overlapBlock] using h
    · have h := hA a b (fun h => hab (congrArg Fin.castSucc h))
      simpa [overlapBlock] using h

theorem gg_pattern_append (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {r : ℕ} (hr : 1 ≤ r) (labels : Fin (r + 1) → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin (r + 1)) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id (r + 1) ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (r + 1 + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  have hd := gg_duplicate_index μ hEx hGG hr p (patternMatrices_measurable labels C hC) t hA
    (fun Q hQ j hj => hcut _ _ (hQ p j (Ne.symm hj)))
  apply hd.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hSym] with Q hQ
  exact fun h => pattern_append_of_duplicate labels C p t hdiag Q hQ h.1.1 h.1.2 h.2

lemma gg_pattern_append_nat (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    {κ : Type*} {n : ℕ} (hn : 2 ≤ n) (labels : Fin n → κ)
    (C : κ → κ → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (p : Fin n) (t : ℝ)
    (hdiag : C (labels p) (labels p) = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices labels C)) :
    0 < μ.real (overlapBlock id (n + 1) ⁻¹'
      patternMatrices (appendLabel labels (labels p)) C) := by
  cases n with
  | zero => omega
  | succ r => exact gg_pattern_append μ hEx hGG hSym (by omega) labels C hC p t hdiag hcut hA

lemma appendLabel_tripleLabels {n : ℕ} (hn : 3 ≤ n) :
    appendLabel (tripleLabels n) (tripleLabels n ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩) =
      tripleLabels (n + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · apply Fin.ext
    simp [tripleLabels]
  · simp [tripleLabels]

theorem gg_triple_pattern (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (C : Fin 3 → Fin 3 → Set ℝ) (hC : ∀ k l, MeasurableSet (C k l)) (t : ℝ)
    (hdiag : ∀ k, C k k = Iio t) (hcut : ∀ k l, C k l ⊆ Iio t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) C)) :
    ∀ n ≥ 3, 0 < μ.real (overlapBlock id n ⁻¹' patternMatrices (tripleLabels n) C) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hA
  | succ n hn ih =>
    have h := gg_pattern_append_nat μ hEx hGG hSym (by omega) (tripleLabels n) C hC
      ⟨n % 3, (Nat.mod_lt _ (by omega)).trans_le hn⟩ t (hdiag _) hcut ih
    rwa [appendLabel_tripleLabels hn] at h

open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma inner_replicaMean {n : ℕ} (v w : Fin n → H) :
    ⟪replicaMean v, replicaMean w⟫_ℝ =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, ⟪v i, w j⟫_ℝ := by
  simp only [replicaMean, real_inner_smul_left, real_inner_smul_right]
  rw [sum_inner]
  simp_rw [inner_sum]
  ring

lemma replicaMean_norm_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → H) {c : ℝ}
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1)
    (hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ ≤ c) :
    ‖replicaMean v‖ ^ 2 ≤ c + (1 - c) / n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow (i : Fin n) : (∑ j, ⟪v i, v j⟫_ℝ) ≤ 1 + ((n : ℝ) - 1) * c := by
    have hs : (∑ j ∈ Finset.univ.erase i, ⟪v i, v j⟫_ℝ) ≤
        ∑ _j ∈ Finset.univ.erase i, c :=
      Finset.sum_le_sum fun j hj => hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    have hc : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      rw [Nat.cast_sub hn]
      norm_num
    simp only [Finset.sum_const, nsmul_eq_mul, hc] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [real_inner_self_eq_norm_sq]
    linarith [hdiag i]
  rw [← real_inner_self_eq_norm_sq, inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, v j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (1 + ((n : ℝ) - 1) * c)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = c + (1 - c) / n := by field_simp; ring

lemma replicaMean_norm_le_one {n : ℕ} (hn : 0 < n) (v : Fin n → H)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ 1) : ‖replicaMean v‖ ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsum : ‖∑ i, v i‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        nlinarith [hdiag i, norm_nonneg (v i)]
      _ = n := by simp
  calc
    ‖replicaMean v‖ = (n : ℝ)⁻¹ * ‖∑ i, v i‖ := by
      simp [replicaMean, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ hn0

lemma inner_replicaMean_le {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, ⟪v i, w j⟫_ℝ ≤ a) : ⟪replicaMean v, replicaMean w⟫_ℝ ≤ a := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) ≤
      (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = a := by field_simp

lemma le_inner_replicaMean {n : ℕ} (hn : 0 < n) (v w : Fin n → H) {a : ℝ}
    (h : ∀ i j, a ≤ ⟪v i, w j⟫_ℝ) : a ≤ ⟪replicaMean v, replicaMean w⟫_ℝ := by
  rw [inner_replicaMean]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    a = (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ((n : ℝ) * a)) := by field_simp
    _ ≤ (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, ⟪v i, w j⟫_ℝ) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)

lemma duplicate_ordered_blocks_bound {n : ℕ} (hn : 0 < n) (v : Fin 3 → Fin n → H)
    {a b c t : ℝ} (hab : a ≤ b)
    (hdiag : ∀ k i, ‖v k i‖ ^ 2 ≤ 1)
    (hoff : ∀ k i j, i ≠ j → ⟪v k i, v k j⟫_ℝ ≤ t)
    (h12 : ∀ i j, ⟪v 0 i, v 1 j⟫_ℝ ≤ a)
    (h13 : ∀ i j, b ≤ ⟪v 0 i, v 2 j⟫_ℝ)
    (h23 : ∀ i j, c ≤ ⟪v 1 i, v 2 j⟫_ℝ) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let x := replicaMean (v 0)
  let y := replicaMean (v 1)
  let z := replicaMean (v 2)
  have hx := replicaMean_norm_le_one hn (v 0) (hdiag 0)
  have hy := replicaMean_norm_sq_le hn (v 1) (hdiag 1) (hoff 1)
  have hz := replicaMean_norm_sq_le hn (v 2) (hdiag 2) (hoff 2)
  have hxy : ⟪x, y⟫_ℝ ≤ a := inner_replicaMean_le hn _ _ h12
  have hxz : b ≤ ⟪x, z⟫_ℝ := le_inner_replicaMean hn _ _ h13
  have hyz : c ≤ ⟪y, z⟫_ℝ := le_inner_replicaMean hn _ _ h23
  change ‖x‖ ≤ _ at hx
  change ‖y‖ ^ 2 ≤ _ at hy
  change ‖z‖ ^ 2 ≤ _ at hz
  have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hdiff : ‖z - y‖ ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
    rw [norm_sub_sq_real, real_inner_comm]
    linarith
  have hinner : b - a ≤ ⟪x, z - y⟫_ℝ := by rw [inner_sub_right]; linarith
  have hnonneg : 0 ≤ ⟪x, z - y⟫_ℝ := by linarith
  have habsq : (b - a) ^ 2 ≤ ⟪x, z - y⟫_ℝ ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hab) hnonneg).mpr hinner
  have hcs : ⟪x, z - y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖z - y‖ ^ 2 := by
    have h := abs_real_inner_le_norm x (z - y)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg _))).mpr h
    simpa only [sq_abs, mul_pow] using hs
  exact habsq.trans (hcs.trans ((mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)).trans
    (by simpa using hdiff)))

lemma posSemidef_standard_basis_inner {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) (i j : Fin n) :
    letI := B.toSeminormedAddCommGroup hB
    letI := B.toInnerProductSpace hB
    ⟪(Pi.single i 1 : Fin n → ℝ), Pi.single j 1⟫_ℝ = B i j := by
  change (B *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1) = B i j
  simp

lemma triangleConstraints_measurable (a b c t : ℝ) (k l : Fin 3) :
    MeasurableSet (triangleConstraints a b c t k l) := by
  unfold triangleConstraints
  split_ifs <;> measurability

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TripleIndex
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma triangleConstraints_diag (a b c t : ℝ) (k : Fin 3) :
    triangleConstraints a b c t k k = Iio t := by simp [triangleConstraints]

lemma triangleConstraints_cut {a : ℝ} (b c t : ℝ) (hat : a ≤ t) (k l : Fin 3) :
    triangleConstraints a b c t k l ⊆ Iio t := by
  unfold triangleConstraints
  split_ifs
  · exact Subset.rfl
  · exact Iio_subset_Iio hat
  · exact Ioo_subset_Iio_self
  · exact Ioo_subset_Iio_self

lemma tripleIndex_ne {n : ℕ} {k l : Fin 3} (hkl : k ≠ l) (i j : Fin n) :
    tripleIndex k i ≠ tripleIndex l j := by
  intro h
  have := congrArg (tripleLabels (3 * n)) h
  exact hkl (by simpa using this)

lemma tripleIndex_inj {n : ℕ} (k : Fin 3) {i j : Fin n} (hij : i ≠ j) :
    tripleIndex k i ≠ tripleIndex k j := by
  intro h
  apply hij
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp [tripleIndex] at h'
  omega

lemma triangle_pattern_psd_bound {n : ℕ} (hn : 0 < n)
    (B : OverlapBlock (3 * n)) (hB : Matrix.PosSemidef B)
    (hdiag : ∀ i, B i i ≤ 1) {a b c t : ℝ} (hab : a ≤ b)
    (hpattern : B ∈ patternMatrices (tripleLabels (3 * n)) (triangleConstraints a b c t)) :
    (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / n) := by
  let _ := Matrix.toSeminormedAddCommGroup B hB
  let _ := Matrix.toInnerProductSpace B hB
  let v : Fin 3 → Fin n → (Fin (3 * n) → ℝ) := fun k i => Pi.single (tripleIndex k i) 1
  have hv (k l : Fin 3) (i j : Fin n) :
      ⟪v k i, v l j⟫_ℝ = B (tripleIndex k i) (tripleIndex l j) :=
    posSemidef_standard_basis_inner B hB _ _
  apply duplicate_ordered_blocks_bound hn v hab
  · intro k i
    rw [← real_inner_self_eq_norm_sq, hv]
    exact hdiag _
  · intro k i j hij
    rw [hv]
    have h := hpattern _ _ (tripleIndex_inj k hij)
    simp only [tripleLabels_tripleIndex, triangleConstraints_diag, mem_Iio] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 1) i j)
    simp [triangleConstraints] at h
    exact h.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (0 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le
  · intro i j
    rw [hv]
    have h := hpattern _ _ (tripleIndex_ne (by decide : (1 : Fin 3) ≠ 2) i j)
    simp [triangleConstraints] at h
    exact h.1.le

theorem gg_triangle_pattern_bound (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t)
    (hA : 0 < μ.real (overlapBlock id 3 ⁻¹'
      patternMatrices (tripleLabels 3) (triangleConstraints a b c t))) :
    (b - a) ^ 2 ≤ 2 * (t - c) := by
  have hall := gg_triple_pattern μ hEx hGG hSym (triangleConstraints a b c t)
    (triangleConstraints_measurable a b c t) t (triangleConstraints_diag a b c t)
    (triangleConstraints_cut b c t hat) hA
  have hbound (n : ℕ) : (b - a) ^ 2 ≤ 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ)) := by
    have hpos := hall (3 * (n + 1)) (by omega)
    have hne : μ (overlapBlock id (3 * (n + 1)) ⁻¹'
        patternMatrices (tripleLabels (3 * (n + 1))) (triangleConstraints a b c t)) ≠ 0 := by
      intro hz
      simp [Measure.real, hz] at hpos
    obtain ⟨Q, hQ, hG, hD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hne
      (ae_restrict_of_ae (hGram.and hdiag))
    have h := triangle_pattern_psd_bound (by omega : 0 < n + 1)
      (overlapBlock id (3 * (n + 1)) Q) (hG _) (fun i => hD i) hab hQ
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have ht : Tendsto (fun n : ℕ => 2 * (t - c) + 2 * ((1 - t) / (n + 1 : ℝ))) atTop
      (𝓝 (2 * (t - c))) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_mul (2 * (1 - t))
    have h' := h.const_add (2 * (t - c))
    simpa only [mul_zero, add_zero, mul_one_div, mul_div_assoc] using h'
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

lemma triangleEvent_pattern {a b c t : ℝ} (hat : a ≤ t) (Q : OverlapArray)
    (hSym : ∀ i j, Q i j = Q j i) (hQ : Q ∈ triangleEvent a b c t) :
    overlapBlock id 3 Q ∈ patternMatrices (tripleLabels 3) (triangleConstraints a b c t) := by
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  have hQt : Q 0 1 < t := hQ.1.trans_le hat
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [overlapBlock, tripleLabels, triangleConstraints, triangleEvent]

lemma gg_triangleEvent_null (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1)
    {a b c t : ℝ} (hab : a ≤ b) (hat : a ≤ t) (hgap : 2 * (t - c) < (b - a) ^ 2) :
    μ (triangleEvent a b c t) = 0 := by
  by_contra hne
  have hpos : 0 < μ.real (triangleEvent a b c t) :=
    ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hle : μ.real (triangleEvent a b c t) ≤ μ.real
      (overlapBlock id 3 ⁻¹' patternMatrices (tripleLabels 3) (triangleConstraints a b c t)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hSym] with Q hQ
    exact triangleEvent_pattern hat Q hQ
  exact hgap.not_ge (gg_triangle_pattern_bound μ hEx hGG hSym hGram hdiag hab hat (hpos.trans_le hle))

lemma exists_rational_triangle_box {x y z : ℝ} (hxy : x < y) (hyz : y ≤ z) :
    ∃ a b c t : ℚ, (a : ℝ) ≤ b ∧ (a : ℝ) ≤ t ∧
      2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 ∧
      x < a ∧ (b : ℝ) < y ∧ y < t ∧ (c : ℝ) < z ∧ z < t := by
  obtain ⟨a, hxa, hay⟩ := exists_rat_btwn hxy
  obtain ⟨b, hab, hby⟩ := exists_rat_btwn hay
  have hδ : 0 < ((b : ℝ) - a) ^ 2 / 8 := by positivity
  obtain ⟨c, hzc, hcz⟩ := exists_rat_btwn (show z - ((b : ℝ) - a) ^ 2 / 8 < z by linarith)
  obtain ⟨t, hzt, htz⟩ := exists_rat_btwn (show z < z + ((b : ℝ) - a) ^ 2 / 8 by linarith)
  refine ⟨a, b, c, t, hab.le, (hay.trans_le hyz).le.trans hzt.le, ?_, hxa, hby,
    hyz.trans_lt hzt, hcz, hzt⟩
  nlinarith

lemma gg_no_ordered_crossing (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, ¬ (Q 0 1 < Q 0 2 ∧ Q 0 2 ≤ Q 1 2) := by
  have hBoxes : ∀ᵐ Q ∂μ, ∀ a b c t : ℚ,
      (a : ℝ) ≤ b → (a : ℝ) ≤ t → 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2 →
      Q ∉ triangleEvent a b c t := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro c
    apply ae_all_iff.mpr
    intro t
    by_cases hab : (a : ℝ) ≤ b
    · by_cases hat : (a : ℝ) ≤ t
      · by_cases hgap : 2 * ((t : ℝ) - c) < ((b : ℝ) - a) ^ 2
        · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
            (gg_triangleEvent_null μ hEx hGG hSym hGram hdiag hab hat hgap)] with Q hQ
          exact fun _ _ _ => hQ
        · exact Eventually.of_forall fun _ _ _ h => (hgap h).elim
      · exact Eventually.of_forall fun _ _ h => (hat h).elim
    · exact Eventually.of_forall fun _ h => (hab h).elim
  filter_upwards [hBoxes] with Q hQ
  rintro ⟨hxy, hyz⟩
  obtain ⟨a, b, c, t, hab, hat, hgap, hbox⟩ := exists_rational_triangle_box hxy hyz
  exact hQ a b c t hab hat hgap hbox

lemma gram_array_symmetric (Q : OverlapArray)
    (hGram : ∀ n, Matrix.PosSemidef (overlapBlock id n Q)) : ∀ i j, Q i j = Q j i := by
  intro i j
  let n := max i j + 1
  let a : Fin n := ⟨i, by dsimp [n]; omega⟩
  let b : Fin n := ⟨j, by dsimp [n]; omega⟩
  have h := (hGram n).isHermitian.apply b a
  simpa [overlapBlock, a, b] using h

theorem gg_ultrametric (μ : Measure OverlapArray) [IsProbabilityMeasure μ]
    (hEx : OverlapSwapInvariant μ) (hGG : GhirlandaGuerra μ id)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n Q))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, Q i i ≤ 1) :
    ∀ᵐ Q ∂μ, min (Q 0 1) (Q 0 2) ≤ Q 1 2 := by
  have hSym : ∀ᵐ Q ∂μ, ∀ i j, Q i j = Q j i :=
    hGram.mono fun Q hQ => gram_array_symmetric Q hQ
  have hno := gg_no_ordered_crossing μ hEx hGG hSym hGram hdiag
  have hno' := (hEx 0 1).quasiMeasurePreserving.ae hno
  have hsmall : ∀ᵐ Q ∂μ, min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
    filter_upwards [hno, hno', hSym] with Q hQ hQ' hs
    simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
      show Equiv.swap (0 : ℕ) 1 2 = 2 from by decide] at hQ'
    rw [hs 1 0] at hQ'
    by_cases h : Q 0 2 ≤ Q 1 2
    · rw [min_eq_left h]
      exact le_of_not_gt fun hh => hQ ⟨hh, h⟩
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h']
      exact le_of_not_gt fun hh => hQ' ⟨hh, h'⟩
  have hsmall' := (hEx 0 2).quasiMeasurePreserving.ae hsmall
  filter_upwards [hsmall', hSym] with Q hQ hs
  simp only [relabelArray, Equiv.swap_apply_left, Equiv.swap_apply_right,
    show Equiv.swap (0 : ℕ) 2 1 = 1 from by decide] at hQ
  simpa only [hs 2 0, hs 1 0, hs 2 1, min_comm] using hQ

lemma scalarArray_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (scalarArray f) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarBlock_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) {n : ℕ} :
    Measurable (scalarBlock f (n := n)) := by
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    hf.comp ((measurable_pi_apply _).comp (measurable_pi_apply _))

lemma scalarArray_swap_invariant (μ : Measure PairedOverlapArray)
    (hEx : PairedSwapInvariant μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    OverlapSwapInvariant (μ.map (scalarArray f)) := by
  intro i j
  have heq : relabelArray (Equiv.swap i j) ∘ scalarArray f =
      scalarArray f ∘ pairedRelabel (Equiv.swap i j) := rfl
  refine ⟨Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _), ?_⟩
  rw [Measure.map_map _ (scalarArray_measurable hf), heq,
    ← Measure.map_map (scalarArray_measurable hf) (hEx i j).measurable,
    (hEx i j).map_eq]
  exact Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

lemma scalarArray_gg (μ : Measure PairedOverlapArray)
    (hGG : JointGhirlandaGuerra μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    GhirlandaGuerra (μ.map (scalarArray f)) id := by
  intro n hn i s hs t ht
  have hblock : Measurable (overlapBlock (id : OverlapArray → OverlapArray) n) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
      (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hedge (i j : ℕ) : Measurable (fun Q : OverlapArray => Q i j) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hmap (u : Set OverlapArray) (hu : MeasurableSet u) :
      (μ.map (scalarArray f)).real u = μ.real (scalarArray f ⁻¹' u) := by
    rw [measureReal_def, Measure.map_apply (scalarArray_measurable hf) hu]
    rfl
  simp only [id_eq]
  rw [hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i n ∈ t})
      ((hs.preimage hblock).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hblock), hmap {Q | Q 0 1 ∈ t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (overlapBlock id n ⁻¹' s ∩ {Q | Q i j ∈ t})
    ((hs.preimage hblock).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact hGG n hn i (scalarBlock f ⁻¹' s) (hs.preimage (scalarBlock_measurable hf))
    (f ⁻¹' t) (ht.preimage hf)

lemma measurableSet_gram_arrays :
    MeasurableSet {Q : OverlapArray | ∀ n, Matrix.PosSemidef (overlapBlock id n Q)} := by
  apply IsClosed.measurableSet
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro n
  have hiff (Q : OverlapArray) :=
    Matrix.posSemidef_iff_dotProduct_mulVec (M := overlapBlock id n Q)
  simp_rw [hiff]
  simp only [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {Q : OverlapArray | Matrix.conjTranspose (overlapBlock id n Q) = overlapBlock id n Q}
    apply isClosed_eq <;> unfold overlapBlock <;> fun_prop
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold overlapBlock
    fun_prop

lemma scalarArray_ultrametric (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hEx : PairedSwapInvariant μ) (hGG : JointGhirlandaGuerra μ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, min (f (Q 0 1)) (f (Q 0 2)) ≤ f (Q 1 2) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hu := gg_ultrametric ν (scalarArray_swap_invariant μ hEx hf)
    (scalarArray_gg μ hGG hf) hg hd
  exact ae_of_ae_map hm.aemeasurable hu

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGibbsArray_closed_full (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0)
    {F : Set (CompactArray CompactJointOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1)×IndexedLeaf k, sourceJointArray x ∈ F) :
    sourceGibbsArrayLaw n k f p d h u z t F=1 := by
  have hp : (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) _) F=1
  rw [Measure.map_apply (show Measurable (fun a : (SourceBaseData n k × (ℕ→ℝ)) ×
      (ℕ → NormalizedSpin (n+1) × IndexedLeaf k) => sourceJointArray a.2) from
      (sourceJointArray_measurable (n+1) k).comp measurable_snd) hF.measurableSet,hp]
  exact measure_univ

lemma compact_spin_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma compact_tree_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactJointOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma sourceGibbsArray_limit_gram (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ r, Matrix.PosSemidef (fun i j : Fin r => (Q i j).2.val)) := by
  constructor
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_spin_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_spin_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_spin_gram_closed r) (fun x => sourceSpinArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
  · rw [ae_all_iff]
    intro r
    apply (mem_ae_iff_prob_eq_one (compact_tree_gram_closed r).measurableSet).mpr
    have hv := weak_limit_closed_full hlim (compact_tree_gram_closed r)
      (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
        (compact_tree_gram_closed r) (fun x => sourceTreeArray_posSemidef x r))
    simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactGGEvents
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma compactGG_events (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (n : ℕ) (hn : 0<n) (i : Fin n)
    (hGG : ∀ (f : CompactBlock CompactJointOverlap n →ᵇ ℝ) (g : CompactJointOverlap →ᵇ ℝ),
      compactGGDefect μ n i f g=0)
    (s : Set (CompactBlock CompactJointOverlap n)) (hs : MeasurableSet s)
    (t : Set CompactJointOverlap) (ht : MeasurableSet t) :
    (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t}/n+
      (∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}))/n := by
  classical
  have he := congrArg (fun ρ : Measure (CompactBlock CompactJointOverlap n × CompactJointOverlap) =>
    ρ.real (s×ˢt)) (compactGG_joint_law μ hn i hGG)
  have hb := (compactBlock_continuous (K:=CompactJointOverlap) n).measurable
  have hm (i j : ℕ) : Measurable (fun Q : CompactArray CompactJointOverlap => Q i j) := by fun_prop
  rw [map_measureReal_apply (hb.prodMk (hm _ _)) (hs.prod ht),
    measureReal_nnreal_smul_apply,measureReal_add_apply] at he
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (μ : Measure _).map (fun Q => (compactBlock n Q,Q i j))).real (s×ˢt) =
      ∑ j ∈ Finset.univ.erase i, (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i j∈t}) := by
    simp only [measureReal_def,Measure.finsetSum_apply]
    rw [ENNReal.toReal_sum (by intro _ _; finiteness)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Measure.map_apply (hb.prodMk (hm _ _)) (hs.prod ht)]
    rfl
  rw [hsum] at he
  have hprod : (((μ : Measure _).map (compactBlock n)).prod
      ((μ : Measure _).map (fun Q : CompactArray CompactJointOverlap => Q 0 1))).real (s×ˢt) =
      (μ : Measure _).real (compactBlock n ⁻¹' s)*(μ : Measure _).real {Q : CompactArray CompactJointOverlap | Q 0 1∈t} := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      Measure.map_apply hb hs,Measure.map_apply (hm 0 1) ht]
    rfl
  rw [hprod] at he
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at he
  change (μ : Measure _).real (compactBlock n ⁻¹' s ∩ {Q | Q i n∈t}) = (n:ℝ)⁻¹*(_+_) at he
  rw [he]
  ring

lemma compactPairReal_measurable : Measurable compactPairReal := by unfold compactPairReal; fun_prop
lemma compactArrayReal_measurable : Measurable compactArrayReal := by
  unfold compactArrayReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))
lemma compactBlockReal_measurable (n : ℕ) : Measurable (compactBlockReal (n:=n)) := by
  unfold compactBlockReal; exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    compactPairReal_measurable.comp ((measurable_pi_apply column).comp (measurable_pi_apply row))

instance compactRealLaw_probability (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure (compactRealLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff compactArrayReal_measurable.aemeasurable).2 inferInstance

lemma compactRealLaw_gg (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0) :
    JointGhirlandaGuerra (compactRealLaw μ) := by
  intro n hn i s hs t ht
  have hb : Measurable (pairedBlock n) := by unfold pairedBlock; fun_prop
  have hedge (a b : ℕ) : Measurable (fun Q : PairedOverlapArray => Q a b) := by fun_prop
  have hmap (u : Set PairedOverlapArray) (hu : MeasurableSet u) :
      (compactRealLaw μ).real u=(μ : Measure _).real (compactArrayReal ⁻¹' u) :=
    map_measureReal_apply compactArrayReal_measurable hu
  rw [hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i n∈t}) ((hs.preimage hb).inter (ht.preimage (hedge i n))),
    hmap _ (hs.preimage hb), hmap {Q | Q 0 1∈t} (ht.preimage (hedge 0 1))]
  have hmj (j : Fin n) := hmap (pairedBlock n ⁻¹' s ∩ {Q | Q i j∈t})
    ((hs.preimage hb).inter (ht.preimage (hedge i j)))
  simp_rw [hmj]
  exact compactGG_events μ n (by omega) i (hGG n i)
    (compactBlockReal ⁻¹' s) (hs.preimage (compactBlockReal_measurable n))
    (compactPairReal ⁻¹' t) (ht.preimage compactPairReal_measurable)

lemma compactRealLaw_exchangeable (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _)) :
    PairedSwapInvariant (compactRealLaw μ) := by
  intro i j
  have hp : Measurable (pairedRelabel (Equiv.swap i j)) := by unfold pairedRelabel; fun_prop
  refine ⟨hp,?_⟩
  unfold compactRealLaw
  rw [Measure.map_map hp compactArrayReal_measurable]
  change Measure.map (compactArrayReal ∘ compactRelabel (Equiv.swap i j)) _ = _
  rw [← Measure.map_map compactArrayReal_measurable (hEx _).measurable,(hEx _).map_eq]

lemma compactRealLaw_diagonals (μ : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).1≤1) ∧
    (∀ᵐ Q ∂compactRealLaw μ, ∀ i, (Q i i).2≤1) := by
  constructor
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).1.property.2)
  · apply ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability) |>.mpr
    exact Filter.Eventually.of_forall (fun Q i => (Q i i).2.property.2)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepEntropy
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma stepCumulative_pos {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) (i : Fin k) :
    0 < stepCumulative w i := by
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> first | exact (hw j).le | rfl
  · exact ⟨0,Finset.mem_univ _,by simpa only [ite_eq_left (Fin.zero_le _)] using hw 0⟩

lemma stepCumulative_lt_one {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (i : Fin k) :
    stepCumulative w i < 1 := by
  rw [← hw1]
  apply Finset.sum_lt_sum
  · intro j _
    split_ifs <;> first | rfl | exact (hw j).le
  · refine ⟨Fin.last k,Finset.mem_univ _,?_⟩
    have hnot : ¬Fin.last k ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val,Fin.val_last,Fin.val_castSucc]
      omega
    simpa only [ite_eq_right hnot] using hw (Fin.last k)

lemma stepCumulative_strictMono {k : ℕ} (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) : StrictMono (stepCumulative w) := by
  intro i j hij
  apply Finset.sum_lt_sum
  · intro a _
    by_cases hai : a ≤ i.castSucc
    · have haj : a ≤ j.castSucc := hai.trans (Fin.castSucc_le_castSucc_iff.mpr hij.le)
      simp only [ite_eq_left hai,ite_eq_left haj,le_refl]
    · simp only [ite_eq_right hai]
      split_ifs <;> first | exact (hw a).le | rfl
  · refine ⟨j.castSucc,Finset.mem_univ _,?_⟩
    have hnot : ¬j.castSucc ≤ i.castSucc := by simpa only [Fin.castSucc_le_castSucc_iff] using not_le.mpr hij
    simpa only [ite_eq_right hnot,ite_eq_left le_rfl] using hw j.castSucc

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_SynchronizedLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

lemma source_contact_limit_exchangeable (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (ν : Measure _) (ν : Measure _) :=
  compact_exchangeability_limit hlim e (fun n => sourceGibbsArray_exchangeable
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) e)

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma scalarArray_nonnegative (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ) {f : ℝ×ℝ→ℝ} (hf : Measurable f)
    (hGram : ∀ᵐ Q ∂μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray f Q)))
    (hdiag : ∀ᵐ Q ∂μ, ∀ i, f (Q i i) ≤ 1) :
    ∀ᵐ Q ∂μ, 0 ≤ f (Q 0 1) := by
  let ν := μ.map (scalarArray f)
  have hm := scalarArray_measurable hf
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hg : ∀ᵐ Q ∂ν, ∀ n, Matrix.PosSemidef (overlapBlock id n Q) :=
    (ae_map_iff hm.aemeasurable measurableSet_gram_arrays).mpr hGram
  have hd : ∀ᵐ Q ∂ν, ∀ i, Q i i ≤ 1 :=
    (ae_map_iff hm.aemeasurable (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>  measurableSet_le
        ((measurable_pi_apply i).comp (measurable_pi_apply i)) measurable_const)).mpr hdiag
  have hs : ∀ᵐ Q ∂ν, ∀ i j, Q i j=Q j i := hg.mono fun Q hQ =>  gram_array_symmetric Q hQ
  have hp (n : ℕ) : ∀ᵐ Q ∂ν, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Q i j := by
    filter_upwards [hg] with Q hQ
    simpa [dotProduct,Matrix.mulVec,overlapBlock] using (hQ n).dotProduct_mulVec_nonneg (fun _ =>  (1:ℝ))
  have hn := gg_overlap_nonnegative ν (fun i j =>  by fun_prop) hs hd hp (scalarArray_gg μ hGG hf)
  exact ae_of_ae_map hm.aemeasurable hn

lemma compact_spin_nonnegative (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : JointGhirlandaGuerra (compactRealLaw ν))
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n =>  (Q i j).1.val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), 0 ≤ (Q 0 1).1.val := by
  have hr : ∀ᵐ Q ∂compactRealLaw ν, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst)) |>.mpr hR
  exact ae_of_ae_map compactArrayReal_measurable.aemeasurable
    (scalarArray_nonnegative (compactRealLaw ν) hGG measurable_fst hr (compactRealLaw_diagonals ν).1)


end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshReplicaKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

lemma freshReplicaMatrixKernel_gram (f : ℝ →ᵇ ℝ) (r : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin r→E) :
    freshReplicaMatrixKernel f r (Matrix.gram ℝ v)=
      ∫ z, gaussianReplicaTest f z ∂multivariateGaussian 0 (Matrix.gram ℝ v) :=
  (Classical.choose_spec (freshKernel_extension_exists f r)).2 (gramCovariance v)

lemma freshReplicaArrayKernel_tendsto {ν : ℕ→ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {ν₀ : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hν : Tendsto ν atTop (𝓝 ν₀)) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    Tendsto (fun n => ∫ Q, freshReplicaArrayKernel f r Q ∂ν n) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel f r Q ∂ν₀)) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (freshReplicaArrayKernel f r)).continuousAt.tendsto.comp hν

lemma freshPattern_moment_measurable_spins
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→E) (hv : Measurable v) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (∫ x, f (inner ℝ (v x) g) ∂μ)^r ∂stdGaussian E)=
      ∫ xs : Fin r→S, ∫ z, gaussianReplicaTest f z ∂multivariateGaussian 0
        (Matrix.gram ℝ (fun i => v (xs i))) ∂Measure.pi (fun _ => μ) := by
  classical
  let F : E×(Fin r→S)→ℝ := fun p => ∏ i, f (inner ℝ (v (p.2 i)) p.1)
  have hm : Measurable F := Finset.measurable_prod _ fun i _ => f.continuous.measurable.comp
    ((hv.comp ((measurable_pi_apply i).comp measurable_snd)).inner measurable_fst)
  have hb (p : E×(Fin r→S)) : ‖F p‖≤‖f‖^r := by
    simp only [F,norm_prod]
    exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => f.norm_coe_le_norm _)).trans_eq
      (by simp)
  have hi : Integrable F ((stdGaussian E).prod (Measure.pi fun _ : Fin r => μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _ = ∫ g, ∫ xs : Fin r→S, F (g,xs) ∂Measure.pi (fun _ => μ) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with g
      simpa only [F,Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin r) (fun x : S => f (inner ℝ (v x) g)) (μ := μ)).symm
    _ = ∫ xs : Fin r→S, ∫ g, F (g,xs) ∂stdGaussian E ∂Measure.pi (fun _ => μ) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with xs
      rw [← gaussianRows_map_stdGaussian (fun i => v (xs i)),
        integral_map (gaussianRows (fun i => v (xs i))).continuous.measurable.aemeasurable
          (gaussianReplicaTest f).continuous.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [F,gaussianReplicaTest_apply,gaussianRows_apply]

lemma freshPattern_gibbs_moment {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→E) (hv : Measurable v) (H : S→ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (tiltMean μ H (fun x => f (inner ℝ (v x) g)) 1)^r ∂stdGaussian E)=
      gibbsReplicaMean μ H r (fun xs => freshReplicaMatrixKernel f r
        (Matrix.gram ℝ (fun i => v (xs i)))) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  simp_rw [← tilt_law_integral_of_integrable μ hH he1]
  rw [gibbsReplicaMean_integral_of_integrable μ hH he,
    freshPattern_moment_measurable_spins (tiltLaw μ H 1) v hv f r]
  apply integral_congr_ae
  exact ae_of_all _ fun xs => (freshReplicaMatrixKernel_gram f r (fun i => v (xs i))).symm

lemma sourceFreshMoment_array (n k : ℕ) (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    sourceFreshMoment n k f ψ p d h u z t r=
      ∫ Q, freshReplicaArrayKernel ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t := by
  let F : CompactBlock CompactJointOverlap r→ᵇ ℝ :=
    (freshReplicaMatrixKernel ψ r).compContinuous
      ⟨fun Q => fun i j : Fin r => (Q i j).1.val,by fun_prop⟩
  have hblock := sourceGibbsArray_block_integral n k f p d h hh0 hh u z t r F.measurable
    (fun Q => F.norm_coe_le_norm Q)
  change (∫ Q, freshReplicaArrayKernel ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t)=_ at hblock
  rw [hblock]
  unfold sourceFreshMoment
  apply integral_congr_ae
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  have he : Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
      (sourceFullSpinLeafKernel n k a) := by
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  have hv : Measurable (fun x : NormalizedSpin (n+1)×IndexedLeaf k => x.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  rw [freshPattern_gibbs_moment _ _ hv _ (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left he]
  rfl

theorem sourceFreshMoment_tendsto (k : ℕ) (f ψ : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (r : ℕ) :
    Tendsto (fun n => sourceFreshMoment (s n) k f ψ (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n)) r) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel ψ r Q ∂ν)) := by
  simp_rw [sourceFreshMoment_array _ _ _ _ _ _ _ (hh0 _) (hh _)]
  exact freshReplicaArrayKernel_tendsto hlim ψ r

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshThermalLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section

lemma freshPartitionClip_eq (f : ℝ →ᵇ ℝ) {x : ℝ} (hx : x∈FreshPartitionRange f) :
    (freshPartitionClip f x).val=x := by
  dsimp [freshPartitionClip]
  rw [min_eq_right hx.2,max_eq_right hx.1]

variable {A S E : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A→S→ℝ) (hH : Measurable (Function.uncurry H))
variable (v : S→E) (hv : Measurable v) (f : ℝ →ᵇ ℝ)

include hH hv in
lemma freshThermalPartition_mem {a : A}
    (he : Integrable (fun x => Real.exp (H a x)) (κ a)) (g : E) :
    freshThermalPartition κ H v f (a,g)∈FreshPartitionRange f := by
  have he1 : Integrable (fun x => Real.exp (1*H a x)) (κ a) := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable (κ a) he1
  let μ := tiltLaw (κ a) (H a) 1
  have hm : Measurable (fun x => Real.exp (f (inner ℝ (v x) g))) :=
    (f.measurable.comp (hv.inner measurable_const)).exp
  have hi : Integrable (fun x => Real.exp (f (inner ℝ (v x) g))) μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp ‖f‖)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm _))
  have hb x := abs_le.mp (f.norm_coe_le_norm (inner ℝ (v x) g))
  unfold freshThermalPartition
  rw [← tilt_law_integral_of_integrable (κ a) hH.of_uncurry_left he1]
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-‖f‖))) hi (fun x => Real.exp_le_exp.mpr (hb x).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hi (integrable_const (Real.exp ‖f‖)) (fun x => Real.exp_le_exp.mpr (hb x).2)

lemma freshThermalLaw_integral (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a))
    (F : ℝ→ℝ) (hF : Measurable F) :
    (∫ x, F x.val ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, F (freshThermalPartition κ H v f a) ∂P.prod (stdGaussian E) := by
  change (∫ x : FreshPartitionRange f, F x.val ∂(P.prod (stdGaussian E)).map
    (fun a => freshPartitionClip f (freshThermalPartition κ H v f a)))=_
  have hmap := integral_map (μ := P.prod (stdGaussian E))
    (f := fun x : FreshPartitionRange f => F x.val)
    (φ := fun a => freshPartitionClip f (freshThermalPartition κ H v f a))
    (((freshPartitionClip_measurable f).comp
      (freshThermalPartition_measurable κ H hH v hv f)).aemeasurable)
    ((hF.comp measurable_subtype_coe).aestronglyMeasurable)
  refine hmap.trans ?_
  apply integral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he] with a ha
  rw [freshPartitionClip_eq f (freshThermalPartition_mem κ H hH v hv f ha a.2)]

include hH hv in
lemma freshThermalPartition_power_integrable (r : ℕ) :
    Integrable (fun a => freshThermalPartition κ H v f a^r) (P.prod (stdGaussian E)) := by
  apply Integrable.of_bound ((freshThermalPartition_measurable κ H hH v hv f).pow_const r).aestronglyMeasurable
    ((Real.exp ‖f‖)^r)
  apply ae_of_all
  intro a
  rw [norm_pow,Real.norm_eq_abs]
  apply pow_le_pow_left₀ (abs_nonneg _)
  apply tiltMean_bound_general (κ a.1) hH.of_uncurry_left
    ((f.measurable.comp (hv.inner measurable_const)).exp) (Real.exp_pos _).le
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((abs_le.mp (f.norm_coe_le_norm _)).2)

lemma freshThermalLaw_moment (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) :
    (∫ x, x.val^r ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, (tiltMean (κ a) (H a) (fun x => expBCF 1 f (inner ℝ (v x) g)) 1)^r
        ∂stdGaussian E ∂P := by
  rw [freshThermalLaw_integral κ P H hH v hv f he (fun x => x^r) (by fun_prop),
    integral_prod _ (freshThermalPartition_power_integrable κ P H hH v hv f r)]
  simp only [freshThermalPartition,expBCF_apply,one_mul]

include hH hv in
lemma freshThermalPartition_log_integrable
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    Integrable (fun a => Real.log (freshThermalPartition κ H v f a)) (P.prod (stdGaussian E)) := by
  apply Integrable.of_bound
    ((freshThermalPartition_measurable κ H hH v hv f).log).aestronglyMeasurable ‖f‖
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he] with a ha
  have hb := freshThermalPartition_mem κ H hH v hv f ha a.2
  have hpos : 0<freshThermalPartition κ H v f a := (Real.exp_pos _).trans_le hb.1
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hb.1
  · simpa only [Real.log_exp] using Real.log_le_log hpos hb.2

lemma freshThermalLaw_log (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    (∫ x, Real.log x.val ∂(freshThermalLaw κ P H hH v hv f : Measure (FreshPartitionRange f)))=
      ∫ a, ∫ g, Real.log (tiltMean (κ a) (H a)
        (fun x => Real.exp (f (inner ℝ (v x) g))) 1) ∂stdGaussian E ∂P := by
  rw [freshThermalLaw_integral κ P H hH v hv f he _ Real.measurable_log,
    integral_prod _ (freshThermalPartition_log_integrable κ P H hH v hv f he)]
  rfl

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BackwardScore
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma Jet3.lipschitz (g : Jet3) : LipschitzWith ‖g.d1‖₊ g.f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (g.has1 x).differentiableAt)
  intro x
  rw [g.deriv_eq]
  exact_mod_cast g.d1.norm_coe_le_norm x

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_moment_limit {a b : ℝ} (μ : ℕ→ProbabilityMeasure (Icc a b))
    (mom : ℕ→ℝ)
    (hmom : ∀ r, Tendsto (fun n => ∫ x, x.val^r ∂(μ n : Measure (Icc a b))) atTop (𝓝 (mom r))) :
    ∃ ν : ProbabilityMeasure (Icc a b), Tendsto μ atTop (𝓝 ν) ∧
      ∀ r, (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
  obtain ⟨ν, -, s, hs, hsub⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (μ n))
  have hm r : (∫ x, x.val^r ∂(ν : Measure (Icc a b)))=mom r := by
    let F : Icc a b→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => x.val^r,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hsub
    have h₂ := (hmom r).comp hs.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  refine ⟨ν,?_,hm⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  apply integral_continuous_tendsto_of_moments (fun n => (μ n : Measure (Icc a b)))
    (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
  rw [hm]
  exact hmom r


lemma sourceFresh_exp_ae (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0

lemma sourceFreshPartitionLaw_moment (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    (∫ x, x.val^r ∂(sourceFreshPartitionLaw n k f p d h u z t : Measure (FreshPartitionRange f)))=
      sourceFreshMoment n k f (expBCF 1 f) p d h u z t r :=
  freshThermalLaw_moment _ _ _ _ _ _ _ (sourceFresh_exp_ae n k f p d h hh0 hh u z t) r

lemma sourceFreshPartitionLaw_log (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    (∫ x, Real.log x.val ∂(sourceFreshPartitionLaw n k f p d h u z t : Measure (FreshPartitionRange f)))=
      sourceFreshLog n k f p d h u z t :=
  freshThermalLaw_log _ _ _ _ _ _ _ (sourceFresh_exp_ae n k f p d h hh0 hh u z t)

theorem sourceFreshLog_tendsto (k : ℕ) (f : ℝ →ᵇℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (FreshPartitionRange f),
      Tendsto (fun n => sourceFreshPartitionLaw (s n) k f (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 η) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 f) r Q ∂ν) ∧
      Tendsto (fun n => sourceFreshLog (s n) k f (p (s n)) (d (s n))
        (h (s n)) (u (s n)) z (t (s n))) atTop
        (𝓝 (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange f)))) := by
  have hmom r := sourceFreshMoment_tendsto k f (expBCF 1 f) p d h hh0 hh u z t s hlim r
  simp_rw [← sourceFreshPartitionLaw_moment _ _ _ _ _ _ (hh0 _) (hh _)] at hmom
  obtain ⟨η,hη,hm⟩ := compact_moment_limit _ _ hmom
  refine ⟨η,hη,hm,?_⟩
  have hlog : Continuous (fun x : FreshPartitionRange f => Real.log x.val) :=
    continuous_subtype_val.log fun x => ne_of_gt ((Real.exp_pos _).trans_le x.prop.1)
  let F : FreshPartitionRange f→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨_,hlog⟩
  have ht := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hη
  change Tendsto (fun n => ∫ x, Real.log x.val ∂(sourceFreshPartitionLaw (s n) k f (p (s n))
    (d (s n)) (h (s n)) (u (s n)) z (t (s n)) : Measure (FreshPartitionRange f))) atTop _ at ht
  simpa only [F,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,sourceFreshPartitionLaw_log _ _ _ _ _ _ (hh0 _) (hh _)] using ht

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compact_gg_spin_geometry (μ : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hEx : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e) (μ : Measure _) (μ : Measure _))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock CompactJointOverlap n →ᵇ ℝ)
      (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect μ n i f g=0)
    (hR : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ n, Matrix.PosSemidef (fun i j : Fin n => (Q i j).1.val))
    (hdiag : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _), ∀ i, (Q i i).1.val=1) :
    ∀ᵐ Q ∂(μ : Measure _), CompactSpinGeometry Q := by
  have hg : ∀ᵐ Q ∂compactRealLaw μ, ∀ n, Matrix.PosSemidef (overlapBlock id n (scalarArray Prod.fst Q)) :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (measurableSet_gram_arrays.preimage
      (scalarArray_measurable measurable_fst))).mpr hR
  have hu := scalarArray_ultrametric (compactRealLaw μ) (compactRealLaw_exchangeable μ hEx)
    (compactRealLaw_gg μ hGG) measurable_fst hg (compactRealLaw_diagonals μ).1
  have hbase : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q 0 1).1.val (Q 0 2).1.val ≤ (Q 1 2).1.val :=
    (ae_map_iff compactArrayReal_measurable.aemeasurable (by measurability)).mp hu
  have hdistinct (i j k : ℕ) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (fun a : Fin 3 => a.val) g Fin.val_injective hg
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    change e 0=i at h0
    change e 1=j at h1
    change e 2=k at h2
    have hh := (hEx e).quasiMeasurePreserving.ae hbase
    simpa only [compactRelabel,h0,h1,h2] using hh
  have hall : ∀ᵐ Q : CompactArray CompactJointOverlap ∂(μ : Measure _),
      ∀ i j k, i≠j → i≠k → j≠k → min (Q i j).1.val (Q i k).1.val ≤ (Q j k).1.val := by
    simp only [ae_all_iff]
    exact hdistinct
  filter_upwards [hR,hdiag,hall] with Q hQ hd hu
  have hs : ∀ i j, (Q i j).1.val=(Q j i).1.val :=
    gram_array_symmetric (fun i j => (Q i j).1.val) hQ
  refine ⟨hs,hd,?_⟩
  intro i j k
  by_cases hij : i=j
  · subst j
    exact min_le_right _ _
  by_cases hik : i=k
  · subst k
    rw [hs j i]
    exact min_le_left _ _
  by_cases hjk : j=k
  · subst k
    rw [hd j,min_self]
    exact (Q i j).1.property.2
  exact hu i j k hij hik hjk

lemma sourceGibbsArray_limit_spin_diagonal (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (u : (n : ℕ) → Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℕ → ℝ≥0)
    (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(ν : Measure _), ∀ i, (Q i i).1.val=1 := by
  rw [ae_all_iff]
  intro i
  have hc : IsClosed {Q : CompactArray CompactJointOverlap | (Q i i).1.val=1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc
    (fun n => sourceGibbsArray_closed_full (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n))
      hc (fun x => sourceJointArray_diagonal x i))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma source_contact_limit_spin_geometry (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ → ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ) → Fin (n+1) → ℝ)
    (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
    {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
  apply compact_gg_spin_geometry ν
    (source_contact_limit_exchangeable k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)
    (source_contact_limit_joint_gg k f p d z hz hz0 hz1 t h hh0 hh u hu hmin hH hhH ht hs hlim hcover)
    (sourceGibbsArray_limit_gram k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim).1
    (sourceGibbsArray_limit_spin_diagonal k f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Control_FreshControl
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem source_contact_freshLog_control (k : ℕ) (g : Jet3) (p d : ℕ → ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ) → Fin (n+1) → ℝ)
    (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k g.f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
    {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    Tendsto (fun n => sourceFreshLog (s n) k g.f (fun a => p a.val) (fun a => d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop
      (𝓝 (controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))))) := by
  obtain ⟨η,hη,hm,hl⟩ := sourceFreshLog_tendsto k g.f (fun _ a => p a.val) (fun _ a => d a.val)
    h hh0 hh u z t s hlim
  have hGG := source_contact_limit_joint_gg k g.f p d z hz hz0 hz1 t h hh0 hh u hu hmin
    hH hhH ht hs hlim hcover
  have hgeo := source_contact_limit_spin_geometry k g.f p d z hz hz0 hz1 t h hh0 hh u hu hmin
    hH hhH ht hcover hs hlim
  have hn := compact_spin_nonnegative ν (compactRealLaw_gg ν hGG)
    (sourceGibbsArray_limit_gram k g.f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim).1
  rwa [compactGG_freshLog_control ν hGG hgeo hn g η hm P hB] at hl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Field
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasurePatternsPatternLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedPatternLog_source (α β : ℝ) (φ : ℝ →ᵇ ℝ) (n : ℕ)
    (g : Patterns α (n+1)) :
    (1/(n+1:ℕ))*normalizedPatternLog n (patternCount α (n+1)) (β • φ) g=
      pressure α β φ (n+1) g := by
  unfold pressure sphereLaw
  rw [integral_map (by fun_prop) (by
    apply Continuous.aestronglyMeasurable
    unfold hamiltonian patternField
    fun_prop)]
  simp_rw [← normalizedPatternEnergy_source α β φ n g]
  unfold normalizedPatternLog
  ring

lemma normalizedPatternLog_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ) :
    Measurable (normalizedPatternLog n M f) := by
  have hm := (Real.continuous_exp.comp (normalizedPatternEnergy_continuous (n+1) M f)).measurable
  exact Real.measurable_log.comp hm.stronglyMeasurable.integral_prod_right'.measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTelescoping
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma normalizedPatternLog_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (normalizedPatternLog n M f) (finitePatternRowsLaw (n+1) M) := by
  apply Integrable.of_bound (normalizedPatternLog_measurable n M f).aestronglyMeasurable (M*‖f‖)
  filter_upwards [] with a
  rw [Real.norm_eq_abs]
  simpa only [normalizedPatternLog,tiltPartition,one_mul,Function.comp_apply,id_eq] using
    tilt_log_partition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (by positivity : 0≤M*‖f‖) (normalizedPatternEnergy_bound _ _ _ a)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_FixedCount
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceCountKernel_apply (n k : ℕ) (a : SourceCountData n k) :
    sourceCountKernel n k a=enrichedIndexedBaseMeasure n k a.2.1 := by
  simp only [sourceCountKernel,Kernel.comap_apply,sourceFullSpinLeafKernel,sourceCountEmbedding,
    sourceSpinLeafKernel_apply]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshDensity
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceDisorderUnassoc_preserving (n k : ℕ) (z : Fin k→ℝ) (t : ℝ≥0) :
    MeasurePreserving (sourceDisorderUnassoc n k) (sourceIndexedDisorderLaw n k z t)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  let K := poissonMeasure ((n+1:ℕ)*t)
  let R := infinitePatternRowsLaw (n+1)
  let B := (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))
  exact (measurePreserving_prodAssoc K (R.prod B) countableGaussianLaw).symm.comp
    ((MeasurePreserving.id K).prod (measurePreserving_prodAssoc R B countableGaussianLaw).symm)

theorem sourceDensityIncrement_eq_fresh (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    sourceDensityIncrement n k f p d h z u t=sourceFreshLog n k f p d h u z t := by
  let J := fun a : SourceBaseData n k × (ℕ→ℝ) =>
    ∫ g, Real.log (freshThermalPartition (sourceFullSpinLeafKernel n k)
      (sourceCouplingHamiltonian n k f p d h u) (fun x => x.1.val) f (a,g))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
  have hi := freshThermalPartition_log_integrable (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceCouplingHamiltonian_measurable n k f p d h u)
    (fun x => x.1.val) (measurable_subtype_coe.comp measurable_fst) f
    (sourceFresh_exp_ae n k f p d h hh0 hh u z t)
  have hj : Integrable J ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) :=
    hi.integral_prod_left
  have hp := sourceDisorderUnassoc_preserving n k z t
  have he (M : ℕ) (a : SourceCountData n k) : J (sourceDisorderUnassoc n k (M,a))=
      ∫ g, Real.log (freshThermalPartition (sourceCountKernel n k)
        (sourceCountHamiltonian n M k f p d h u) (fun x => x.1.val) f (a,g))
          ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1))) := by
    apply integral_congr_ae
    exact ae_of_all _ fun g => by
      simp only [freshThermalPartition,sourceFullSpinLeafKernel,Kernel.comap_apply,
        sourceSpinLeafKernel_apply,sourceCountKernel_apply]
      rfl
  rw [sourceDensityIncrement]
  simp_rw [sourceCountExpectedLog_fresh n _ k f p d h hh0 hh u z hz hz0 hz1,← he]
  change (∫ M, ∫ a, J (sourceDisorderUnassoc n k (M,a)) ∂sourceCountLaw n k z
    ∂poissonMeasure ((n+1:ℕ)*t))=_
  calc
    _=(∫ a, J (sourceDisorderUnassoc n k a) ∂sourceIndexedDisorderLaw n k z t) := by
      simpa only [Function.comp_def,sourceCountLaw,sourceIndexedDisorderLaw] using
        (integral_prod _ (hp.integrable_comp_of_integrable hj)).symm
    _=sourceFreshLog n k f p d h u z t := ?_
  have hmap := integral_map (φ := sourceDisorderUnassoc n k) (f := J) hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact hj.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  exact hmap.symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GlobalContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma source_global_contact_perturbation_min (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q hw hw1 δ)
      (sourceContactCompactDomain n k α H) a) :
    IsMinOn (fun u => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
      sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u)
      (Icc (fun _ => 1) (fun _ => 2)) a.2.2 := by
  intro u hu
  change quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2 ≤
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u-
    sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u
  have he := hmin (show (a.1,a.2.1,u)∈sourceContactCompactDomain n k α H from
    ⟨ha.1,ha.2.1,hu⟩)
  unfold sourceStepContactObjective sourceJointPressure at he
  change -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 a.2.2-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) a.2.2 ≤
    -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w) a.1 u-
    (∑ i, w i*(q i:ℝ)*a.2.1 i)+(entropy (weightedStepTrial w q hw hw1)).toReal+
    (a.1:ℝ)*(controlValue P f (weightedStepTrial w q hw hw1)+δ)+
    quadraticBoxPenalty (sourcePenaltyWeight (n+1)) u at he
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BoundaryEstimate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma perturbationScale_tendsto_zero :
    Tendsto (fun n : ℕ => perturbationScale (n+1)) atTop (𝓝 0) := by
  unfold perturbationScale
  convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [neg_div]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UpperContact
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem sourceStepContactObjective_eventual_lower (k : ℕ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (p d : ℕ → ℕ)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    (w : Fin (k+1) → ℝ) (q r : Fin (k+1) → Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq1 : (q (Fin.last k):ℝ)<1) (hr : Monotone r) (hr1 : (r (Fin.last k):ℝ)<1)
    {η : ℝ} (hη : 0<η) (hqr : ∀ i, (q i:ℝ)+η≤(r i:ℝ))
    (α : ℝ≥0) (H : ℝ) (hH0 : 0≤H)
    (hH : (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
      2*(α:ℝ)*‖g.f‖ ≤ η*w (Fin.last k)*H)
    {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ sourceContactCompactDomain n k α H,
      -ε ≤ sourceStepContactObjective n k P g.f (fun i => p i.val) (fun i => d i.val)
        w q (fun i => (hw i).le) hw1 δ a := by
  choose c hc hm using fun n => source_global_contact_exists n k P g.f
    (fun i => p i.val) (fun i => d i.val) w q hw hw1 δ α hH0
  have hmin n := source_global_contact_perturbation_min n k P g.f
    (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ α H (hc n) (hm n)
  have he : ∀ᶠ n : ℕ in atTop, -ε ≤ sourceStepContactObjective n k P g.f
      (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ (c n) := by
    by_contra hnot
    have hf : ∃ᶠ n : ℕ in atTop, sourceStepContactObjective n k P g.f
        (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ (c n)< -ε := by
      simpa only [not_eventually,not_le] using hnot
    obtain ⟨v,hv,hneg⟩ := extraction_of_frequently_atTop hf
    obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n =>
      sourceGibbsArrayLaw (v n) k g.f (fun i => p i.val) (fun i => d i.val)
        (c (v n)).2.1 (c (v n)).2.2 (stepCumulative w) (c (v n)).1)
    let b := v ∘ s
    have hb : StrictMono b := hv.comp hs
    have hl : Tendsto (fun n => sourceGibbsArrayLaw (b n) k g.f
        (fun i => p i.val) (fun i => d i.val) (c (b n)).2.1 (c (b n)).2.2
          (stepCumulative w) (c (b n)).1) atTop (𝓝 ν) := hlim
    have ht : ∀ᶠ n in atTop, 0<(c (b n)).1 := by
      filter_upwards [hb.tendsto_atTop.eventually
        (sourceNegativeContact_positive_density w hw hw1 H hε)] with n hn
      exact hn P g.f _ _ q hq hq1 δ α (c (b n)) (hc (b n)) (hneg (s n))
    have hcap : ∀ᶠ n in atTop, (c (b n)).2.1 (Fin.last k)<H := by
      filter_upwards [hb.tendsto_atTop.eventually
        (sourceNegativeContact_field_interior w hw hw1 P g.f q r hr hr1 hη hqr α H hH hε)] with n hn
      exact hn _ _ δ hδ.le (c (b n)) (hc (b n)) (hneg (s n))
    have hord := source_global_contact_control_order_along k P g p d w q hw hw1 hq δ α H c
      hc hm hH0 hcover hb hl hcap hB
    have hfresh := source_contact_freshLog_control k g p d (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (fun n => (c n).1) (fun n => (c n).2.1) (fun n => (hc n).2.1.1.1)
      (fun n => (hc n).2.1.2) (fun n => (c n).2.2) (fun n => (hc n).2.2) hmin hH0
      (fun n => (hc n).2.1.1.2 0) (T := (α:ℝ)) (fun n => (hc n).1.2) hcover hb hl P hB
    have hderiv : controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ ≤
        controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) := by
      apply ge_of_tendsto hfresh
      filter_upwards [ht] with n hn
      rw [←sourceDensityIncrement_eq_fresh (b n) k g.f _ _ _
        (hc (b n)).2.1.1.1 (hc (b n)).2.1.2 _ _
        (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)]
      exact source_global_contact_density (b n) k P g.f _ _ w q hw hw1 δ α H (hc (b n)) (hm (b n)) hn
    linarith
  filter_upwards [he] with n hn
  intro a ha
  exact hn.trans (hm n ha)


lemma source_depoisson_error_tendsto (f : ℝ →ᵇ ℝ) (α : ℝ≥0) :
    Tendsto (fun n : ℕ => ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(α:ℝ))+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => (α:ℝ)/(n+1:ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h2 : Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have he (n : ℕ) : ‖f‖/(n+1:ℕ)*(Real.sqrt ((n+1:ℕ)*(α:ℝ))+1)=
      ‖f‖*(Real.sqrt ((α:ℝ)/(n+1:ℕ))+1/(n+1:ℕ)) := by
    have hn0 : (0:ℝ)<(n+1:ℕ) := by positivity
    have hs : Real.sqrt ((n+1:ℕ)*(α:ℝ))/(n+1:ℕ)=Real.sqrt ((α:ℝ)/(n+1:ℕ)) := by
      calc
        _ = Real.sqrt (((n+1:ℕ)*(α:ℝ))/((n+1:ℕ):ℝ)^2) := by
          rw [Real.sqrt_div (by positivity),Real.sqrt_sq hn0.le]
        _ = _ := by congr 1; field_simp
    calc
      _ = ‖f‖*(Real.sqrt ((n+1:ℕ)*(α:ℝ))/(n+1:ℕ)+1/(n+1:ℕ)) := by ring
      _ = _ := by rw [hs]
  simp_rw [he]
  simpa using (h1.sqrt.add h2).const_mul ‖f‖

theorem expectedPressure_upper_weightedStep (k : ℕ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
    (hq1 : (q (Fin.last k):ℝ)<1) (α : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal+
      (α:ℝ)*controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1)+ε := by
  let r : Fin (k+1)→Time := fun i => ⟨((q i:ℝ)+1)/2,by
    constructor <;> linarith [(q i).2.1,(q i).2.2]⟩
  have hr : Monotone r := by
    intro i j hij
    change ((q i:ℝ)+1)/2 ≤ ((q j:ℝ)+1)/2
    have he : (q i:ℝ)≤(q j:ℝ) := hq hij
    linarith
  have hr1 : (r (Fin.last k):ℝ)<1 := by dsimp [r]; linarith
  let η : ℝ := (1-(q (Fin.last k):ℝ))/2
  have hη : 0<η := by dsimp [η]; linarith
  have hqr i : (q i:ℝ)+η≤(r i:ℝ) := by
    have he : (q i:ℝ)≤(q (Fin.last k):ℝ) := hq (Fin.le_last i)
    dsimp [η,r]
    linarith
  let A := (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+2*(α:ℝ)*‖g.f‖
  let H := A/(η*w (Fin.last k))
  have hH0 : 0≤H := by
    apply div_nonneg _ (mul_pos hη (hw _)).le
    dsimp [A]
    positivity
  have hH : A≤η*w (Fin.last k)*H := by
    dsimp [H]
    rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos hη (hw _)))]
  let δ := ε/(4*((α:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hd : (α:ℝ)*δ≤ε/4 := by
    dsimp [δ]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hc : (α:ℝ)*ε≤ε*((α:ℝ)+1) := by nlinarith [α.coe_nonneg]
    have he : (α:ℝ)*(ε/(4*((α:ℝ)+1)))*4=(α:ℝ)*ε/((α:ℝ)+1) := by
      field_simp
    rw [he]
    exact (div_le_iff₀ (by positivity)).mpr hc
  let p : ℕ→ℕ := fun i => (Nat.unpair i).1
  let d : ℕ→ℕ := fun i => (Nat.unpair i).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  have hc := sourceStepContactObjective_eventual_lower k P hB g p d hcover w q r hw hw1
    hq hq1 hr hr1 hη hqr α H hH0 hH hδ (show 0<ε/4 by positivity)
  have ht : Tendsto (fun n : ℕ => 8*perturbationScale (n+1)^2) atTop (𝓝 0) := by
    simpa using perturbationScale_tendsto_zero.pow 2 |>.const_mul 8
  filter_upwards [hc,ht.eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity)),
    (source_depoisson_error_tendsto g.f α).eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity))]
    with n hn ht' he'
  have ha : (α,fun _ => 0,fun _ : Fin (n+1) => 3/2)∈sourceContactCompactDomain n k α H := by
    refine ⟨⟨zero_le,le_rfl⟩,⟨⟨fun _ => le_rfl,fun _ => hH0⟩,monotone_const⟩,?_⟩
    constructor <;> intro j <;> norm_num
  have hh := hn _ ha
  simp only [sourceStepContactObjective,sourceJointPressure,quadraticBoxPenalty,
    sub_self,zero_pow (by norm_num : 2≠0),mul_zero,Finset.sum_const_zero,sub_zero,add_zero] at hh
  have ho := source_zeroField_original_compare n k g.f (fun i => p i.val) (fun i => d i.val)
    (stepCumulative w) (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
    (stepCumulative_lt_one w hw hw1) α
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LevelTrialApprox
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma trialLevelQuantile_mono (m : Trial) (n : ℕ) : Monotone (trialLevelQuantile m n) := by
  intro i j hij
  apply le_sInf
  intro t ht
  apply sInf_le
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right
    (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij) (by positivity : (0:ℝ)≤n+1)) ht

lemma trialLevelQuantile_le (m : Trial) (n : ℕ) (i : Fin (n+1)) {t : Time}
    (ht : (i:ℝ)/(n+1:ℝ)< m t) : trialLevelQuantile m n i≤t := sInf_le ht

lemma trialLevelQuantile_lt (m : Trial) (n : ℕ) (i : Fin (n+1)) {t : Time}
    (ht : trialLevelQuantile m n i<t) : (i:ℝ)/(n+1:ℝ)< m t := by
  obtain ⟨s,hs,hst⟩ := sInf_lt_iff.mp ht
  exact hs.trans_le (m.monotone hst.le)

lemma uniform_threshold_sum (m : Trial) (n : ℕ) (t : Time) :
    (∑ i : Fin (n+1), if (i:ℝ)/(n+1:ℝ)< m t then (1/(n+1:ℝ)) else 0)=
      upperRoundedTrial m n t := by
  have hc : ⌈(n+1:ℝ)*m t⌉₊≤n+1 := Nat.ceil_le.mpr (by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [m.le_one t])
  have he (i : ℕ) : ((i:ℝ)/(n+1:ℝ)< m t) ↔ i<⌈(n+1:ℝ)*m t⌉₊ := by
    rw [div_lt_iff₀ (by positivity),Nat.lt_ceil]
    rw [mul_comm]
  simp_rw [he]
  change (∑ i : Fin (n+1), (fun j : ℕ => if j<⌈(n+1:ℝ)*m t⌉₊ then 1/(n+1:ℝ) else 0) i.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j<⌈(n+1:ℝ)*m t⌉₊ then 1/(n+1:ℝ) else 0) (n+1),←Finset.sum_filter]
  have hset : (Finset.range (n+1)).filter (fun i => i<⌈(n+1:ℝ)*m t⌉₊)=
      Finset.range ⌈(n+1:ℝ)*m t⌉₊ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hset,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  change _=(⌈((n+1:ℕ):ℝ)*m t⌉₊:ℝ)/(n+1:ℕ)
  simp only [Nat.cast_add,Nat.cast_one]
  ring

lemma le_levelStepTrial (m : Trial) (n : ℕ) (t : Time) : m t≤levelStepTrial m n t := by
  apply (le_upperRoundedTrial m n t).trans
  rw [←uniform_threshold_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : (i:ℝ)/(n+1:ℝ)< m t
  · simp only [ite_eq_left hi,ite_eq_left (trialLevelQuantile_le m n i hi),le_refl]
  · rw [ite_eq_right hi]
    split_ifs <;> positivity

lemma levelStepTrial_ae (m : Trial) (n : ℕ) :
    (fun t => levelStepTrial m n t)=ᵐ[timeLaw] (fun t => upperRoundedTrial m n t) := by
  have hn : ∀ᵐ t ∂timeLaw, ∀ i : Fin (n+1), t≠trialLevelQuantile m n i := by
    apply ae_all_iff.mpr
    intro i
    simp [ae_iff,timeLaw_eq_volume]
  filter_upwards [hn] with t ht
  rw [←uniform_threshold_sum]
  change (∑ i : Fin (n+1), if trialLevelQuantile m n i≤t then 1/(n+1:ℝ) else 0)=_
  apply Finset.sum_congr rfl
  intro i _
  have hi : trialLevelQuantile m n i≤t ↔ (i:ℝ)/(n+1:ℝ)< m t :=
    ⟨fun h => trialLevelQuantile_lt m n i (lt_of_le_of_ne h (Ne.symm (ht i))),trialLevelQuantile_le m n i⟩
  simp only [hi]

lemma levelStepTrial_L1 (m : Trial) (n : ℕ) :
    (∫ t, |levelStepTrial m n t-m t| ∂timeLaw)≤1/(n+1:ℝ) := by
  have he : (∫ t, |levelStepTrial m n t-m t| ∂timeLaw)=
      ∫ t, |upperRoundedTrial m n t-m t| ∂timeLaw :=
    integral_congr_ae ((levelStepTrial_ae m n).mono fun t ht => by dsimp only at ht ⊢; rw [ht])
  rw [he]
  simpa only [Nat.cast_add,Nat.cast_one] using upperRoundedTrial_L1_le m n

lemma trialLevelQuantile_terminal (m : Trial) (n : ℕ) {r : Time} (hr : m r=1)
    (i : Fin (n+1)) : trialLevelQuantile m n i ≤ r := by
  apply trialLevelQuantile_le
  rw [hr]
  apply (div_lt_one (by positivity : (0:ℝ)<n+1)).mpr
  exact_mod_cast i.isLt

theorem exists_uniform_step_trial_approx (m : Trial) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (q : Fin (n+1)→Time), Monotone q ∧ (q (Fin.last n):ℝ)<1 ∧
      let v := weightedStepTrial (fun _ : Fin (n+1) => 1/(n+1:ℝ)) q
        (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)
      (∀ t, m t≤v t) ∧ entropy v≤entropy m ∧
        (∫ t, |v t-m t| ∂timeLaw)<ε := by
  obtain ⟨u,hufin,⟨r,hr,hterm⟩,hmu,hS,_,hL⟩ :=
    exists_finite_terminal_trial_approx m (show 0<ε/2 by positivity)
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0<ε/2 by positivity)
  refine ⟨n,trialLevelQuantile u n,trialLevelQuantile_mono u n,
    lt_of_le_of_lt (trialLevelQuantile_terminal u n (hterm r le_rfl) _) hr,?_⟩
  change (∀ t, m t≤levelStepTrial u n t) ∧ entropy (levelStepTrial u n)≤entropy m ∧ _
  refine ⟨fun t => (hmu t).trans (le_levelStepTrial u n t),
    (entropy_antitone (le_levelStepTrial u n)).trans hS,?_⟩
  have hi : (∫ t, |levelStepTrial u n t-m t| ∂timeLaw) ≤
      (∫ t, |levelStepTrial u n t-u t| ∂timeLaw)+(∫ t, |u t-m t| ∂timeLaw) := by
    calc
      _ ≤ ∫ t, |levelStepTrial u n t-u t|+|u t-m t| ∂timeLaw :=
        integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
          (((trial_integrable _).sub (trial_integrable _)).abs.add
            ((trial_integrable _).sub (trial_integrable _)).abs) (fun t => abs_sub_le _ _ _)
      _ = _ := integral_add ((trial_integrable _).sub (trial_integrable _)).abs
        ((trial_integrable _).sub (trial_integrable _)).abs
  have hl := levelStepTrial_L1 u n
  change (∫ t, |levelStepTrial u n t-m t| ∂timeLaw)<ε
  linarith


 theorem expectedPressure_upper_trial
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (α : ℝ≥0) (m : Trial) (hm : entropy m≠∞) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (entropy m).toReal+(α:ℝ)*controlValue P g.f m+ε := by
  let C : ℝ := (α:ℝ)*(3/2)*‖g.d1‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨k,q,hq,hq1,_,hS,hL⟩ := exists_uniform_step_trial_approx m
    (show 0<ε/(2*(C+1)) by positivity)
  let v := weightedStepTrial (fun _ : Fin (k+1) => 1/(k+1:ℝ)) q
    (uniformQuantileWeights_nonneg k) (uniformQuantileWeights_sum k)
  have hv : ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1)≤
      (entropy v).toReal+(α:ℝ)*controlValue P g.f v+ε/2 :=
    expectedPressure_upper_weightedStep k P hB g _ q (fun _ => by positivity)
      (uniformQuantileWeights_sum k) hq hq1 α (show 0<ε/2 by positivity)
  have hS' : (entropy v).toReal≤(entropy m).toReal := ENNReal.toReal_mono hm hS
  have hc := mul_le_mul_of_nonneg_left
    (controlValue_trial_sub_le P g.f v m ‖g.d1‖₊ g.lipschitz) α.coe_nonneg
  have he : C*(∫ t, |v t-m t| ∂timeLaw)≤ε/2 := by
    calc
      _ ≤ C*(ε/(2*(C+1))) := mul_le_mul_of_nonneg_left hL.le hC
      _ ≤ ε/2 := by
        rw [←mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0<2*(C+1))).mpr
        nlinarith
  filter_upwards [hv] with n hn
  dsimp only [C] at he
  change (α:ℝ)*(controlValue P g.f v-controlValue P g.f m) ≤
    (α:ℝ)*((3/2)*‖g.d1‖^2*(∫ t, |v t-m t| ∂timeLaw)) at hc
  nlinarith

 theorem expectedPressure_upper_variational
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P)
    (g : Jet3) (α : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, expectedPressure (α:ℝ) 1 g.f (n+1) ≤
      (terminalVariational P (α:ℝ) g.f).toReal+ε := by
  have hi : terminalVariational P (α:ℝ) g.f <
      (((terminalVariational P (α:ℝ) g.f).toReal+ε/2:ℝ):EReal) := by
    rw [←terminalVariational_coe_toReal P (α:ℝ) α.coe_nonneg g.f,EReal.coe_lt_coe_iff]
    simp only [EReal.toReal_coe]
    linarith
  obtain ⟨m,hm⟩ := iInf_lt_iff.mp hi
  have hS : entropy m≠∞ := by
    intro h
    simp only [h,EReal.coe_ennreal_top,EReal.coe_add_top,not_top_lt] at hm
  rw [←EReal.coe_ennreal_toReal hS,←EReal.coe_add,EReal.coe_lt_coe_iff] at hm
  filter_upwards [expectedPressure_upper_trial P hB g α m hS (show 0<ε/2 by positivity)] with n hn
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem expectedPressure_limit_smooth (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) :
    Tendsto (fun n : ℕ=>expectedPressure α 1 g.f (n+1)) atTop
      (𝓝 (terminalVariational P α g.f).toReal) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [expectedPressure_lower_smooth P hB hα g h1 h2 h3 (show 0<ε/2 by positivity),
    expectedPressure_upper_variational P hB g ⟨α,hα.le⟩ (show 0<ε/2 by positivity)] with n hn hu
  change expectedPressure α 1 g.f (n+1) ≤ (terminalVariational P α g.f).toReal + ε/2 at hu
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_PressureMonotone
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma normalizedPatternLog_mono (n M : ℕ) (f g : ℝ→ᵇℝ)
    (hfg : ∀ x : ℝ, f x≤g x) (a : Fin M→Fin (n+1)→ℝ) :
    normalizedPatternLog n M f a≤normalizedPatternLog n M g a := by
  have hm (f : ℝ→ᵇℝ) : Measurable (normalizedPatternEnergy (n+1) M f a) :=
    ((normalizedPatternEnergy_continuous (n+1) M f).comp
      (show Continuous (fun x : NormalizedSpin (n+1)=>(a,x)) from continuous_const.prodMk continuous_id)).measurable
  have hi (f : ℝ→ᵇℝ) : Integrable
      (fun x=>Real.exp (normalizedPatternEnergy (n+1) M f a x)) (unitSphereLaw (n+1)) := by
    apply Integrable.of_bound (hm f).exp.aestronglyMeasurable (Real.exp (M*‖f‖))
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (normalizedPatternEnergy_bound _ _ _ a x))
  apply Real.log_le_log
  · simpa only [tiltPartition,one_mul] using tilt_partition_pos (unitSphereLaw (n+1))
      (hm f) (by positivity : 0≤M*‖f‖) (normalizedPatternEnergy_bound _ _ _ a) 1
  · apply integral_mono (hi f) (hi g)
    intro x
    apply Real.exp_le_exp.mpr
    unfold normalizedPatternEnergy
    exact Finset.sum_le_sum (fun j _=>hfg _)

lemma expectedPressure_mono_terminal (α : ℝ) (f g : ℝ→ᵇℝ)
    (hfg : ∀ x : ℝ,f x≤g x) (n : ℕ) :
    expectedPressure α 1 f (n+1)≤expectedPressure α 1 g (n+1) := by
  unfold expectedPressure
  simp_rw [←normalizedPatternLog_source α 1 _ n,one_smul]
  rw [integral_const_mul,integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono (normalizedPatternLog_integrable n _ f)
    (normalizedPatternLog_integrable n _ g) (normalizedPatternLog_mono n _ f g hfg)
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactEnvelope
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma exists_smooth_lower_envelope (f : ℝ→ᵇℝ) {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ g : Jet3,
      HasCompactSupport (g.d1 : ℝ→ℝ) ∧ HasCompactSupport (g.d2 : ℝ→ℝ) ∧
      HasCompactSupport (g.d3 : ℝ→ℝ) ∧ ‖g.f‖≤‖f‖+2*ε ∧
      (∀ x : ℝ,g.f x≤f x) ∧ (∀ x : ℝ,|x|≤R→|g.f x-f x|≤2*ε) := by
  let K:=‖f‖
  let ψ : ContDiffBump (0:ℝ):=⟨R,R+1,hR,by linarith⟩
  let F : ℝ→ℝ:=fun x=>ψ x*(f x+K)
  have hF : Continuous F:=ψ.continuous.mul (f.continuous.add continuous_const)
  have hFs : HasCompactSupport F:=ψ.hasCompactSupport.mul_right
  obtain ⟨g,hg,hgf,hgs⟩:=hF.exists_contDiff_approx (⊤:ℕ∞)
    (ε:=fun _=>ε) continuous_const (fun _=>hε)
  have hg' : ContDiff ℝ ∞ g:=hg
  have hs : HasCompactSupport g:=hFs.mono hgs
  let J:=(Jet3.ofCompactSmooth g hg' hs).addConstant (-K-ε)
  have hJ (x : ℝ) : J.f x=g x-K-ε := by simp [J,Jet3.addConstant]; ring
  have hzero (x : ℝ) : 0≤F x := by
    have hf:= (abs_le.mp (f.norm_coe_le_norm x)).1
    dsimp [F,K]
    exact mul_nonneg ψ.nonneg (by linarith)
  have hle (x : ℝ) : F x≤f x+K :=
    mul_le_of_le_one_left (by have hf:=(abs_le.mp (f.norm_coe_le_norm x)).1; dsimp [K]; linarith) ψ.le_one
  have herr (x : ℝ) : |g x-F x|<ε := by simpa only [Real.dist_eq] using hgf x
  have hlower (x : ℝ) : J.f x≤f x := by
    rw [hJ]
    have hh:=(abs_lt.mp (herr x)).2
    linarith [hle x]
  refine ⟨J,?_,?_,?_,?_,hlower,?_⟩
  · change HasCompactSupport (deriv g)
    exact hs.deriv
  · change HasCompactSupport (deriv (deriv g))
    exact hs.deriv.deriv
  · change HasCompactSupport (deriv (deriv (deriv g)))
    exact hs.deriv.deriv.deriv
  · apply (BoundedContinuousFunction.norm_le (by positivity : 0≤‖f‖+2*ε)).mpr
    intro x
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · rw [hJ]
      have hh:=(abs_lt.mp (herr x)).1
      dsimp [K] at *
      linarith [hzero x]
    · have hh:=(abs_le.mp (f.norm_coe_le_norm x)).2
      linarith [hlower x]
  · intro x hx
    have hψ : ψ x=1:=ψ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hx)
    have he : F x=f x+K:=by simp [F,hψ]
    rw [hJ]
    have hh:=herr x
    rw [he] at hh
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩

lemma exists_smooth_lower_sequence (f : ℝ→ᵇℝ) :
    ∃ g : ℕ→Jet3,
      (∀ n,HasCompactSupport ((g n).d1 : ℝ→ℝ) ∧ HasCompactSupport ((g n).d2 : ℝ→ℝ) ∧
        HasCompactSupport ((g n).d3 : ℝ→ℝ)) ∧
      (∀ n,‖(g n).f‖≤‖f‖+1) ∧ (∀ n x,(g n).f x≤f x) ∧
      ∀ R : ℝ,0<R→∀ ε : ℝ,0<ε→∃ N : ℕ,∀ n≥N,∀ x : ℝ,|x|≤R→|(g n).f x-f x|≤ε := by
  have hx (n : ℕ):=exists_smooth_lower_envelope f
    (by positivity : 0<(n:ℝ)+1) (by positivity : 0<(1:ℝ)/(2*((n:ℝ)+1)))
  choose g h1 h2 h3 hn hlo he using hx
  refine ⟨g,(fun n=>⟨h1 n,h2 n,h3 n⟩),?_,hlo,?_⟩
  · intro n
    have hh : 2*((1:ℝ)/(2*((n:ℝ)+1)))=1/((n:ℝ)+1) := by field_simp
    have hle : (1:ℝ)/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hi:=hn n
    rw [hh] at hi
    exact hi.trans (by linarith)
  · intro R hR ε hε
    obtain ⟨N1,hN1⟩:=exists_nat_ge R
    obtain ⟨N2,hN2⟩:=exists_nat_one_div_lt hε
    refine ⟨max N1 N2,fun n hn x hx=>?_⟩
    have hN1' : N1≤n:=(le_max_left _ _).trans hn
    have hN2' : N2≤n:=(le_max_right _ _).trans hn
    have hx' : |x|≤(n:ℝ)+1 := by
      have hc : (N1:ℝ)≤n:=by exact_mod_cast hN1'
      linarith
    have hh:=he n x hx'
    have heq : 2*((1:ℝ)/(2*((n:ℝ)+1)))=1/((n:ℝ)+1) := by field_simp
    rw [heq] at hh
    exact hh.trans ((one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hN2' 1)).trans hN2.le)

lemma exists_smooth_upper_sequence (f : ℝ→ᵇℝ) :
    ∃ g : ℕ→Jet3,
      (∀ n,HasCompactSupport ((g n).d1 : ℝ→ℝ) ∧ HasCompactSupport ((g n).d2 : ℝ→ℝ) ∧
        HasCompactSupport ((g n).d3 : ℝ→ℝ)) ∧
      (∀ n,‖(g n).f‖≤‖f‖+1) ∧ (∀ n x,f x≤(g n).f x) ∧
      ∀ R : ℝ,0<R→∀ ε : ℝ,0<ε→∃ N : ℕ,∀ n≥N,∀ x : ℝ,|x|≤R→|(g n).f x-f x|≤ε := by
  obtain ⟨g,hs,hn,hlo,he⟩:=exists_smooth_lower_sequence (-f)
  refine ⟨fun n=>(g n).negative,fun n=>⟨(hs n).1.neg,(hs n).2.1.neg,(hs n).2.2.neg⟩,?_,?_,?_⟩
  · intro n
    simpa only [Jet3.negative,norm_neg] using hn n
  · intro n x
    have h:=hlo n x
    change f x≤-(g n).f x
    change (g n).f x≤-f x at h
    linarith
  · intro R hR ε hε
    obtain ⟨N,hN⟩:=he R hR ε hε
    refine ⟨N,fun n hn x hx=>?_⟩
    have h:=hN n hn x hx
    change |-(g n).f x-f x|≤ε
    change |(g n).f x- -f x|≤ε at h
    rw [show -(g n).f x-f x = -((g n).f x+f x) by ring,abs_neg]
    simpa only [sub_neg_eq_add] using h

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBoundedContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem expectedPressure_limit_terminal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (f : ℝ→ᵇℝ) :
    Tendsto (fun n : ℕ=>expectedPressure α 1 f (n+1)) atTop
      (𝓝 (terminalVariational P α f).toReal) := by
  obtain ⟨g,gs,gn,gl,gc⟩:=exists_smooth_lower_sequence f
  obtain ⟨h,hs,hn,hl,hc⟩:=exists_smooth_upper_sequence f
  have gV:=controlValue_uniform_of_compact P hB f (fun n=>(g n).f) (‖f‖+1)
    (by positivity) (by linarith) gn gc
  have hV:=controlValue_uniform_of_compact P hB f (fun n=>(h n).f) (‖f‖+1)
    (by positivity) (by linarith) hn hc
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hδ : 0<ε/(4*α):=by positivity
  obtain ⟨G,hG⟩:=gV _ hδ
  obtain ⟨H,hH⟩:=hV _ hδ
  have hGV:=terminalVariational_abs_sub_le P α hα.le (g G).f f (ε/(4*α))
    (fun m=>(hG G le_rfl m).le)
  have hHV:=terminalVariational_abs_sub_le P α hα.le (h H).f f (ε/(4*α))
    (fun m=>(hH H le_rfl m).le)
  have he : α*(ε/(4*α))=ε/4 := by field_simp
  rw [he] at hGV hHV
  have hg:=expectedPressure_limit_smooth P hB hα (g G) (gs G).1 (gs G).2.1 (gs G).2.2
  have hh:=expectedPressure_limit_smooth P hB hα (h H) (hs H).1 (hs H).2.1 (hs H).2.2
  filter_upwards [Metric.tendsto_nhds.1 hg (ε/4) (by positivity),
    Metric.tendsto_nhds.1 hh (ε/4) (by positivity)] with n hgn hhn
  have hlo:=expectedPressure_mono_terminal α (g G).f f (gl G) n
  have hhi:=expectedPressure_mono_terminal α f (h H).f (hl H) n
  rw [Real.dist_eq] at hgn hhn ⊢
  rcases abs_le.mp hGV with ⟨glo,ghi⟩
  rcases abs_le.mp hHV with ⟨hlo',hhi'⟩
  rcases abs_lt.mp hgn with ⟨gln,ghn⟩
  rcases abs_lt.mp hhn with ⟨hln,hhn⟩
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma expectedPressure_terminal_scaling (α β : ℝ) (φ : ℝ→ᵇℝ) (n : ℕ) :
    expectedPressure α β φ (n+1)=expectedPressure α 1 (β • φ) (n+1) := by
  unfold expectedPressure
  apply integral_congr_ae
  filter_upwards [] with g
  rw [←normalizedPatternLog_source α β φ n g,
    ←normalizedPatternLog_source α 1 (β • φ) n g,one_smul]

theorem main_oai (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P)
    (α β : ℝ) (hα : 0 < α) (_hβ : 0 < β) (φ : ℝ →ᵇ ℝ) :
    ∃ p : ℝ, variationalValue P α β φ = (p : EReal) ∧
      Tendsto (fun N : ℕ => expectedPressure α β φ (N + 1)) atTop (𝓝 p) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N : ℕ => patternLaw α (N + 1)
          {g | ε < |pressure α β φ (N + 1) g - p|}) atTop (𝓝 0) := by
  let p:=(terminalVariational P α (β • φ)).toReal
  have hp : Tendsto (fun N : ℕ=>expectedPressure α β φ (N+1)) atTop (𝓝 p) := by
    have heq : (fun N : ℕ=>expectedPressure α β φ (N+1)) =
        (fun N : ℕ=>expectedPressure α 1 (β • φ) (N+1)) :=
      funext (expectedPressure_terminal_scaling α β φ)
    rw [heq]
    exact expectedPressure_limit_terminal P hB hα (β • φ)
  refine ⟨p,?_,hp,?_⟩
  · rw [variationalValue_eq_terminal]
    exact (terminalVariational_coe_toReal P α hα.le (β • φ)).symm
  · exact pressure_probability_of_expected_limit α β hα.le φ p hp

end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.main_oai := @OAI.SphericalPerceptronFreeEnergy.main_oai
