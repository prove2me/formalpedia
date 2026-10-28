-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:39:30.826982+00:00
-- url     : https://prove2.me/submissions/895680d1-3e45-4bb1-8e25-c238744a79cd

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceLabelRestorationRatio_pair_value
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_array_limit_label_law
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_monomial_tendsto
import Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_perturbation_contact_exists

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

lemma truncatedCountableGaussianField_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (n : ℕ) (g : ℕ → ℝ) (x : S) :
    truncatedCountableGaussianField v L n g x=gaussianPrefixField v (min n (L x)) g x := by
  unfold truncatedCountableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun i => g i * maskedGaussianCoefficient v L i x) n,
    Fin.sum_univ_eq_sum_range (fun i => g i * v i x) (min n (L x))]
  have he (i : ℕ) : g i*maskedGaussianCoefficient v L i x=
      if i<L x then g i*v i x else 0 := by
    unfold maskedGaussianCoefficient
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_range_cutoff _ n (L x)

lemma truncatedCountableGaussianField_eventually_eq (v : ℕ → S → ℝ) (L : S → ℕ)
    (x : S) : ∀ᶠ n in atTop, ∀ g,
      truncatedCountableGaussianField v L n g x=countableGaussianField v L g x := by
  filter_upwards [eventually_ge_atTop (L x)] with n hn g
  rw [truncatedCountableGaussianField_eq,min_eq_right hn]
  rfl

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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_BcfEvalRingHom
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma gaussianAverage_scaling (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s f x = ∫ z, f (x+Real.sqrt s*z) ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt s)^2, sq_nonneg _⟩ : ℝ≥0) = s := by
    ext; exact Real.sq_sqrt s.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt s)
  simp only [mul_zero,NNReal.mk] at hL
  rw [hv,mul_one] at hL
  exact (hL.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun z => f (x+z)) (gaussianReal 0 s))).symm

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableTotalBiasedLaw
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff
attribute [fun_prop] stablePoissonTotal_measurable

lemma stableEppfValue_singleton_one {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    stableEppfValue a b [1] = 1 := by
  have hga : Real.Gamma (1-a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha)).ne'
  have hgb : Real.Gamma (1-b) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  simp [stableEppfValue,hga,hgb]

lemma stableEppfValue_join {a b r : ℝ} (hr : b < r) (rs : List ℝ)
    (hn : 0 < r+rs.sum-a) :
    stableEppfValue a b ((r+1)::rs) =
      (r-b)/(r+rs.sum-a)*stableEppfValue a b (r::rs) := by
  unfold stableEppfValue
  simp only [List.sum_cons,List.length_cons,List.map_cons,List.prod_cons,Nat.add_sub_cancel]
  rw [show r+1+rs.sum-a = (r+rs.sum-a)+1 by ring,
    show r+1-b = (r-b)+1 by ring,
    Real.Gamma_add_one hn.ne',Real.Gamma_add_one (sub_pos.mpr hr).ne']
  field_simp
  simp only [mul_comm b]
  ring

lemma stableEppfValue_new {a b : ℝ} (hb : b < 1) (rs : List ℝ) (hne : rs ≠ [])
    (hn : 0 < rs.sum-a) :
    stableEppfValue a b (1::rs) =
      ((rs.length:ℝ)*b-a)/(rs.sum-a)*stableEppfValue a b rs := by
  have hj : 1 ≤ rs.length := by cases rs <;> simp_all
  have hj1 : rs.length-1+1 = rs.length := Nat.sub_add_cancel hj
  have hgb : Real.Gamma (1-b) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr hb)).ne'
  unfold stableEppfValue
  simp only [List.sum_cons,List.length_cons,List.map_cons,List.prod_cons,Nat.add_sub_cancel,div_self hgb,one_mul]
  rw [show 1+rs.sum-a = (rs.sum-a)+1 by ring,Real.Gamma_add_one hn.ne',
    ← hj1,Finset.prod_range_succ]
  have hcast : ((rs.length-1:ℕ):ℝ)+1 = (rs.length:ℝ) := by exact_mod_cast hj1
  rw [hcast,hj1]
  field_simp
  simp only [mul_comm b]
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_DecoratedWeightedTotal
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
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma fractionalLogMoment_centered {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {b : ℝ} (hb : b ≠ 0) {f : X×S → ℝ} (x : X)
    (hI : Integrable (fun s => Real.exp (b*f (x,s))) ν) :
    Integrable (fun s => Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x))) ν ∧
    (∫ s, Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) ∂ν) = 1 := by
  have hp : 0 < ∫ s, Real.exp (b*f (x,s)) ∂ν := by
    apply integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hI |>.mpr
    simp [Function.support,Real.exp_ne_zero]
  have hfac (s : S) : Real.exp (b*(f (x,s)-fractionalLogMoment ν b f x)) =
      Real.exp (-(Real.log (∫ t, Real.exp (b*f (x,t)) ∂ν)))*Real.exp (b*f (x,s)) := by
    rw [← Real.exp_add]
    congr 1
    unfold fractionalLogMoment
    field_simp
    ring
  constructor
  · simp_rw [hfac]
    exact hI.const_mul _
  · simp_rw [hfac]
    rw [integral_const_mul,Real.exp_neg,Real.exp_log hp,inv_mul_cancel₀ hp.ne']

lemma finiteCascadeShifts_normalized_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0) (H : X → ℝ)
    (hI : finiteCascadeFractionalIntegrable ν step H n z) : ∀ i x,
    Integrable (fun s => Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s))) ν ∧
    (∫ s, Real.exp (z i*finiteCascadeShifts ν step n z H i (x,s)) ∂ν) = 1 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    rcases hI with ⟨hroot,htail⟩
    intro i
    refine Fin.cases ?_ (fun j => ih (fun k => z k.succ) (fun k => hz k.succ) htail j) i
    intro x
    exact fractionalLogMoment_centered ν (hz 0)
      (f := fun p => finiteCascadeLogRecursion ν step n (fun j => z j.succ) H (step p)) x (hroot x)

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
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_ReweightedMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators Polynomial
namespace SphericalPerceptronFreeEnergy

lemma weighted_compact_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {a b : ℝ}
    (A : Ω → ℝ) (hA : Measurable A) (Z : Ω → Icc a b) (hZ : Measurable Z)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ x, |A x| ≤ C) (f : C(Icc a b,ℝ)) :
    Integrable (fun x => A x*f (Z x)) μ := by
  apply Integrable.of_bound (hA.mul (f.continuous.measurable.comp hZ)).aestronglyMeasurable (C*‖f‖)
  exact ae_of_all _ fun x => by
    change |A x*f (Z x)| ≤ C*‖f‖
    rw [abs_mul]
    exact mul_le_mul (hB x) (f.norm_coe_le_norm (Z x)) (abs_nonneg _) hC

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma mem_interior_integrableExpSet_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ=univ := Set.eq_univ_of_forall hX
  simp [he]

omit [IsProbabilityMeasure μ] in
lemma cgf_analytic_of_all
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) (t : ℝ) :
    AnalyticAt ℝ (cgf X μ) t :=
  analyticAt_cgf (mem_interior_integrableExpSet_of_all μ hX t)

lemma entropicMean_eq_div (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    {p : ℝ} (hp : p ≠ 0) : entropicMean μ p X=cgf X μ p/p := by
  rw [entropicMean,intervalIntegral.integral_comp_mul_left _ hp]
  simp only [mul_zero,mul_one]
  have hc : Continuous (deriv (cgf X μ)) := continuous_iff_continuousAt.mpr
    (fun t => (cgf_analytic_of_all μ hX t).deriv.differentiableAt.continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (cgf_analytic_of_all μ hX t).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _),cgf_zero,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma entropicMean_zero (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ) :
    entropicMean μ 0 X=∫ ω, X ω ∂μ := by
  simp [entropicMean,deriv_cgf_zero (mem_interior_integrableExpSet_of_all μ hX 0)]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

lemma gaussian_integrable_exp_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a σ : ℝ) (x : E) :
    Integrable (fun y : E => Real.exp (a*f (x+σ • y))) μ := by
  have hbound (y : E) : a*f (x+σ • y) ≤ |a| *|f x|+(|a| *L*|σ|)*‖y‖ := by
    have hl := hf.dist_le_mul (x+σ • y) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hl
    have hn := abs_add_le (f (x+σ • y)-f x) (f x)
    rw [sub_add_cancel] at hn
    have hmul := mul_le_mul_of_nonneg_left (le_trans hn (add_le_add hl le_rfl)) (abs_nonneg a)
    have hle := le_abs_self (a*f (x+σ • y))
    rw [abs_mul] at hle
    nlinarith
  have hfc := hf.continuous
  apply ((gaussian_integrable_exp_norm μ (|a| *L*|σ|)).const_mul
    (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (hbound y)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

lemma integrable_of_all_exp (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) :
    Integrable X μ :=
  (memLp_of_mem_interior_integrableExpSet (mem_interior_integrableExpSet_of_all μ hX 0) 1).integrable (by simp)

omit [IsProbabilityMeasure μ] in
lemma all_exp_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) (c : ℝ) :
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t*(X ω+c))) μ := by
  intro t
  simpa only [mul_add,Real.exp_add] using (hX t).mul_const (Real.exp (t*c))

lemma entropicMean_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (p c : ℝ) : entropicMean μ p (fun ω => X ω+c)=entropicMean μ p X+c := by
  by_cases hp : p=0
  · subst p
    rw [entropicMean_zero μ (all_exp_add_const μ hX c),entropicMean_zero μ hX,
      integral_add (integrable_of_all_exp μ hX) (integrable_const c),integral_const]
    simp
  · rw [entropicMean_eq_div μ (all_exp_add_const μ hX c) hp,entropicMean_eq_div μ hX hp]
    simp only [cgf,mgf_add_const]
    rw [Real.log_mul (ne_of_gt (mgf_pos (hX p))) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    field_simp

lemma entropicMean_mono_variable
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hXY : X ≤ᵐ[μ] Y) {p : ℝ} (hp : 0 ≤ p) :
    entropicMean μ p X ≤ entropicMean μ p Y := by
  rcases hp.eq_or_lt with hp|hp
  · subst p
    rw [entropicMean_zero μ hX,entropicMean_zero μ hY]
    exact integral_mono_ae (integrable_of_all_exp μ hX) (integrable_of_all_exp μ hY) hXY
  · rw [entropicMean_eq_div μ hX (ne_of_gt hp),entropicMean_eq_div μ hY (ne_of_gt hp)]
    apply div_le_div_of_nonneg_right _ hp.le
    exact Real.log_le_log (mgf_pos (hX p)) (mgf_mono_of_nonneg hXY hp.le (hY p))

lemma entropicMean_bounded_difference
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    {C p : ℝ} (hp : 0 ≤ p) (hXY : ∀ᵐ ω ∂μ, |X ω-Y ω| ≤ C) :
    |entropicMean μ p X-entropicMean μ p Y| ≤ C := by
  have h1 : X ≤ᵐ[μ] (fun ω => Y ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).2
    linarith
  have h2 : Y ≤ᵐ[μ] (fun ω => X ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).1
    linarith
  have H1 := entropicMean_mono_variable μ hX (all_exp_add_const μ hY C) h1 hp
  have H2 := entropicMean_mono_variable μ hY (all_exp_add_const μ hX C) h2 hp
  rw [entropicMean_add_const μ hY] at H1
  rw [entropicMean_add_const μ hX] at H2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianMarkRecursion
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
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_linear_shift {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (A : E →L[ℝ] E) (a : ℝ) (x : E) :
    Integrable (fun y => Real.exp (a*f (x+A y))) μ := by
  have hA : LipschitzWith ‖A‖₊ (fun y => x+A y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_left] using A.lipschitz.dist_le_mul y z
  have hg := hf.comp hA
  simpa using gaussian_integrable_exp_lipschitz μ hg a 1 (0:E)

lemma gaussianLinearEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {b : ℝ} (hb : 0 ≤ b) (A : E →L[ℝ] E) :
    LipschitzWith L (gaussianLinearEntropic μ b A f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianLinearEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a x)
    (fun a => gaussian_integrable_exp_linear_shift μ hf A a y) hb
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+A z) (y+A z)

lemma gaussianLinearBackward_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (ℝ×(E →L[ℝ] E)))
    (hl : ∀ c ∈ l, 0 ≤ c.1) : LipschitzWith L (gaussianLinearBackward μ l f) := by
  induction l with
  | nil => exact hf
  | cons c l ih =>
    exact gaussianLinearEntropic_lipschitz μ
      (ih (fun d hd => hl d (List.mem_cons_of_mem c hd))) (hl c List.mem_cons_self) c.2

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
lemma gaussianLinearMarkStep_measurable (A : ℕ → E →L[ℝ] E) :
    Measurable (gaussianLinearMarkStep A) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply (j+1)).comp measurable_fst).add
    ((A j).measurable.comp measurable_snd)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma linearCascadeWord_nonneg (A : ℕ → E →L[ℝ] E) (k : ℕ) (z : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) : ∀ c ∈ linearCascadeWord A k z, 0 ≤ c.1 := by
  induction k with
  | zero => simp [linearCascadeWord]
  | succ k ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) c hc

lemma gaussianLinearRecursion_realization (ν : ProbabilityMeasure E) [IsGaussian (ν:Measure E)]
    (A : ℕ → E →L[ℝ] E) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (k : ℕ) (z : Fin k → ℝ) (hz : ∀ i, 0 < z i) :
    (∀ x, finiteCascadeLogRecursion ν (gaussianLinearMarkStep A) k z (fun x => f (x 0)) x=
        gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k z) f (x k)) ∧
    finiteCascadeFractionalIntegrable ν (gaussianLinearMarkStep A) (fun x => f (x 0)) k z := by
  induction k with
  | zero => exact ⟨fun _ => rfl,trivial⟩
  | succ k ih =>
    have H := ih (fun i => z i.succ) (fun i => hz i.succ)
    let g := gaussianLinearBackward (ν:Measure E) (linearCascadeWord A k (fun i => z i.succ)) f
    have hg : LipschitzWith L g := gaussianLinearBackward_lipschitz (ν:Measure E) hf _
      (linearCascadeWord_nonneg A k _ (fun i => (hz i.succ).le))
    constructor
    · intro x
      simp only [finiteCascadeLogRecursion,fractionalLogMoment,H.1,gaussianLinearMarkStep,
        linearCascadeWord,gaussianLinearBackward,gaussianLinearEntropic]
      rw [entropicMean_eq_div (ν:Measure E)
        (fun a => gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) a (x (k+1)))
        (hz 0).ne']
      rfl
    · constructor
      · intro x
        simp only [H.1,gaussianLinearMarkStep]
        exact gaussian_integrable_exp_linear_shift (ν:Measure E) hg (A k) (z 0) (x (k+1))
      · exact H.2

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

lemma indexedCommonDepth_comm (n : ℕ) (l m : IndexedLeaf n) :
    indexedCommonDepth n l m = indexedCommonDepth n m l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexedCommonDepth,ih m.2.2 l.2.2,eq_comm]

lemma indexedCommonDepth_self (n : ℕ) (l : IndexedLeaf n) :
    indexedCommonDepth n l l = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [indexedCommonDepth,ih]

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IndexedVisit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

section

lemma oneDecoratedVisit_count {X : Type} (h : X → ℝ≥0∞) (n : ℕ) :
    cascadeVisitCount n ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [oneDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount] using ih

lemma oneDecoratedVisit_likelihood {X : Type} (h : X → ℝ≥0∞) (n : ℕ)
    (z : Fin n → ℝ) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : a < 1) :
    cascadeShapeLikelihood n z a ((oneDecoratedVisit h n).bare n) = 1 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [oneDecoratedVisit,DecoratedVisitShape.bare,List.map_cons,List.map_nil,
      cascadeShapeLikelihood,List.prod_cons,List.prod_nil,mul_one]
    rw [ih (fun i => z i.succ) (fun i => hz1 i.succ) (z 0) (hz1 0)]
    simp only [oneDecoratedVisit_count,Nat.cast_one,stableEppfValue_singleton_one ha (hz1 0),
      ENNReal.ofReal_one,one_mul]

end

lemma twoDecoratedVisit_count {X : Type} (h k : X → ℝ≥0∞) (n : ℕ) (d : Fin (n+1)) :
    cascadeVisitCount n ((twoDecoratedVisit h k n d).bare n) = 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction d using Fin.cases with
    | zero => simp [twoDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount,oneDecoratedVisit_count]
    | succ d => simpa [twoDecoratedVisit,DecoratedVisitShape.bare,cascadeVisitCount] using ih d

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedVisitKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma tiltedMarkKernel_markov (ν : ProbabilityMeasure S) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedMarkKernel ν z F) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [tiltedMarkKernel,Kernel.withDensity_apply _ ((hF.const_mul z).exp.ennreal_ofReal)]
  simp only [Kernel.const_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI x)
    (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),hM x]
  exact ENNReal.ofReal_one

lemma tiltedStateStep_markov (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (z : ℝ) (F : X×S → ℝ)
    (hF : Measurable F) (hI : ∀ x, Integrable (fun s => Real.exp (z*F (x,s))) ν)
    (hM : ∀ x, (∫ s, Real.exp (z*F (x,s)) ∂ν) = 1) :
    IsMarkovKernel (tiltedStateStep ν step z F) := by
  have := tiltedMarkKernel_markov ν z F hF hI hM
  exact Kernel.IsMarkovKernel.map _ hs

lemma pathOneKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) : IsMarkovKernel (pathOneKernel n κ) := by
  induction n with
  | zero => dsimp [pathOneKernel]; infer_instance
  | succ n ih =>
    have := hκ 0
    have := ih (fun i => κ i.succ) (fun i => hκ i.succ)
    dsimp [pathOneKernel]; infer_instance

lemma pathPairKernel_markov (n : ℕ) (κ : Fin n → Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (d : Fin (n+1)) :
    IsMarkovKernel (pathPairKernel n κ d) := by
  induction n with
  | zero => dsimp [pathPairKernel]; infer_instance
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) d
    · have := pathOneKernel_markov (n+1) κ hκ
      simp only [pathPairKernel,Fin.cases_zero]; infer_instance
    · have := hκ 0
      have := ih (fun i => κ i.succ) (fun i => hκ i.succ) j
      simp only [pathPairKernel,Fin.cases_succ]; infer_instance

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
-- module Solutions.OAIQ061_PF.Perceptron_Cascade_TwoVisitWeights
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cascadeShapeReplicas_fintype _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma depthMassIncrement_nonneg (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz1 : ∀ i,z i<1) (a : ℝ) (ha : a<1) (haz : ∀ i,a<z i) (d : Fin (n+1)) :
    0≤depthMassIncrement n z a d := by
  induction n generalizing a with
  | zero => exact sub_nonneg.mpr ha.le
  | succ n ih =>
    induction d using Fin.cases with
    | zero => exact sub_nonneg.mpr (haz 0).le
    | succ d =>
      exact ih _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij))
        (fun i => hz1 i.succ) (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d

lemma twoDecoratedVisit_likelihood (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z)
    (hz1 : ∀ i,z i<1) (a : ℝ) (ha : a<1) (haz : ∀ i,a<z i) (d : Fin (n+1)) :
    cascadeShapeLikelihood n z a ((twoDecoratedVisit (X:=Unit) (fun _ => 1) (fun _ => 1) n d).bare n)=
      ENNReal.ofReal (depthMassIncrement n z a d/(1-a)) := by
  induction n generalizing a with
  | zero => simp [cascadeShapeLikelihood,depthMassIncrement,(sub_pos.mpr ha).ne']
  | succ n ih =>
    induction d using Fin.cases with
    | zero =>
      simp only [twoDecoratedVisit,Fin.cases_zero,DecoratedVisitShape.bare,cascadeShapeLikelihood,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,oneDecoratedVisit_count,Nat.cast_one,
        oneDecoratedVisit_likelihood _ _ _ (fun i => hz1 i.succ) _ (hz1 0),one_mul]
      have he := stableEppfValue_new (hz1 0) [1] (by simp) (by simpa using sub_pos.mpr ha)
      simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,add_zero,
        stableEppfValue_singleton_one ha (hz1 0),mul_one] at he
      rw [he]
      simp [depthMassIncrement]
    | succ d =>
      simp only [twoDecoratedVisit,Fin.cases_succ,DecoratedVisitShape.bare,cascadeShapeLikelihood,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,twoDecoratedVisit_count,Nat.cast_ofNat]
      rw [ih _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)) (fun i => hz1 i.succ)
        (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d]
      have he := stableEppfValue_join (hz1 0) ([] : List ℝ) (by simpa using sub_pos.mpr ha)
      simp only [List.sum_nil,add_zero,stableEppfValue_singleton_one ha (hz1 0),mul_one] at he
      rw [show (1:ℝ)+1=2 by norm_num] at he
      rw [he,←ENNReal.ofReal_mul (div_nonneg
        (depthMassIncrement_nonneg n _ (fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij))
          (fun i => hz1 i.succ) (z 0) (hz1 0) (fun i => hz (Fin.succ_pos i)) d)
        (sub_pos.mpr (hz1 0)).le)]
      congr 1
      change _=depthMassIncrement n (fun i => z i.succ) (z 0) d/(1-a)
      field_simp [(sub_pos.mpr (hz1 0)).ne']

lemma depthMassIncrement_eq (n : ℕ) (z : Fin n→ℝ) (a : ℝ) (d : Fin (n+1)) :
    depthMassIncrement n z a d=(Fin.snoc z 1 : Fin (n+1) → ℝ) d-(Fin.cons a z : Fin (n+1) → ℝ) d := by
  induction n generalizing a with
  | zero => simp [depthMassIncrement,Fin.snoc_zero,Fin.cons_zero,Fin.eq_zero d]
  | succ n ih =>
    induction d using Fin.cases with
    | zero => simp [depthMassIncrement]
    | succ d =>
      change depthMassIncrement n (fun i => z i.succ) (z 0) d=_
      rw [ih,Fin.cons_succ]
      have h1 : (Fin.cons (z 0) (fun i => z i.succ) : Fin (n+1) → ℝ) d=z d := congrFun (Fin.cons_self_tail z) d
      rw [h1]
      congr 1
      induction d using Fin.lastCases with
      | last => simp
      | cast d => simp only [Fin.succ_castSucc,Fin.snoc_castSucc]

lemma depthMassIncrement_stepCumulative {n : ℕ} (w : Fin (n+1)→ℝ) (hw1 : ∑ i,w i=1)
    (d : Fin (n+1)) : depthMassIncrement n (stepCumulative w) 0 d=w d := by
  rw [depthMassIncrement_eq]
  have hu : (Fin.snoc (stepCumulative w) 1 : Fin (n+1) → ℝ) d=∑ i,if i≤d then w i else 0 := by
    induction d using Fin.lastCases with
    | last => simpa only [Fin.snoc_last,Fin.le_last,ite_true] using hw1.symm
    | cast d => simp only [Fin.snoc_castSucc,stepCumulative]
  have hl : (Fin.cons 0 (stepCumulative w) : Fin (n+1) → ℝ) d=∑ i,if i<d then w i else 0 := by
    induction d using Fin.cases with
    | zero => simp
    | succ d =>
      simp only [Fin.cons_succ,stepCumulative]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact propext (by change i.val≤d.val ↔ i.val<d.val+1; omega)
  rw [hu,hl,←Finset.sum_sub_distrib]
  calc
    _ = ∑ i,if i=d then w d else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i d with h|rfl|h
      · simp [h,le_of_lt h,ne_of_lt h]
      · simp
      · simp [not_le_of_gt h,not_lt_of_gt h,ne_of_gt h]
    _ = w d := by simp

lemma twoVisitMass_stepCumulative {n : ℕ} (w : Fin (n+1)→ℝ)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1) (d : Fin (n+1)) :
    (twoVisitMass n (stepCumulative w) d).toReal=w d := by
  rw [twoVisitMass,twoDecoratedVisit_likelihood n _ (stepCumulative_strictMono w hw)
    (stepCumulative_lt_one w hw hw1) 0 (by norm_num) (stepCumulative_pos w hw),
    depthMassIncrement_stepCumulative w hw1]
  simp only [sub_zero,div_one,ENNReal.toReal_ofReal (hw d).le]

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

lemma gibbsReplicaMean_product_of_integrable {H F : S → ℝ} {n : ℕ}
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hG : Measurable G)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {D B : ℝ}
    (hFD : ∀ x, |F x| ≤ D) (hGB : ∀ x, |G x| ≤ B) :
    gibbsReplicaMean μ H (n+1) (fun x => F (x 0)*G (fun j => x j.succ)) =
      tiltMean μ H F 1*gibbsReplicaMean μ H n G := by
  have heI : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ heI
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  rw [← tilt_law_integral_of_integrable μ hH heI]
  let ν := tiltLaw μ H 1
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm
  rw [← he.integral_comp' (fun x => F (x 0)*G (fun j => x j.succ))]
  change (∫ p : S×(Fin n → S), F ((Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) 0)*
    G (fun j => (Fin.insertNth 0 p.1 p.2 : Fin (n+1) → S) j.succ)
      ∂ν.prod (Measure.pi fun _ => ν)) = _
  simp only [Fin.insertNth_zero',Fin.cons_zero,Fin.cons_succ]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable D
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFD x)
  have hGi : Integrable G (Measure.pi fun _ : Fin n => ν) := Integrable.of_bound
    hG.aestronglyMeasurable B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hGB x)
  rw [integral_prod _ (hFi.mul_prod hGi)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

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
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_KernelReplicaGibbs
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
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernel_replicaMean_measurable {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G)) :
    Measurable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) := by
  change Measurable (fun a => tiltMean (kernelReplica κ n a) (replicaPotential (H a) n) (G a) 1)
  apply kernel_tiltMean_measurable (kernelReplica κ n) (H := fun a => replicaPotential (H a) n) _ hG
  change Measurable (fun a : A × (Fin n → S) => ∑ i, H a.1 (a.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

end

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CountableFreshMoment
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

variable {S : Type} [MeasurableSpace S] {k : ℕ}

lemma labelProfile_covariance (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance (labelProfileRow q) (labelProfileRow q)
      (indexedGaussianRowLength (I := Fin 1) k) x y = q (indexedCommonDepth k y.2 x.2) := by
  simpa only [labelProfileRow,Fin.sum_univ_one,mul_one] using
    profileGaussianRow_covariance (fun l (_ : Fin 1) => q l) (fun _ => h0) (fun _ => hq)
      (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)))
      (fun _ : S => WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) x y

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshDiagonalNoise
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal BoundedContinuousFunction ENNReal

section

variable {n r : ℕ}

lemma freshNoiseRows_apply (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0)
    (x : Fin n→ℝ) (y : Fin r→ℝ) (i : Fin r) :
    inner ℝ (freshNoiseRows v s i) (WithLp.toLp 2 (Sum.elim x y)) =
      inner ℝ (v i) (WithLp.toLp 2 x) + Real.sqrt s*y i := by
  classical
  change (∑ j : Fin n ⊕ Fin r, Sum.elim x y j *
    Sum.elim (fun j => v i j) (fun j => if j=i then Real.sqrt s else 0) j) = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [show (∑ j : Fin r, y j * if j=i then Real.sqrt s else 0)=Real.sqrt s*y i by
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]; ring]
  rfl

lemma freshNoiseRows_gram (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) :
    Matrix.gram ℝ (freshNoiseRows v s)=fun i j => Matrix.gram ℝ v i j + if i=j then (s:ℝ) else 0 := by
  classical
  ext i j
  change (∑ l : Fin n ⊕ Fin r,
    Sum.elim (fun l => v j l) (fun l => if l=j then Real.sqrt s else 0) l *
    Sum.elim (fun l => v i l) (fun l => if l=i then Real.sqrt s else 0) l)=_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases h : i=j
  · subst j
    simp only [ite_true,← sq,Real.sq_sqrt s.coe_nonneg]
    simp [Matrix.gram,PiLp.inner_apply,pow_two]
  · simp only [ite_eq_right h,zero_mul]
    rfl

lemma countableGaussianCovariance_finite_gram {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) (r : ℕ) (xs : Fin r→S) :
    ∃ n : ℕ, ∃ w : Fin r→EuclideanSpace ℝ (Fin n),
      Matrix.gram ℝ w=(fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
  have hc : ∀ᶠ n : ℕ in Filter.atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn⟩ := hc.exists
  refine ⟨n,fun i => WithLp.toLp 2 (fun j : Fin n => maskedGaussianCoefficient v L j.val (xs i)),?_⟩
  ext i j
  rw [← hn i j]
  change (∑ l : Fin n, maskedGaussianCoefficient v L l.val (xs j)*
    maskedGaussianCoefficient v L l.val (xs i))=_
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end

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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StepDual
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

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_UniformQuantileCells
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

lemma uniformQuantileGrid_strict (n : ℕ) : StrictMono (uniformQuantileGrid n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

lemma uniformQuantileGrid_zero (n : ℕ) : uniformQuantileGrid n 0=0 := by
  apply Subtype.ext
  norm_num [uniformQuantileGrid]

lemma uniformQuantileGrid_last (n : ℕ) : uniformQuantileGrid n (Fin.last (n+1))=1 := by
  apply Subtype.ext
  change ((n+1:ℕ):ℝ)/(n+1)=1
  push_cast
  exact div_self (by positivity)

lemma uniformQuantileCell_mono (n : ℕ) : Monotone (uniformQuantileCell n) := by
  intro u v huv
  change min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ≤ min ⌊(n+1:ℝ)*(v:ℝ)⌋₊ n
  exact min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (show (u:ℝ)≤v from huv) (by positivity)))

lemma uniformQuantileCell_measurable (n : ℕ) : Measurable (uniformQuantileCell n) :=
  (uniformQuantileCell_mono n).measurable

lemma uniformQuantileCell_floor {n : ℕ} {u : Time} (hu : (u:ℝ)<1) :
    (uniformQuantileCell n u).val=⌊(n+1:ℝ)*(u:ℝ)⌋₊ := by
  change min _ n=_
  apply min_eq_left
  have hf : ⌊(n+1:ℝ)*(u:ℝ)⌋₊<n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) u.2.1)]
    push_cast
    nlinarith
  omega

lemma uniformQuantileCell_bounds (n : ℕ) (u : Time) :
    uniformQuantileGrid n (uniformQuantileCell n u).castSucc≤u ∧
      u≤uniformQuantileGrid n (uniformQuantileCell n u).succ := by
  by_cases hu : (u:ℝ)<1
  · have he := uniformQuantileCell_floor (n:=n) hu
    constructor
    · change ((uniformQuantileCell n u).val:ℝ)/(n+1)≤u
      rw [he,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity) u.2.1)
    · change (u:ℝ)≤((_ : ℕ):ℝ)/(n+1)
      rw [Fin.val_succ,he,le_div_iff₀ (by positivity)]
      push_cast
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((n+1:ℝ)*(u:ℝ))).le
  · have he : u=1 := Subtype.ext (le_antisymm u.2.2 (le_of_not_gt hu))
    subst u
    have hcell : uniformQuantileCell n 1=Fin.last n := by
      apply Fin.ext
      change min ⌊(n+1:ℝ)*1⌋₊ n=n
      rw [mul_one,show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
      omega
    rw [hcell,Fin.succ_last,uniformQuantileGrid_last]
    exact ⟨le_top,le_rfl⟩

lemma uniformQuantileCell_atom {n : ℕ} {u : Time} (hu : (u:ℝ)<1) (i : Fin (n+1)) :
    uniformQuantileCell n u=i ↔
      u∈Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
  rw [Fin.ext_iff,uniformQuantileCell_floor hu]
  rw [Nat.floor_eq_iff (mul_nonneg (by positivity) u.2.1)]
  change ((i:ℝ)≤(n+1:ℝ)*(u:ℝ) ∧ (n+1:ℝ)*(u:ℝ)<(i:ℝ)+1) ↔
    ((i:ℝ)/(n+1)≤(u:ℝ) ∧ (u:ℝ)<((i.val+1:ℕ):ℝ)/(n+1))
  rw [div_le_iff₀ (by positivity),lt_div_iff₀ (by positivity)]
  push_cast
  ring_nf

lemma uniformQuantileCell_weight (n : ℕ) (i : Fin (n+1)) :
    timeLaw.real ((uniformQuantileCell n) ⁻¹' {i})=1/(n+1:ℝ) := by
  have hae : ((uniformQuantileCell n) ⁻¹' {i})=ᵐ[timeLaw]
      Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
    have hnot : ∀ᵐ u ∂timeLaw, u≠1 := by exact ae_iff.mpr (by simp)
    filter_upwards [hnot] with u hu
    exact propext (uniformQuantileCell_atom (lt_of_le_of_ne u.2.2 (fun he => hu (Subtype.ext he))) i)
  rw [measureReal_congr hae]
  simp only [Measure.real,timeLaw_eq_volume,unitInterval.volume_Ico]
  rw [ENNReal.toReal_ofReal]
  · dsimp [uniformQuantileGrid]
    push_cast
    ring
  · exact sub_nonneg.mpr ((uniformQuantileGrid_strict n).monotone (Fin.castSucc_le_succ i))

lemma uniformQuantileCell_integral (n : ℕ) (F : Fin (n+1)→ℝ) :
    (∫ u, F (uniformQuantileCell n u) ∂timeLaw)=∑ i, (1/(n+1:ℝ))*F i := by
  rw [integral_finite_label _ (uniformQuantileCell_measurable n)]
  simp_rw [uniformQuantileCell_weight]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshGGLogUniqueness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma probability_Icc_eq_of_moments {a b : ℝ} (μ ν : ProbabilityMeasure (Icc a b))
    (hm : ∀ r : ℕ, (∫ x, x.val^r ∂(μ : Measure (Icc a b)))=
      ∫ x, x.val^r ∂(ν : Measure (Icc a b))) : μ=ν := by
  have h : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    apply integral_continuous_tendsto_of_moments (fun _ : ℕ => (μ : Measure (Icc a b)))
      (ν : Measure (Icc a b)) (fun r => ?_) F.toContinuousMap
    rw [hm r]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_ArrayLimitGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
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
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactJointMonomials
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
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

lemma sourceLabelLaw_integral (k : ℕ) (w : Fin (k+1)→ℝ) (hw : ∀ l, 0≤w l)
    (g : unitInterval→ℝ) (hg : Measurable g) :
    (∫ x, g x ∂sourceLabelLaw k w)=∑ l, w l*g (sourceLabelLevel k l) := by
  unfold sourceLabelLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac' g _ hg.stronglyMeasurable,
      ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro l _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

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
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMarkedKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma freshMarkedMatrixKernel_gram {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin r→E) :
    freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v)=
      ∫ z, Ψ z ∂multivariateGaussian 0 (Matrix.gram ℝ v) :=
  (Classical.choose_spec (freshMarked_extension_exists Ψ)).2 (gramCovariance v)

lemma freshMarkedMatrixKernel_gaussian {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (v : Fin r→E) :
    (∫ g, Ψ (gaussianRows v g) ∂stdGaussian E) = freshMarkedMatrixKernel Ψ (Matrix.gram ℝ v) := by
  rw [freshMarkedMatrixKernel_gram,←gaussianRows_map_stdGaussian v,
    integral_map (gaussianRows v).continuous.measurable.aemeasurable Ψ.continuous.aestronglyMeasurable]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_FreshMomentLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy


lemma sourceFresh_exp_ae (n k : ℕ) (f : ℝ →ᵇℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_LabelFreshKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceLabelLevel_val_injective (k : ℕ) :
    Function.Injective (fun l : Fin (k+1) => (sourceLabelLevel k l).val) := by
  intro i j hij
  apply Fin.ext
  have h : (i.val:ℝ)=(j.val:ℝ) := by
    apply (div_left_inj' (show (k+1:ℕ)≠(0:ℝ) by positivity)).mp
    exact hij
  exact_mod_cast h

lemma labelProfileInterpolant_node {k : ℕ} (q : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    labelProfileInterpolant q (sourceLabelLevel k l)=q l := by
  exact Lagrange.eval_interpolate_at_node q (sourceLabelLevel_val_injective k).injOn (Finset.mem_univ l)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_CompactArrayMap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.compactRealLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

lemma compactDiagonalMapBlock_continuous {e d : K→L} (he : Continuous e) (hd : Continuous d) (n : ℕ) :
    Continuous (compactDiagonalMapBlock e d n) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold compactDiagonalMapBlock
  split_ifs <;> fun_prop

omit [TopologicalSpace K] [TopologicalSpace L] in
lemma compactDiagonalMapBlock_compactBlock (e d : K→L) (n : ℕ) (Q : CompactArray K) :
    compactBlock n (compactDiagonalMapArray e d Q)=compactDiagonalMapBlock e d n (compactBlock n Q) := by
  funext i j
  simp only [compactBlock,compactDiagonalMapArray,compactDiagonalMapBlock,Fin.val_inj]


variable [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
  [SecondCountableTopology K] [SecondCountableTopology L]

lemma compactDiagonalMapLaw_integral (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K)) (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, F (compactDiagonalMapArray e d Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactDiagonalMapArray_continuous he hd).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactDiagonalMapLaw_gg (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0) (n : ℕ) (i : Fin n)
    (f : CompactBlock L n →ᵇ ℝ) (g : L →ᵇ ℝ) :
    compactGGDefect (compactDiagonalMapLaw e d he hd μ) n i f g=0 := by
  let f' := f.compContinuous ⟨compactDiagonalMapBlock e d n,compactDiagonalMapBlock_continuous he hd n⟩
  let g' := g.compContinuous ⟨e,he⟩
  have hmul (a b : ℕ) (hab : a≠b) :
      (∫ Q, f (compactBlock n Q)*g (Q a b) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
        ∫ Q, f' (compactBlock n Q)*g' (Q a b) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q)*g (Q a b))
      ((f.measurable.comp (compactBlock_continuous n).measurable).mul (g.measurable.comp (by fun_prop)))]
    simp only [compactDiagonalMapBlock_compactBlock,compactDiagonalMapArray,ite_eq_right hab]
    rfl
  have hf : (∫ Q, f (compactBlock n Q) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, f' (compactBlock n Q) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q))
      (f.measurable.comp (compactBlock_continuous n).measurable)]
    simp only [compactDiagonalMapBlock_compactBlock]
    rfl
  have hg : (∫ Q, g (Q 0 1) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, g' (Q 0 1) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => g (Q 0 1)) (by fun_prop)]
    rfl
  unfold compactGGDefect
  rw [hmul i.val n (Nat.ne_of_lt i.isLt),hf,hg]
  have hs : (∑ j ∈ Finset.univ.erase i, ∫ Q, f (compactBlock n Q)*g (Q i j)
      ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∑ j ∈ Finset.univ.erase i, ∫ Q, f' (compactBlock n Q)*g' (Q i j)
        ∂(μ : Measure (CompactArray K)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply hmul
    intro hij
    exact (Finset.mem_erase.mp hj).1 (Fin.ext hij.symm)
  rw [hs]
  exact hGG n i f' g'
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_IndexedTerminalProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y S T : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace S] [MeasurableSpace T]

lemma cascadeTiltedStep_markov (ν : ProbabilityMeasure S) (step : X×S→X)
    (hs : Measurable step) (n : ℕ) (z : Fin n→ℝ) (hz : ∀ i, 0<z i)
    (H : X→ℝ) (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z)
    (i : Fin n) :
    IsMarkovKernel (tiltedStateStep ν step (z i) (finiteCascadeShifts ν step n z H i)) :=
  tiltedStateStep_markov ν step hs (z i) _ (finiteCascadeShifts_measurable ν step hs n z hH i)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).1)
    (fun x => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun i => (hz i).ne') H hI i x).2)

lemma pathCorrelation_one (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (d : Fin (n+1)) (x : X) : pathCorrelation n κ (fun _ => 1) d x=1 := by
  have := pathPairKernel_markov n κ hκ d
  simp [pathCorrelation]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_RestorationMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

lemma restorationReplicaTest_measurable (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    (hW : Measurable W) (hF : Measurable F) (k : ℕ) :
    Measurable (restorationReplicaTest r W F k) := by
  induction k with
  | zero => exact hF
  | succ k hk =>
    exact (hW.comp (measurable_pi_apply 0)).mul
      (hk.comp (Measurable.of_eval fun index => measurable_pi_apply index.succ))

omit [MeasurableSpace S] in
lemma restorationReplicaTest_bound (r : ℕ) {W : S→ℝ} {F : (Fin r→S)→ℝ}
    {D B : ℝ} (hD : 0≤D) (_hB : 0≤B) (hW : ∀ x, |W x|≤D) (hF : ∀ x, |F x|≤B)
    (k : ℕ) (x : Fin (r+k)→S) : |restorationReplicaTest r W F k x| ≤ D^k*B := by
  induction k with
  | zero => simpa only [restorationReplicaTest,pow_zero,one_mul] using hF x
  | succ k hk =>
    rw [restorationReplicaTest,abs_mul]
    exact (mul_le_mul (hW _) (hk _) (abs_nonneg _) hD).trans_eq (by ring)

lemma restoration_replica_moment (μ : Measure S) [IsProbabilityMeasure μ]
    {H W : S→ℝ} {r : ℕ} {F : (Fin r→S)→ℝ}
    (hH : Measurable H) (hW : Measurable W) (hF : Measurable F)
    (hi : Integrable (fun x => Real.exp (H x)) μ)
    {D B : ℝ} (hD : 0≤D) (hB : 0≤B) (hWD : ∀ x, |W x|≤D) (hFB : ∀ x, |F x|≤B)
    (k : ℕ) :
    gibbsReplicaMean μ H (r+k) (restorationReplicaTest r W F k) =
      (tiltMean μ H W 1)^k*gibbsReplicaMean μ H r F := by
  induction k with
  | zero => simp only [restorationReplicaTest,pow_zero,one_mul,Nat.add_zero]
  | succ k hk =>
    change gibbsReplicaMean μ H ((r+k)+1) (fun x => W (x 0)*restorationReplicaTest r W F k (fun i => x i.succ)) = _
    rw [gibbsReplicaMean_product_of_integrable μ hH hW
        (restorationReplicaTest_measurable r hW hF k) hi hWD
        (restorationReplicaTest_bound r hD hB hWD hFB k), hk]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem source_label_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l, 0<w l) (hw1 : ∑ l,w l=1) (p d : ℕ→ℕ)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b) :
    ∃ (u : (n : ℕ)→Fin (n+1)→ℝ)
      (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) (s : ℕ→ℕ),
      (∀ n,u n∈Icc (fun _=>1) (fun _=>2)) ∧ StrictMono s ∧
      Tendsto (fun n => sourceGibbsArrayLaw (s n) k 0 (fun j=>p j.val)
        (fun j=>d j.val) (fun _=>0) (u (s n)) (stepCumulative w) 0) atTop (𝓝 ν) ∧
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (g : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G g=0) ∧
      (∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=CompactJointOverlap) e)
        (ν : Measure _) (ν : Measure _)) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hc (n : ℕ) := source_perturbation_contact_exists n k (0 : ℝ →ᵇ ℝ)
    (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (fun _=>le_rfl) monotone_const
    (stepCumulative w) hz hz0 hz1 0
  choose u hu hm using hc
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence (fun n => sourceGibbsArrayLaw n k
    (0 : ℝ →ᵇ ℝ) (fun j=>p j.val) (fun j=>d j.val) (fun _=>0) (u n) (stepCumulative w) 0)
  refine ⟨u,ν,s,hu,hs,hlim,?_,?_,?_,?_⟩
  · exact source_contact_limit_joint_gg k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hs hlim hcover
  · exact source_contact_limit_exchangeable k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
      (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  · apply source_array_limit_label_law k 0 p d w hw hw1
      (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u (fun n j=>?_) (fun _=>0)
      (fun b hb=>hcover 0 b (by omega)) hs hlim
    have h := (hu n).1 j
    linarith
  · exact source_contact_limit_spin_geometry k 0 p d (stepCumulative w) hz hz0 hz1
      (fun _=>0) (fun _ _=>0) (fun _ _=>le_rfl) (fun _=>monotone_const) u hu hm
      (H:=0) (T:=0) le_rfl (fun _=>le_rfl) (fun _=>le_rfl) hcover hs hlim

lemma indexedCommonDepth_ultrametric (n : ℕ) (a b c : IndexedLeaf n) :
    min (indexedCommonDepth n a b) (indexedCommonDepth n a c)≤ indexedCommonDepth n b c := by
  let l := min (indexedCommonDepth n a b) (indexedCommonDepth n a c)
  apply (indexedLeafSharedVertex_eq_iff n b c l).mp
  exact ((indexedLeafSharedVertex_eq_iff n a b l).mpr (min_le_left _ _)).symm.trans
    ((indexedLeafSharedVertex_eq_iff n a c l).mpr (min_le_right _ _))

lemma sourceJointArray_label_geometry {N k : ℕ} (x : ℕ→NormalizedSpin N×IndexedLeaf k) :
    CompactLabelGeometry k (sourceJointArray x) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_comm k (x j).2 (x i).2]
  · intro i
    simp only [sourceJointArray,sourceJointOverlap,indexedCommonDepth_self,Fin.val_last]
  · intro i j l
    change min (((indexedCommonDepth k (x j).2 (x i).2).val:ℝ)/(k+1:ℕ))
      (((indexedCommonDepth k (x l).2 (x i).2).val:ℝ)/(k+1:ℕ))≤
      ((indexedCommonDepth k (x l).2 (x j).2).val:ℝ)/(k+1:ℕ)
    have h := indexedCommonDepth_ultrametric k (x i).2 (x j).2 (x l).2
    rw [indexedCommonDepth_comm k (x i).2 (x j).2,
      indexedCommonDepth_comm k (x i).2 (x l).2,indexedCommonDepth_comm k (x j).2 (x l).2] at h
    rcases le_total (indexedCommonDepth k (x j).2 (x i).2) (indexedCommonDepth k (x l).2 (x i).2) with he|he
    · rw [min_eq_left he] at h
      exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
    · rw [min_eq_right he] at h
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))

lemma compactLabelGeometry_closed (k : ℕ) : IsClosed {Q | CompactLabelGeometry k Q} := by
  unfold CompactLabelGeometry
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

lemma sourceGibbsArray_limit_label_geometry (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelGeometry k Q := by
  have hc := compactLabelGeometry_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x => sourceJointArray_label_geometry x))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelReferenceValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileTerminal_lipschitz (g : Jet3) (s : ℝ≥0) :
    LipschitzWith (‖(g.heatLog s 1).d1‖₊*
      ‖innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊)
      (labelProfileTerminal g s) := by
  have he : labelProfileTerminal g s =
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog s 1).f
        ((innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))) v) := by
    funext v
    rw [Jet3.heatLog_f]
    rfl
  rw [he]
  have heatLipschitz : LipschitzWith ‖(g.heatLog s 1).d1‖₊ (g.heatLog s 1).f := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g.heatLog s 1).has1 point).differentiableAt)
    intro point
    rw [(g.heatLog s 1).deriv_eq]
    exact_mod_cast (g.heatLog s 1).d1.norm_coe_le_norm point
  exact heatLipschitz.comp
    (innerSL ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ)) : EuclideanSpace ℝ (Fin 1))).lipschitz

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma compactLabelNodes_closed (k : ℕ) : IsClosed {Q | CompactLabelNodes k Q} := by
  unfold CompactLabelNodes
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (Set.finite_range (sourceLabelLevel k)).isClosed.preimage (by fun_prop)

lemma sourceGibbsArray_limit_label_nodes (k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n=>sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactLabelNodes k Q := by
  have hc := compactLabelNodes_closed k
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc (fun n=>sourceGibbsArray_closed_full
    (s n) k f (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) hc
    (fun x i j => ⟨indexedCommonDepth k (x j).2 (x i).2,rfl⟩))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma labelProfileSpin_node {k : ℕ} (q : Fin (k+1)→Time) (l : Fin (k+1)) :
    labelProfileSpin q (sourceLabelLevel k l)=timeSpin (q l) := by
  apply Subtype.ext
  change min 1 (max 0 (labelProfileInterpolant (fun i => (q i:ℝ)) (sourceLabelLevel k l)))=(q l:ℝ)
  rw [labelProfileInterpolant_node,max_eq_right (q l).prop.1,min_eq_right (q l).prop.2]

lemma labelProfileMap_continuous {k : ℕ} (q : Fin (k+1)→Time) : Continuous (labelProfileMap q) :=
  ((labelProfileSpin_continuous q).comp continuous_snd).prodMk continuous_snd

lemma sourceLabelLevel_le {k : ℕ} (i j : Fin (k+1)) :
    sourceLabelLevel k i ≤ sourceLabelLevel k j ↔ i≤j := by
  change (i.val:ℝ)/(k+1:ℕ)≤(j.val:ℝ)/(k+1:ℕ) ↔ i≤j
  rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ)<(k+1:ℕ))]
  exact_mod_cast (Iff.rfl : i.val≤j.val ↔ i≤j)

lemma compactSpinGeometry_closed : IsClosed {Q : CompactArray CompactJointOverlap | CompactSpinGeometry Q} := by
  unfold CompactSpinGeometry
  simp only [ofPred_and,ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
        isClosed_le (by fun_prop) (by fun_prop)))

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfileReferenceFull
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma labelProfileDiagonal_continuous : Continuous labelProfileDiagonal := by
  unfold labelProfileDiagonal
  fun_prop

lemma labelProfileSpin_ultra {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q)
    (i j l : ℕ) : min (labelProfileSpin q (Q i j).2).val (labelProfileSpin q (Q i l).2).val≤
      (labelProfileSpin q (Q j l).2).val := by
  obtain ⟨a,ha⟩ := hN i j
  obtain ⟨b,hb⟩ := hN i l
  obtain ⟨c,hc⟩ := hN j l
  have hs := hQ.2.2 i j l
  rw [←ha,←hb,←hc] at hs
  rw [←ha,←hb,←hc,labelProfileSpin_node,labelProfileSpin_node,labelProfileSpin_node]
  change min (q a:ℝ) (q b:ℝ)≤(q c:ℝ)
  rcases le_total a b with hab|hab
  · have hab' : (sourceLabelLevel k a).val ≤ (sourceLabelLevel k b).val :=
      (sourceLabelLevel_le a b).mpr hab
    have hac : a ≤ c := (sourceLabelLevel_le a c).mp (by
      change (sourceLabelLevel k a).val≤(sourceLabelLevel k c).val
      simpa only [min_eq_left hab'] using hs)
    exact (min_le_left _ _).trans (hq hac)
  · have hba' : (sourceLabelLevel k b).val ≤ (sourceLabelLevel k a).val :=
      (sourceLabelLevel_le b a).mpr hab
    have hbc : b ≤ c := (sourceLabelLevel_le b c).mp (by
      change (sourceLabelLevel k b).val≤(sourceLabelLevel k c).val
      simpa only [min_eq_right hba'] using hs)
    exact (min_le_right _ _).trans (hq hbc)

lemma labelProfileDiagonalMap_geometry {k : ℕ} (q : Fin (k+1)→Time) (hq : Monotone q)
    {Q : CompactArray CompactJointOverlap} (hQ : CompactLabelGeometry k Q) (hN : CompactLabelNodes k Q) :
    CompactSpinGeometry (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q) := by
  have hsym (i j : ℕ) : (Q i j).2=(Q j i).2 := Subtype.ext (hQ.1 i j)
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j; rfl
    · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right (Ne.symm hij),labelProfileMap,hsym i j]
  · intro i
    simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal]
  · intro i j l
    by_cases hjl : j=l
    · subst l
      simp only [compactDiagonalMapArray,↓reduceIte,labelProfileDiagonal,min_self]
      split_ifs <;> first | exact le_rfl | exact (labelProfileSpin q (Q i j).2).prop.2
    · by_cases hij : i=j
      · subst j
        simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
        exact min_le_right _ _
      · by_cases hil : i=l
        · subst l
          simp only [compactDiagonalMapArray,↓reduceIte,ite_eq_right hij,ite_eq_right hjl,labelProfileDiagonal,labelProfileMap]
          rw [hsym i j]
          exact min_le_left _ _
        · simp only [compactDiagonalMapArray,ite_eq_right hij,ite_eq_right hil,ite_eq_right hjl,labelProfileMap]
          exact labelProfileSpin_ultra q hq hQ hN i j l

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CountableMarkedDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma truncatedFreshMarkedKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (n : ℕ) (xs : Fin r→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i => truncatedCountableGaussianField v L n g (xs i)))
      ∂countableGaussianLaw)=
      freshMarkedMatrixKernel Ψ (fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
  let rows : Fin r→EuclideanSpace ℝ (Fin n) := fun i =>
    WithLp.toLp 2 (fun j => maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
    ext i j
    change (∑ l : Fin n, maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i)) = _
    unfold gaussianPrefixCovariance
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [←hg,←freshMarkedMatrixKernel_gaussian,←map_pi_eq_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]
  have hp := gaussianCoordinatePrefix_measurePreserving n
  have hm : AEStronglyMeasurable (fun y : Fin n→ℝ => Ψ (gaussianRows rows (WithLp.toLp 2 y)))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  rfl

lemma countableFreshMarkedKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (xs : Fin r→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i => countableGaussianField v L g (xs i))) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel Ψ (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : Fin r, ∀ g,
      truncatedCountableGaussianField v L n g (xs i)=countableGaussianField v L g (xs i) :=
    Filter.eventually_all.mpr (fun i => truncatedCountableGaussianField_eventually_eq v L (xs i))
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn,hc⟩ := (he.and hc).exists
  simpa only [hn,hc] using truncatedFreshMarkedKernel v L Ψ n xs

lemma freshMixedKernel_diagonal_noise {r n : ℕ} (f : Fin r→ℝ →ᵇ ℝ)
    (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) :
    freshMarkedMatrixKernel (gaussianMixedTest f)
      (fun i j => Matrix.gram ℝ v i j + if i=j then (s:ℝ) else 0)=
      freshMarkedMatrixKernel (gaussianMixedTest (fun i => gaussianAverageBCF s (f i)))
        (Matrix.gram ℝ v) := by
  classical
  rw [←freshNoiseRows_gram v s,←freshMarkedMatrixKernel_gaussian,
    ←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  let F : (Fin n→ℝ)×(Fin r→ℝ)→ℝ := fun p =>
    ∏ i : Fin r, f i (inner ℝ (v i) (WithLp.toLp 2 p.1)+Real.sqrt s*p.2 i)
  have hF : Integrable F ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin r => gaussianReal 0 1)) := by
    apply Integrable.of_bound (by fun_prop) (∏ i, ‖f i‖)
    exact ae_of_all _ fun p => by
      simp only [F,norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun index _ => (f index).norm_coe_le_norm _)
  have hp := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n⊕Fin r => gaussianReal 0 1)
  have hm : AEStronglyMeasurable (fun z : Fin n⊕Fin r→ℝ =>
      gaussianMixedTest f (gaussianRows (freshNoiseRows v s) (WithLp.toLp 2 z)))
      (Measure.pi fun _ => gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  have he : (fun p : (Fin n→ℝ)×(Fin r→ℝ) =>
      gaussianMixedTest f (gaussianRows (freshNoiseRows v s)
        (WithLp.toLp 2 ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin r => ℝ)).symm p))))=F := by
    funext p
    simp only [gaussianMixedTest_apply,gaussianRows_apply]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (f i) (freshNoiseRows_apply v s p.1 p.2 i)
  rw [he,integral_prod _ hF]
  have hi (x : Fin n→ℝ) : (∫ y : Fin r→ℝ, F (x,y) ∂Measure.pi (fun _ => gaussianReal 0 1))=
      gaussianMixedTest (fun i => gaussianAverageBCF s (f i)) (gaussianRows v (WithLp.toLp 2 x)) := by
    rw [gaussianMixedTest_apply]
    change (∫ y : Fin r→ℝ, ∏ i, f i (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y i)
      ∂Measure.pi (fun _ => gaussianReal 0 1))=_
    rw [integral_fintype_prod_eq_prod (f := fun i y => f i (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y))]
    apply Finset.prod_congr rfl
    intro i hi
    exact (gaussianAverage_scaling s (f i) _).symm
  simp_rw [hi]
  rw [←freshMarkedMatrixKernel_gaussian,←map_pi_eq_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]

lemma countableFreshMixed_diagonal {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ) (s : ℝ≥0) (xs : Fin r→S) :
    (∫ g, ∏ i, gaussianAverageBCF s (f i) (countableGaussianField v L g (xs i)) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel (gaussianMixedTest f)
        (fun i j => countableGaussianCovariance v v L (xs i) (xs j) + if i=j then (s:ℝ) else 0) := by
  have h := countableFreshMarkedKernel v L (gaussianMixedTest (fun i => gaussianAverageBCF s (f i))) xs
  simp only [gaussianMixedTest_apply] at h
  rw [h]
  obtain ⟨n,w,hw⟩ := countableGaussianCovariance_finite_gram v L r xs
  have he (i j : Fin r) := congrFun (congrFun hw i) j
  simp_rw [←he]
  exact (freshMixedKernel_diagonal_noise f w s).symm

variable {S : Type} [MeasurableSpace S] {k r : ℕ}

lemma labelProfile_mixed_kernel (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (f : Fin r→ℝ →ᵇ ℝ) (xs : Fin r→S×IndexedLeaf k) :
    (∫ g, ∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (f i)
      (labelProfileField q g (xs i)) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel (gaussianMixedTest f)
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) := by
  have h := countableFreshMixed_diagonal (labelProfileRow q)
    (indexedGaussianRowLength (I := Fin 1) k) f (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) xs
  apply h.trans
  apply congrArg (freshMarkedMatrixKernel (gaussianMixedTest f))
  funext i j
  rw [labelProfile_covariance q h0 hq]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,indexedCommonDepth_self]
    change q (Fin.last k)+(1-q (Fin.last k))=1
    ring
  · simp only [ite_eq_right hij,add_zero]

lemma labelProfileField_product_measurable (q : Fin (k+1)→ℝ) :
    Measurable (fun p : (ℕ→ℝ)×(S×IndexedLeaf k) => labelProfileField q p.1 p.2) :=
  countableGaussianField_measurable (v := labelProfileRow q)
    (indexedGaussianRow_measurable k _ measurable_const)
    (indexedGaussianRowLength_measurable (I := Fin 1) k)

lemma measurableReplicaProduct {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (V : A→B→ℝ) (hV : Measurable (Function.uncurry V)) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (fun p : A×(Fin r→B) => ∏ i, f i (V p.1 (p.2 i))) := by
  have h (i : Fin r) : Measurable (fun p : A×(Fin r→B) => f i (V p.1 (p.2 i))) :=
    (f i).measurable.comp (hV.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact Finset.measurable_prod Finset.univ (fun i _ => h i)

lemma labelMixedValue_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelMixedValue (S:=S) q s f)) :=
  measurableReplicaProduct (labelProfileField q) (labelProfileField_product_measurable q)
    (fun i => gaussianAverageBCF s (f i))

lemma labelMixedValue_bound {S : Type} [MeasurableSpace S] {k r : ℕ}
    (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ)
    (z : ℕ→ℝ) (xs : Fin r→S×IndexedLeaf k) :
    |labelMixedValue q s f z xs|≤∏ i, ‖gaussianAverageBCF s (f i)‖ := by
  simp only [labelMixedValue,Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun index _ =>
    (gaussianAverageBCF s (f index)).norm_coe_le_norm _)

lemma labelTwoMixed_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f g : Fin r→ℝ →ᵇ ℝ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F) :
    Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) =>
      F p.2 * labelMixedValue q s f p.1.1 p.2 * labelMixedValue q s g p.1.2 p.2) := by
  have hf := (labelMixedValue_measurable (S:=S) q s f).comp
    (measurable_fst.fst.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.1,p.2)))
  have hg := (labelMixedValue_measurable (S:=S) q s g).comp
    (measurable_fst.snd.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.2,p.2)))
  exact ((hF.comp measurable_snd).mul hf).mul hg

lemma labelProfile_twoMixed_fubini (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (ν : Measure (Fin r→S×IndexedLeaf k)) [IsProbabilityMeasure ν]
    (f g : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ xs, |F xs|≤C) :
    (∫ z, ∫ xs, F xs *
      (∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (f i) (labelProfileField q z.1 (xs i))) *
      (∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (g i) (labelProfileField q z.2 (xs i))) ∂ν
      ∂countableGaussianLaw.prod countableGaussianLaw) =
    ∫ xs, F xs * freshMarkedMatrixKernel (gaussianMixedTest f)
      (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) *
      freshMarkedMatrixKernel (gaussianMixedTest g)
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) ∂ν := by
  let s : ℝ≥0 := (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0)
  have hm := labelTwoMixed_measurable q s f g F hF
  have hi : Integrable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) =>
      F p.2 * (∏ i, gaussianAverageBCF s (f i) (labelProfileField q p.1.1 (p.2 i))) *
        (∏ i, gaussianAverageBCF s (g i) (labelProfileField q p.1.2 (p.2 i))))
      ((countableGaussianLaw.prod countableGaussianLaw).prod ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (C*(∏ i, ‖gaussianAverageBCF s (f i)‖)*(∏ i, ‖gaussianAverageBCF s (g i)‖))
    exact ae_of_all _ fun p => by
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (hb _) (labelMixedValue_bound q s f p.1.1 p.2)
          (abs_nonneg _) hC) (labelMixedValue_bound q s g p.1.2 p.2)
        (abs_nonneg _) (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))

  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun xs => by
    change (∫ z, F xs * labelMixedValue q s f z.1 xs * labelMixedValue q s g z.2 xs
      ∂countableGaussianLaw.prod countableGaussianLaw)=_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    apply congrArg (fun y => F xs*y)
    calc
      _ = (∫ z, labelMixedValue q s f z xs ∂countableGaussianLaw)*
          (∫ z, labelMixedValue q s g z xs ∂countableGaussianLaw) := integral_prod_mul _ _
      _ = _ := congrArg₂ (·*·) (labelProfile_mixed_kernel q h0 hq h1 f xs)
        (labelProfile_mixed_kernel q h0 hq h1 g xs)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_TiltedPathDiagonal
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
variable {X Y R Q : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace R] [MeasurableSpace Q]

lemma rootPathCorrelation_one (μ : Measure R) [IsProbabilityMeasure μ]
    (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X) (hκ : ∀ i, IsMarkovKernel (κ i))
    (d : Fin (n+1)) : rootPathCorrelation μ x n κ (fun _=>1) d=1 := by
  simp only [rootPathCorrelation,pathCorrelation_one n κ hκ,integral_const,probReal_univ,one_smul]

open scoped ENNReal NNReal BoundedContinuousFunction

lemma residualResponse_one (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    residualResponse s f 1 x=1 := by
  change gaussianAverage s (expBCF 1 f * 1 : ℝ →ᵇ ℝ) x / _=1
  rw [mul_one]
  exact div_self (gaussianAverage_exp_pos s 1 f x).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S : Type} [MeasurableSpace S] {k : ℕ}

lemma replicaFrontLift_measurable {r : ℕ} {F : (Fin r→S)→ℝ}
    (hF : Measurable F) (j : ℕ) : Measurable (replicaFrontLift F j) := by
  induction j with
  | zero => exact hF
  | succ j hj => exact hj.comp (Measurable.of_eval fun coordinate => measurable_pi_apply coordinate.succ)

omit [MeasurableSpace S] in
lemma replicaFrontLift_bound {r : ℕ} {F : (Fin r→S)→ℝ} {C : ℝ}
    (hF : ∀ x, |F x|≤C) (j : ℕ) (x : Fin (r+j)→S) : |replicaFrontLift F j x|≤C := by
  induction j with
  | zero => exact hF x
  | succ j hj => exact hj _

omit [MeasurableSpace S] in
lemma labelRestorationTest_replica {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (j : ℕ) (x : Fin (r+j)→S×IndexedLeaf k) :
    restorationReplicaTest r (labelRestorationWeight q s f z) (labelRestorationTest q s f v w F z) j x =
      replicaFrontLift F j x * labelMixedValue q s (labelRestoredFunctions f v j) z.1 x *
        labelMixedValue q s (labelRestoredFunctions f w j) z.2 x := by
  induction j with
  | zero => rfl
  | succ j hj =>
    change labelRestorationWeight q s f z (x 0) *
      restorationReplicaTest r (labelRestorationWeight q s f z) (labelRestorationTest q s f v w F z) j (fun i => x i.succ) = _
    rw [hj]
    simp only [Nat.add_succ,replicaFrontLift,labelMixedValue,labelRestoredFunctions,Fin.prod_univ_succ,
      Fin.cons_zero,Fin.cons_succ,labelRestorationWeight]
    ring

lemma labelRestorationWeight_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) : Measurable (labelRestorationWeight (S:=S) q s f z) := by
  have hm (a : ℕ→ℝ) : Measurable (fun x : S×IndexedLeaf k =>
      gaussianAverageBCF s (expBCF 1 f) (labelProfileField q a x)) :=
    by
      have hp : Measurable (fun x : S×IndexedLeaf k => (a,x)) := measurable_const.prodMk measurable_id
      have hfield := (labelProfileField_product_measurable (S:=S) q).comp hp
      exact (gaussianAverageBCF s (expBCF 1 f)).measurable.comp hfield
  exact (hm z.1).mul (hm z.2)

omit [MeasurableSpace S] in
lemma labelRestorationWeight_bound (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) :
    |labelRestorationWeight q s f z x|≤‖gaussianAverageBCF s (expBCF 1 f)‖^2 := by
  rw [labelRestorationWeight,abs_mul,pow_two]
  exact mul_le_mul ((gaussianAverageBCF s (expBCF 1 f)).norm_coe_le_norm _)
    ((gaussianAverageBCF s (expBCF 1 f)).norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)

lemma labelRestorationTest_measurable {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} (hF : Measurable F)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) : Measurable (labelRestorationTest q s f v w F z) :=
  (labelTwoMixed_measurable q s (fun i => expBCF 1 f*v i) (fun i => expBCF 1 f*w i) F hF).comp
    (measurable_const.prodMk measurable_id)

lemma labelRestorationTest_bound {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ x, |F x|≤C) (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : Fin r→S×IndexedLeaf k) :
    |labelRestorationTest q s f v w F z x|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  simp only [labelRestorationTest,abs_mul]
  exact mul_le_mul (mul_le_mul (hF _) (labelMixedValue_bound q s _ _ _) (abs_nonneg _) hC)
    (labelMixedValue_bound q s _ _ _) (abs_nonneg _)
    (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))

lemma labelRestoration_moments {r : ℕ} (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (v w : Fin r→ℝ →ᵇ ℝ)
    (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ] (H : (S×IndexedLeaf k)→ℝ)
    (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F) {C : ℝ} (hC : 0≤C)
    (hb : ∀ x, |F x|≤C) (j : ℕ) :
    let s : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩
    (∫ z, (tiltMean μ H (labelRestorationWeight q s f z) 1)^j *
      gibbsReplicaMean μ H r (labelRestorationTest q s f v w F z)
      ∂countableGaussianLaw.prod countableGaussianLaw) =
    gibbsReplicaMean μ H (r+j) (fun xs => replicaFrontLift F j xs *
      freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f v j))
        (fun i l => if i=l then 1 else q (indexedCommonDepth k (xs l).2 (xs i).2)) *
      freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f w j))
        (fun i l => if i=l then 1 else q (indexedCommonDepth k (xs l).2 (xs i).2))) := by
  intro s
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  have he (z : (ℕ→ℝ)×(ℕ→ℝ)) := restoration_replica_moment μ hH
    (labelRestorationWeight_measurable q s f z) (labelRestorationTest_measurable q s f v w hF z) hi
    (sq_nonneg _) (mul_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    (labelRestorationWeight_bound q s f z) (labelRestorationTest_bound q s f v w hC hb z) j
  simp_rw [←he,gibbsReplicaMean_integral_of_integrable μ hH hi,labelRestorationTest_replica]
  exact labelProfile_twoMixed_fubini q h0 hq h1 (Measure.pi fun _ : Fin (r+j) => tiltLaw μ H 1)
    (labelRestoredFunctions f v j) (labelRestoredFunctions f w j) (replicaFrontLift F j)
    (replicaFrontLift_measurable hF j) hC (replicaFrontLift_bound hb j)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationKernel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A : Type*} {S : Type} [MeasurableSpace A] [MeasurableSpace S] {k r : ℕ}

lemma labelRestorationWeight_joint (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelRestorationWeight (S:=S) q s f)) := by
  have h₁ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.1,p.2)) from
      measurable_fst.fst.prodMk measurable_snd)
  have h₂ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.2,p.2)) from
      measurable_fst.snd.prodMk measurable_snd)
  exact ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₁).mul
    ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₂)

lemma labelRestorationWeight_exp {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) :
    labelRestorationWeight q s f z x =
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) := by
  have he (a : ℝ) : Real.exp (heatLog s 1 f a)=gaussianAverageBCF s (expBCF 1 f) a := by
    simpa only [NNReal.coe_one,one_mul,gaussianAverageBCF_coe] using exp_heatLog s 1 (by norm_num) f a
  simp only [Real.exp_add,he,labelRestorationWeight]

variable (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
variable (H : A → S×IndexedLeaf k → ℝ)
variable (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
variable (v w : Fin r → ℝ →ᵇ ℝ) (F : (Fin r → S×IndexedLeaf k) → ℝ)

lemma labelKernelDenominator_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (labelKernelDenominator κ H q s f) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hW := (labelRestorationWeight_joint (S:=S) q s f).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_tiltMean_measurable (κ.comap Prod.fst measurable_fst) hH' hW

lemma labelKernelNumerator_measurable (hH : Measurable (Function.uncurry H)) (hF : Measurable F) :
    Measurable (labelKernelNumerator κ H q s f v w F) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hG := (labelTwoMixed_measurable (S:=S) q s (fun i => expBCF 1 f*v i)
    (fun i => expBCF 1 f*w i) F hF).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(Fin r → S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_replicaMean_measurable (κ.comap Prod.fst measurable_fst) hH' hG

lemma labelKernelNumerator_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (a : A×((ℕ→ℝ)×(ℕ→ℝ))) :
    |labelKernelNumerator κ H q s f v w F a|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  apply tiltMean_bound_general (Measure.pi fun _ : Fin r => κ a.1)
    (replicaPotential_measurable hH.of_uncurry_left r)
    (labelRestorationTest_measurable q s f v w hF a.2)
    (mul_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  exact labelRestorationTest_bound q s f v w hC hb a.2

lemma labelKernelDenominator_bounds (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    labelKernelDenominator κ H q s f (a,z) ∈ Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) := by
  have hm (g : ℕ→ℝ) : Measurable (fun x : S×IndexedLeaf k => heatLog s 1 f (labelProfileField q g x)) := by
    have hp := (labelProfileField_product_measurable (S:=S) q).of_uncurry_left (x:=g)
    exact (heatLog_continuous s 1 f).measurable.comp hp
  have hb (x : S×IndexedLeaf k) :
      |heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)|≤2*‖f‖ :=
    (abs_add_le _ _).trans ((add_le_add (heatLog_abs_le s 1 f _) (heatLog_abs_le s 1 f _)).trans_eq
      (two_mul ‖f‖).symm)
  have he := tiltMean_exp_bounds (κ a) hH.of_uncurry_left ((hm z.1).add (hm z.2)) hi
    (mul_nonneg (by norm_num) (norm_nonneg f)) hb
  have hw : labelRestorationWeight (S:=S) q s f z = fun x =>
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) :=
    funext (labelRestorationWeight_exp q s f z)
  simpa only [labelKernelDenominator,hw,Set.mem_Icc,Pi.add_apply] using he

lemma restorationClip_measurable (f : ℝ →ᵇ ℝ) : Measurable (restorationClip f) :=
  (measurable_const.max (measurable_const.min measurable_id)).subtype_mk
lemma restorationClip_eq (f : ℝ →ᵇ ℝ) {x : ℝ} (hx : x∈RestorationRange f) :
    (restorationClip f x).val=x := by
  dsimp [restorationClip]
  rw [min_eq_right hx.2,max_eq_right hx.1]

lemma gaussianAverageBCF_norm_le (s : ℝ≥0) (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖≤‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
  exact gaussianAverage_abs_le s f

lemma labelKernelCompactDenominator_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (labelKernelCompactDenominator κ H q s f) :=
  (restorationClip_measurable f).comp (labelKernelDenominator_measurable κ H q s f hH)

lemma labelKernelCompactDenominator_eq (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    (labelKernelCompactDenominator κ H q s f (a,z)).val=labelKernelDenominator κ H q s f (a,z) :=
  restorationClip_eq f (labelKernelDenominator_bounds κ H q s f hH hi z)

lemma labelKernelNumerator_uniform_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (a : A×((ℕ→ℝ)×(ℕ→ℝ))) :
    |labelKernelNumerator κ H q s f v w F a|≤
      C*(∏ i, ‖expBCF 1 f*v i‖)*(∏ i, ‖expBCF 1 f*w i‖) := by
  refine (labelKernelNumerator_bound κ H q s f v w F hH hF hC hb a).trans ?_
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ hC
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => gaussianAverageBCF_norm_le s _)
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => gaussianAverageBCF_norm_le s _)
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)

lemma labelKernel_weighted_integrable (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (P : Measure A) [IsFiniteMeasure P]
    (J : C(RestorationRange f,ℝ)) :
    Integrable (fun a => labelKernelNumerator κ H q s f v w F a * J (labelKernelCompactDenominator κ H q s f a))
      (P.prod (countableGaussianLaw.prod countableGaussianLaw)) :=
  weighted_compact_integrable _ _ (labelKernelNumerator_measurable κ H q s f v w F hH hF)
    _ (labelKernelCompactDenominator_measurable κ H q s f hH) _ (by positivity)
    (labelKernelNumerator_uniform_bound κ H q s f v w F hH hF hC hb) J

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelRestorationMoments2
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma jointRestorationBlockTest_source (N k r : ℕ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (j : ℕ) (x : Fin (r+j) → NormalizedSpin N×IndexedLeaf k) :
    jointRestorationBlockTest r F j (fun i l => sourceJointOverlap (x i) (x l)) =
      replicaFrontLift (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
        F (fun i l => sourceJointOverlap (x i) (x l))) j x := by
  induction j with
  | zero => rfl
  | succ j hj => exact hj _

lemma labelMarkedBlockKernel_source {N k r : ℕ} (q : Fin (k+1) → ℝ)
    (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (x : Fin r → NormalizedSpin N×IndexedLeaf k) :
    labelMarkedBlockKernel q Ψ (fun i l => sourceJointOverlap (x i) (x l)) =
      freshMarkedMatrixKernel Ψ (fun i l => if i=l then 1 else q (indexedCommonDepth k (x l).2 (x i).2)) := by
  apply congrArg (freshMarkedMatrixKernel Ψ)
  funext i l
  change (if i=l then 1 else labelProfileInterpolant q (sourceJointOverlap (x i) (x l)).2)=_
  split_ifs with hi
  · rfl
  · exact labelProfileInterpolant_node q _

lemma labelRestoration_to_block (N k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (μ : Measure (NormalizedSpin N×IndexedLeaf k)) [IsProbabilityMeasure μ]
    (H : NormalizedSpin N×IndexedLeaf k → ℝ) (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (j : ℕ) :
    (∫ b, (tiltMean μ H (labelRestorationWeight q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) ψ b) 1)^j *
      gibbsReplicaMean μ H r (labelRestorationTest q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) ψ v w
        (fun x => F (fun i l => sourceJointOverlap (x i) (x l))) b)
        ∂countableGaussianLaw.prod countableGaussianLaw) =
      gibbsReplicaMean μ H (r+j) (fun x => labelRestorationBlockMoment q ψ v w F j
        (fun i l => sourceJointOverlap (x i) (x l))) := by
  have hp (i l : Fin r) : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k => (x i,x l)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply l)
  have hc (i l : Fin r) := (sourceJointOverlap_measurable N k).comp (hp i l)
  have hblock : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
      fun i l => sourceJointOverlap (x i) (x l)) :=
    Measurable.of_eval fun row => Measurable.of_eval fun column => hc row column
  have hF := F.measurable.comp hblock
  have he := labelRestoration_moments q h0 hq h1 ψ v w μ H hH hi _ hF
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) j
  refine he.trans ?_
  apply congrArg (gibbsReplicaMean μ H (r+j))
  funext x
  simp only [labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    labelMarkedBlockKernel_source,jointRestorationBlockTest_source]
  rfl

lemma sourceLabelRestorationMoment_array (n k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) (j : ℕ) :
    sourceLabelRestorationMoment n k r q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) f ψ v w F p d h u z t j =
      ∫ Q, labelRestorationBlockMoment q ψ v w F j (compactBlock (r+j) Q) ∂sourceGibbsArrayLaw n k f p d h u z t := by
  refine Eq.trans ?_ (sourceGibbsArray_block_integral n k f p d h hh0 hh u z t (r+j)
    (F := fun Q => labelRestorationBlockMoment q ψ v w F j Q)
    (labelRestorationBlockMoment q ψ v w F j).measurable
    (fun Q => (labelRestorationBlockMoment q ψ v w F j).norm_coe_le_norm Q)).symm
  unfold sourceLabelRestorationMoment
  apply integral_congr_ae
  filter_upwards [sourceFresh_exp_ae n k f p d h hh0 hh u z t] with a ha
  exact labelRestoration_to_block (n+1) k r q h0 hq h1 ψ v w F _ _
    (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left ha j

lemma sourceLabelRestorationMoment_tendsto (k r : ℕ) (q : Fin (k+1) → ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
    (p d : (n : ℕ) → Fin (n+1) → ℕ) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n)) (u : (n : ℕ) → Fin (n+1) → ℝ)
    (z : Fin k → ℝ) (t : ℕ → ℝ≥0) (s : ℕ → ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (j : ℕ) :
    Tendsto (fun n => sourceLabelRestorationMoment (s n) k r q (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0)
      f ψ v w F (p (s n)) (d (s n)) (h (s n)) (u (s n)) z (t (s n)) j) atTop
      (𝓝 (∫ Q, labelRestorationBlockMoment q ψ v w F j (compactBlock (r+j) Q) ∂ν)) := by
  simp_rw [sourceLabelRestorationMoment_array _ _ _ _ h0 hq h1 _ _ _ _ _ _ _ _ (hh0 _) (hh _)]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    ((labelRestorationBlockMoment q ψ v w F j).compContinuous
      ⟨compactBlock (r+j),compactBlock_continuous (r+j)⟩)).continuousAt.tendsto.comp hlim

lemma sourceReplicaBlock_measurable (N k r : ℕ) :
    Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
      fun i l => sourceJointOverlap (x i) (x l)) := by
  have hp (i l : Fin r) : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k => (x i,x l)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply l)
  have hc (i l : Fin r) := (sourceJointOverlap_measurable N k).comp (hp i l)
  exact Measurable.of_eval fun row => Measurable.of_eval fun column => hc row column

variable (n k r : ℕ) (q : Fin (k+1) → ℝ) (s : ℝ≥0)
variable (f ψ : ℝ →ᵇ ℝ) (v w : Fin r → ℝ →ᵇ ℝ) (F : CompactBlock CompactJointOverlap r →ᵇ ℝ)
variable (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ)
variable (z : Fin k → ℝ) (t : ℝ≥0)

lemma sourceLabelRestorationNumerator_measurable :
    Measurable (sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u) :=
  labelKernelNumerator_measurable _ _ _ _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    (F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r))

lemma sourceLabelRestorationDenominator_measurable :
    Measurable (sourceLabelRestorationDenominator n k q s f ψ p d h u) :=
  labelKernelCompactDenominator_measurable _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)

lemma sourceLabelRestorationNumerator_bound (a) :
    |sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a|≤
      ‖F‖*(∏ i, ‖expBCF 1 ψ*v i‖)*(∏ i, ‖expBCF 1 ψ*w i‖) :=
  labelKernelNumerator_uniform_bound _ _ _ _ _ _ _ _ (sourceCouplingHamiltonian_measurable n k f p d h u)
    (F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r)) (norm_nonneg F)
    (fun _ => F.norm_coe_le_norm _) a

lemma sourceLabelRestorationPolynomial (hh0 : ∀ i,0≤h i) (hh : Monotone h) (j : ℕ) :
    (∫ a, sourceLabelRestorationNumerator n k r q s f ψ v w F p d h u a *
      (sourceLabelRestorationDenominator n k q s f ψ p d h u a).val^j
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw)) =
    sourceLabelRestorationMoment n k r q s f ψ v w F p d h u z t j := by
  let κ := sourceFullSpinLeafKernel n k
  let H := sourceCouplingHamiltonian n k f p d h u
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let T := fun x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k => F (fun i l => sourceJointOverlap (x i) (x l))
  have hH := sourceCouplingHamiltonian_measurable n k f p d h u
  have hT := F.measurable.comp (sourceReplicaBlock_measurable (n+1) k r)
  have hF := sourceFresh_exp_ae n k f p d h hh0 hh u z t
  let J : C(RestorationRange ψ,ℝ) := ⟨fun x => x.val^j,continuous_subtype_val.pow j⟩
  have hI := labelKernel_weighted_integrable κ H q s ψ v w T hH hT
    (norm_nonneg F) (fun x => F.norm_coe_le_norm _) P J
  have hae := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hF
  have hEq : (fun a => labelKernelNumerator κ H q s ψ v w T a * J (labelKernelCompactDenominator κ H q s ψ a)) =ᵐ[P.prod (countableGaussianLaw.prod countableGaussianLaw)]
      (fun a => labelKernelNumerator κ H q s ψ v w T a * (labelKernelDenominator κ H q s ψ a)^j) := by
    filter_upwards [hae] with a ha
    dsimp only [J,ContinuousMap.coe_mk]
    rw [labelKernelCompactDenominator_eq κ H q s ψ hH ha a.2]
  have hi := hI.congr hEq
  change (∫ a, labelKernelNumerator κ H q s ψ v w T a * J (labelKernelCompactDenominator κ H q s ψ a) ∂P.prod _) = _
  rw [integral_congr_ae hEq,integral_prod _ hi]
  unfold sourceLabelRestorationMoment
  apply integral_congr_ae
  exact ae_of_all _ fun a => integral_congr_ae (ae_of_all _ fun b => mul_comm _ _)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelPairTestValue
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma scalarFrontMatrixTest_label {k : ℕ} (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactJointOverlap (2+j)) :
    scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (labelProfileGram q Q) =
      jointRestorationBlockTest 2 (labelProfilePairTest q F) j Q := by
  induction j with
  | zero =>
    change F (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ)≤1) (if (1 : Fin 2)=0 then 1 else (labelProfileSpin q (Q 1 0).2).val)) = _
    simp only [show (1 : Fin 2) ≠ 0 by decide,ite_false,Set.projIcc_of_mem _ (labelProfileSpin q (Q 1 0).2).prop]
    rfl
  | succ j hj =>
    change scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (fun i l => labelProfileGram q Q i.succ l.succ) = _
    have he : (fun i l => labelProfileGram q Q i.succ l.succ)=labelProfileGram q (fun i l => Q i.succ l.succ) := by
      funext i l
      simp only [labelProfileGram,Fin.succ_inj]
    exact (congrArg (fun M : Matrix (Fin (2+j)) (Fin (2+j)) ℝ => scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j M) he).trans (hj _)

lemma labelMarkedBlockKernel_profile {k r : ℕ} (q : Fin (k+1)→Time)
    (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (Q : CompactBlock CompactJointOverlap r)
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    labelMarkedBlockKernel (fun i => (q i:ℝ)) Ψ Q = freshMarkedMatrixKernel Ψ (labelProfileGram q Q) := by
  apply congrArg (freshMarkedMatrixKernel Ψ)
  funext i l
  change (if i=l then 1 else labelProfileInterpolant (fun i => (q i:ℝ)) (Q i l).2)=_
  by_cases hil : i=l
  · simp only [hil,labelProfileGram,ite_true]
  · obtain ⟨d,hd⟩ := hN i l
    simp only [labelProfileGram,ite_eq_right hil,←hd,labelProfileInterpolant_node,labelProfileSpin_node,timeSpin]

lemma scalarRestorationPairMoment_label {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ)
    (Q : CompactBlock CompactJointOverlap (2+j))
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    scalarRestorationPairMoment f v w F j (labelProfileGram q Q) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ => v) (fun _ => w)
        (labelProfilePairTest q F) j Q := by
  simp only [scalarRestorationPairMoment,labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    scalarFrontMatrixTest_label,labelMarkedBlockKernel_profile q _ Q hN]

lemma scalarRestorationPairMoment_diagonalMap {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ)
    (Q : CompactArray CompactJointOverlap) (hN : CompactLabelNodes k Q) :
    scalarRestorationPairMoment f v w F j (fun i l =>
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ => v) (fun _ => w)
        (labelProfilePairTest q F) j (compactBlock (2+j) Q) := by
  have he : (fun i l : Fin (2+j) => (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val)=
      labelProfileGram q (compactBlock (2+j) Q) := by
    funext i l
    simp only [compactDiagonalMapArray,labelProfileGram,Fin.val_inj]
    split_ifs <;> rfl
  rw [he]
  exact scalarRestorationPairMoment_label q f v w F j _ (fun i l => hN i l)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CompactRestorationWitness
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

lemma compactWeightedLaw_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (C : ℝ)
    (A : Ω→ℝ) (hA : Measurable A) (Z : Ω→RestorationRange f) (hZ : Measurable Z)
    (hb : ∀ x, |A x|≤C) (J : WeightedRestorationRange f C → ℝ) (hJ : Measurable J) :
    (∫ x, J x ∂(compactWeightedLaw μ f C A hA Z hZ hb : Measure _))=
      ∫ x, J (⟨A x,abs_le.mp (hb x)⟩,Z x) ∂μ :=
  integral_map ((hA.subtype_mk).prodMk hZ).aemeasurable hJ.aestronglyMeasurable

lemma compactWeighted_witness {Ω : ℕ→Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ)→Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ℝ →ᵇ ℝ) (C : ℝ) (A : (n : ℕ)→Ω n→ℝ) (Z : (n : ℕ)→Ω n→RestorationRange f)
    (hA : ∀ n, Measurable (A n)) (hZ : ∀ n, Measurable (Z n)) (hb : ∀ n x, |A n x|≤C)
    (b : ℕ→ℝ) (hm : ∀ j, Tendsto (fun n => ∫ x, A n x*(Z n x).val^j ∂μ n) atTop (𝓝 (b j)))
    (J : C(RestorationRange f,ℝ)) (L : ℝ)
    (hL : Tendsto (fun n => ∫ x, A n x*J (Z n x) ∂μ n) atTop (𝓝 L)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange f C),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange f C)))=b j) ∧
      (∫ x, x.1.val*J x.2 ∂(η : Measure (WeightedRestorationRange f C)))=L := by
  let ν n := compactWeightedLaw (μ n) f C (A n) (hA n) (Z n) (hZ n) (hb n)
  obtain ⟨η,-,s,hs,hlim⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ν n))
  have ht (G : C(WeightedRestorationRange f C,ℝ)) :
      Tendsto (fun n => ∫ x, G x ∂(ν (s n) : Measure (WeightedRestorationRange f C))) atTop (𝓝 (∫ x, G x ∂(η : Measure (WeightedRestorationRange f C)))) := by
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact G)).continuousAt.tendsto.comp hlim
  refine ⟨η,?_,?_⟩
  · intro j
    let G : C(WeightedRestorationRange f C,ℝ) := ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    have hh := ht G
    simp only [ν,compactWeightedLaw_integral _ _ _ _ _ _ _ _ _ G.continuous.measurable] at hh
    exact tendsto_nhds_unique hh ((hm j).comp hs.tendsto_atTop)
  · let G : C(WeightedRestorationRange f C,ℝ) := ⟨fun x => x.1.val*J x.2,
      (continuous_subtype_val.comp continuous_fst).mul (J.continuous.comp continuous_snd)⟩
    have hh := ht G
    simp only [ν,compactWeightedLaw_integral _ _ _ _ _ _ _ _ _ G.continuous.measurable] at hh
    exact tendsto_nhds_unique hh (hL.comp hs.tendsto_atTop)

lemma sourceLabelRestorationNumerator_pair_bound (n k : ℕ) (f ψ v w : ℝ →ᵇ ℝ)
    (F : CompactOverlap →ᵇ ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a) :
    |sourceLabelRestorationNumerator n k 2 (fun i => (q i:ℝ)) s f ψ
      (fun _ => v) (fun _ => w) (labelProfilePairTest q F) p e h u a|≤pairRestorationBound ψ v w F := by
  apply (sourceLabelRestorationNumerator_bound n k 2 _ s f ψ (fun _ => v) (fun _ => w)
    (labelProfilePairTest q F) p e h u a).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  exact F.norm_compContinuous_le _

lemma sourceLabelPair_witness (k : ℕ) (q : Fin (k+1)→Time) (hq : Monotone q)
    (f : ℝ →ᵇ ℝ) (g : Jet3) (v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ)
    (p e : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i,0≤h n i) (hh : ∀ n,Monotone (h n)) (u : (n : ℕ)→Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (t : ℕ→ℝ≥0) (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (e (s n)) (h (s n))
      (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F)),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F))))=
        ∫ Q, labelRestorationBlockMoment (fun i => (q i:ℝ)) g.f (fun _ => v) (fun _ => w)
          (labelProfilePairTest q F) j (compactBlock (2+j) Q) ∂ν) ∧
      (∫ x, x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F))))=
        ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
          (labelPairCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v d *
           labelPairCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) w d) := by
  let τ : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩
  apply compactWeighted_witness
    (fun n => ((sourceBaseDataLaw (s n) k z (t (s n))).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw))
    g.f (pairRestorationBound g.f v w F)
    (fun n => sourceLabelRestorationNumerator (s n) k 2 (fun i => (q i:ℝ)) τ f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationDenominator (s n) k (fun i => (q i:ℝ)) τ f g.f
      (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationNumerator_measurable ..)
    (fun n => sourceLabelRestorationDenominator_measurable ..)
    (fun n a => sourceLabelRestorationNumerator_pair_bound ..) _ ?_ (restorationReciprocal g.f 2) _ ?_
  · intro j
    simp_rw [sourceLabelRestorationPolynomial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hh0 _) (hh _) j]
    exact sourceLabelRestorationMoment_tendsto k 2 (fun i => (q i:ℝ)) (q 0).prop.1
      (fun i l hil => hq hil) (q (Fin.last k)).prop.2 f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) p e h hh0 hh u z t s hlim j
  · change Tendsto (fun n => sourceLabelRestorationRatio (s n) k 2 (fun i => (q i:ℝ)) τ f g.f
      (fun _ => v) (fun _ => w) (labelProfilePairTest q F) (p (s n)) (e (s n)) (h (s n)) (u (s n)) z (t (s n))) atTop _
    simp_rw [sourceLabelRestorationRatio_pair_value _ k f g _ _ _ (hh0 _) (hh _) _ q τ v w F z hz hz0 hz1]
    exact tendsto_const_nhds

lemma labelPairCoefficient_one (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) :
    labelPairCoefficient k z q g s 1 d=1 := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  simp only [labelPairCoefficient,labelResidualObservable,residualResponse_one]
  exact rootPathCorrelation_one _ _ k _ hκ d

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileUpperTail
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

lemma unit_valued_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {q : Time→Time} (hq : Measurable q) : Integrable (fun u => (q u:ℝ)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_subtype_coe.comp hq).aestronglyMeasurable
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (q u).property.1]
    exact (q u).property.2

lemma uniformQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileLower n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (show i.castSucc ≤ j.castSucc from hij))
lemma uniformQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (uniformQuantileUpper n q) := by
  intro i j hij
  exact hq ((uniformQuantileGrid_strict n).monotone (Fin.succ_le_succ_iff.mpr hij))
lemma sampleQuantileLower_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileLower n q) :=
  (uniformQuantileLower_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantileUpper_mono (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    Monotone (sampleQuantileUpper n q) :=
  (uniformQuantileUpper_mono n hq).comp (uniformQuantileCell_mono n)
lemma sampleQuantile_bracket (n : ℕ) {q : Time→Time} (hq : Monotone q) (u : Time) :
    sampleQuantileLower n q u ≤ q u ∧ q u ≤ sampleQuantileUpper n q u :=
  ⟨hq (uniformQuantileCell_bounds n u).1,hq (uniformQuantileCell_bounds n u).2⟩

lemma sampleQuantile_gap_integral (n : ℕ) (q : Time→Time) :
    (∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw)=
      ((q 1:ℝ)-q 0)/(n+1:ℝ) := by
  change (∫ u, (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i)
    (uniformQuantileCell n u) ∂timeLaw)=_
  rw [uniformQuantileCell_integral n (fun i => (uniformQuantileUpper n q i:ℝ)-uniformQuantileLower n q i),← Finset.mul_sum]
  unfold uniformQuantileUpper uniformQuantileLower
  rw [finite_sum_successive_differences (n+1) (fun i => (q (uniformQuantileGrid n i):ℝ)),
    uniformQuantileGrid_last,uniformQuantileGrid_zero]
  ring

lemma sampleQuantileLower_L1 (n : ℕ) {q : Time→Time} (hq : Monotone q) :
    (∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw) ≤ 1/(n+1:ℝ) := by
  have hl := unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable
  have hu := unit_valued_integrable timeLaw (sampleQuantileUpper_mono n hq).measurable
  have hi := unit_valued_integrable timeLaw hq.measurable
  calc
    _  ≤  ∫ u, ((sampleQuantileUpper n q u:ℝ)-sampleQuantileLower n q u) ∂timeLaw := by
      apply integral_mono (hl.sub hi).abs (hu.sub hl)
      intro u
      have hb := sampleQuantile_bracket n hq u
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonpos (sub_nonpos.mpr (show (sampleQuantileLower n q u:ℝ) ≤ q u from hb.1))]
      have ht : (q u:ℝ) ≤ sampleQuantileUpper n q u := hb.2
      linarith
    _ = ((q 1:ℝ)-q 0)/(n+1:ℝ) := sampleQuantile_gap_integral n q
    _  ≤  1/(n+1:ℝ) := div_le_div_of_nonneg_right (by have := (q 1).2.2; have := (q 0).2.1; linarith) (by positivity)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_QuantileReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma unit_pow_abs_sub_le (a b : Time) (r : ℕ) :
    |(a:ℝ)^r-(b:ℝ)^r|≤(r:ℝ)*|(a:ℝ)-b| := by
  have hm : max |(a:ℝ)| |(b:ℝ)|≤1 := by
    rw [abs_of_nonneg a.prop.1,abs_of_nonneg b.prop.1]
    exact max_le a.prop.2 b.prop.2
  have hp : max |(a:ℝ)| |(b:ℝ)|^(r-1)≤1 := pow_le_one₀ (by positivity) hm
  calc
    _ ≤ |(a:ℝ)-b| *r*max |(a:ℝ)| |(b:ℝ)|^(r-1) := abs_pow_sub_pow_le ..
    _ ≤ |(a:ℝ)-b| *r*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

lemma unit_pow_integrable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (q : A→Time) (hq : Measurable q) (r : ℕ) : Integrable (fun u => (q u:ℝ)^r) μ := by
  apply Integrable.of_bound ((measurable_subtype_coe.comp hq).pow_const r).aestronglyMeasurable 1
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)^r‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (q u).prop.1 r)]
    exact pow_le_one₀ (q u).prop.1 (q u).prop.2

lemma sampleQuantileLower_moment_tendsto (q : Time→Time) (hq : Monotone q) (r : ℕ) :
    Tendsto (fun n => ∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw) atTop
      (𝓝 (∫ u, (q u:ℝ)^r ∂timeLaw)) := by
  have hz : Tendsto (fun n : ℕ => (r:ℝ)*(1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (r:ℝ)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
  rw [Real.dist_eq,←integral_sub (unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r)
    (unit_pow_integrable timeLaw q hq.measurable r)]
  calc
    _ ≤ ∫ u, |(sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r| ∂timeLaw := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun u => (sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r))
    _ ≤ ∫ u, (r:ℝ)*|(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := by
      apply integral_mono
        ((unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r).sub
          (unit_pow_integrable timeLaw q hq.measurable r)).abs
        (((unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable).sub
          (unit_valued_integrable timeLaw hq.measurable)).abs.const_mul (r:ℝ))
      exact fun u => unit_pow_abs_sub_le _ _ r
    _ = (r:ℝ)*∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := integral_const_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity)

lemma quantileSpinLaw_integral (q : Time→Time) (hq : Measurable q)
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ x, F x ∂(quantileSpinLaw q hq : Measure CompactOverlap))=∫ u, F (timeSpin (q u)) ∂timeLaw :=
  integral_map (timeSpin_continuous.measurable.comp hq).aemeasurable hF.aestronglyMeasurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LabelProfilePairReference
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem labelProfile_pair_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=
        ∑ d,w d*F (timeSpin (q d))*
          (labelPairCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
            (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v d *
           labelPairCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
            (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v' d) := by
  let p := fun n => (Nat.unpair n).1
  let d := fun n => (Nat.unpair n).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  obtain ⟨u,ρ,s,hu,hs,hlim,hGG,hex,hpair,hgeo⟩ := source_label_reference_exists k w hw hw1 p d hcover
  have hL := sourceGibbsArray_limit_label_geometry k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  have hN := sourceGibbsArray_limit_label_nodes k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  let ν := compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
  obtain ⟨η,hm,hl⟩ := sourceLabelPair_witness k q hq 0 g v v' F
    (fun _ j=>p j.val) (fun _ j=>d j.val) (fun _ _=>0) (fun _ _=>le_rfl)
    (fun _=>monotone_const) u (stepCumulative w) (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) (fun _=>0) s hlim
  refine ⟨ν,η,compactDiagonalMapLaw_gg _ _ _ _ ρ hGG,?_,?_,?_,?_⟩
  · change ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)).map
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal), CompactSpinGeometry Q
    apply (ae_map_iff (compactDiagonalMapArray_continuous (labelProfileMap_continuous q) labelProfileDiagonal_continuous).measurable.aemeasurable
      compactSpinGeometry_closed.measurableSet).mpr
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact labelProfileDiagonalMap_geometry q hq hLQ hNQ
  · intro A
    change (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _))=_
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => A (Q 0 1).1) (by fun_prop)]
    have he : (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=
        ∫ Q, A (labelProfileSpin q (Q 1 0).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)) := by
      apply integral_congr_ae
      filter_upwards [hL] with Q hLQ
      rw [show (Q 0 1).2=(Q 1 0).2 from Subtype.ext (hLQ.1 0 1)]
    change (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=_
    have hmap : (∫ x, A (labelProfileSpin q x) ∂((ρ : Measure (CompactArray CompactJointOverlap)).map
        (fun Q => (Q 1 0).2)))=∫ Q, A (labelProfileSpin q (Q 1 0).2)
          ∂(ρ : Measure (CompactArray CompactJointOverlap)) :=
      integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 1 0).2)
        from by fun_prop).aemeasurable
        (show Measurable (fun x : Time => A (labelProfileSpin q x)) from
          A.measurable.comp (labelProfileSpin_continuous q).measurable).aestronglyMeasurable
    rw [he,←hmap,hpair,sourceLabelLaw_integral k w (fun l => (hw l).le) (fun x => A (labelProfileSpin q x))
      (A.measurable.comp (labelProfileSpin_continuous q).measurable)]
    simp_rw [labelProfileSpin_node]
  · intro j
    rw [hm j]
    change _=∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val)
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal
        (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _)
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal
      (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val))
      ((scalarRestorationPairMoment g.f v v' F j).continuous.comp (by fun_prop)).measurable]
    apply integral_congr_ae
    filter_upwards [hN] with Q hNQ
    exact (scalarRestorationPairMoment_diagonalMap q g.f v v' F j Q hNQ).symm
  · rw [hl]
    apply Finset.sum_congr rfl
    intro d _
    rw [twoVisitMass_stepCumulative w hw hw1]
    ring

lemma labelProfile_unmarked_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f 1 1 F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∑ d,w d*F (timeSpin (q d)) := by
  obtain ⟨ν,η,hν,hgeo,hpair,hm,hl⟩ := labelProfile_pair_reference_exists k w hw hw1 q hq g 1 1 F
  refine ⟨ν,η,hν,hgeo,hpair,hm,?_⟩
  have h1 d := labelPairCoefficient_one k (stepCumulative w) (stepCumulative_pos w hw)
    (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) d
  simp_rw [h1] at hl
  simpa only [mul_one] using hl


theorem quantile_pair_reference_exists_oai (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j, (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f 1 1 F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ z,F z ∂(quantileSpinLaw q hq.measurable : Measure CompactOverlap) := by
  have hex (n : ℕ) := labelProfile_unmarked_reference_exists n (fun _=>1/(n+1:ℝ))
    (by intro i; positivity) (uniformQuantileWeights_sum n) (uniformQuantileLower n q)
    (uniformQuantileLower_mono n hq) g F
  choose μ ξ hGG hgeo hpair hm hl using hex
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence μ
  have hG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0 := by
    intro r i G a
    apply compactGGDefect_limit hlim r i G a
    simp only [Function.comp_apply,hGG]
    exact tendsto_const_nhds
  have hgeom : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
    apply (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mpr
    have hv := weak_limit_closed_full hlim compactSpinGeometry_closed (fun n => ?_)
    · simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
    · have hh := (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mp (hgeo (s n))
      rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
      exact ENNReal.coe_injective hh
  have hp : (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
      (quantileSpinLaw q hq.measurable : Measure CompactOverlap) := by
    let ρ : ProbabilityMeasure CompactOverlap := ⟨(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1),
    (Measure.isProbabilityMeasure_map_iff (show Measurable
      (fun array : CompactArray CompactJointOverlap => (array 0 1).1)
      from by fun_prop).aemeasurable).2 inferInstance⟩
    have he : ρ=quantileSpinLaw q hq.measurable := by
      apply probability_Icc_eq_of_moments
      intro r
      rw [quantileSpinLaw_integral q hq.measurable (fun x => x.val^r) (by fun_prop)]
      change (∫ x : CompactOverlap, x.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))=_
      rw [integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable (show Measurable (fun x : CompactOverlap => x.val^r) from by fun_prop).aestronglyMeasurable]
      let F : CompactOverlap→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x=>x.val^r,by fun_prop⟩
      let FF : CompactArray CompactJointOverlap→ᵇℝ := F.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
      have hν := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction FF).continuousAt.tendsto.comp hlim
      have hv n : (∫ Q, FF Q ∂(μ n : Measure _))=∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw := by
        change (∫ Q, F (Q 0 1).1 ∂(μ n : Measure (CompactArray CompactJointOverlap)))=_
        rw [hpair n F]
        exact (uniformQuantileCell_integral n (fun i => (uniformQuantileLower n q i:ℝ)^r)).symm
      change Tendsto (fun n => ∫ Q, FF Q ∂(μ (s n) : Measure (CompactArray CompactJointOverlap))) atTop
        (𝓝 (∫ Q, FF Q ∂(ν : Measure (CompactArray CompactJointOverlap)))) at hν
      simp_rw [hv] at hν
      exact tendsto_nhds_unique hν ((sampleQuantileLower_moment_tendsto q hq r).comp hs.tendsto_atTop)
    exact congrArg (fun x : ProbabilityMeasure CompactOverlap => (x : Measure CompactOverlap)) he
  obtain ⟨η,-,t,ht,hη⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ξ (s n)))
  have hv := hlim.comp ht.tendsto_atTop
  refine ⟨ν,η,hG,hgeom,hp,?_,?_⟩
  · intro j
    let A : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ :=
      (scalarRestorationPairMoment g.f 1 1 F j).compContinuous
        ⟨fun Q i l => (Q i l).1.val,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*x.2.val^j ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) at h₁
    simp_rw [hm] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · let A : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*restorationReciprocal g.f 2 x.2,
        (continuous_subtype_val.comp continuous_fst).mul
          ((restorationReciprocal g.f 2).continuous.comp continuous_snd)⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ := F.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) at h₁
    simp_rw [hl,←hpair] at h₁
    have he := tendsto_nhds_unique h₁ h₂
    rw [he,←hp]
    exact (integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
      from by fun_prop).aemeasurable F.measurable.aestronglyMeasurable).symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists_oai := @OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists_oai
