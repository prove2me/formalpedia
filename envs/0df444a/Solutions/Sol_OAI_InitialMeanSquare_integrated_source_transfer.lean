-- Prove2me | solution 1 for OAI.InitialMeanSquare.integrated_source_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:50:49.479804+00:00
-- url     : https://prove2.me/submissions/9b064039-8e36-4ef4-91ea-f23723ce020d

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Theorems.Thm_OAI_InitialMeanSquare_source_weighted_cauchy
import Theorems.Thm_OAI_InitialMeanSquare_sourceChildEnergy_le
import Theorems.Thm_OAI_InitialMeanSquare_sourceChildEnergy_continuous
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_JointLogSeparation_triple_integral_bound
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SecondPassIntegration_fixedRow_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
end
end
open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end
end InitialMeanSquare
namespace CubicEisenstein
section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv
example : InnerProductSpace ℂ EuclideanGradientL2 := inferInstance
example : CompleteSpace EuclideanGradientL2 := inferInstance
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv
example : InnerProductSpace ℂ EuclideanH1 := inferInstance
end CubicEisenstein
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
end
private theorem weighted_conjugate_pair_swap {α : Type*} (s : Finset α)
    (w P Q : α → ℂ) (B X Y : ℝ)
    (h : ‖∑ x ∈ s, w x * P x * star (Q x)‖ ≤ B * X * Y) :
    ‖∑ x ∈ s, w x * star (Q x) * P x‖ ≤ B * (Y * X) := by
  have he : (∑ x ∈ s, w x * star (Q x) * P x) =
      ∑ x ∈ s, w x * P x * star (Q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  exact h.trans_eq (by ring)
end InitialMeanSquare
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
namespace OAI.InitialMeanSquare
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
      (w : Frequency→SecondExpansionData ι→ℂ) (A K : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
      (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀q,∀x∈s,‖w q x‖≤A) → (∀x∈s,Continuous (fun q => w q x)) →
      ‖integratedSourceMode p hp hcop hg b₁ b₂ b₃ s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖≤
        A*C*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖*
          sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C,hC,hpointwise⟩ := source_weighted_cauchy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hA hK hs hmap hT hnorm hw hwc
  let f := sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂
  let G := sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := sourceChildEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := sourceChildEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀q,0≤G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false)*
    Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀q,G q≤M := by
    intro q
    dsimp [G,sourceGeometricMean,M]
    gcongr
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f sourceFixedMode
    apply continuous_finsetSum
    intro x hx
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 V₁ X₁ true
      (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) V₂ X₂ false
      (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact ((hwc x hx).mul h₁.star).mul h₂
  have hpoint : ∀q,‖f q‖≤(A*C*K^ε)*G q := by
    intro q
    let P : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false) u.2 (-u.1)
    let Q : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) u.2 u.1
    have hh := hpointwise p hinj r s T (w q) P Q
      A K hA hK hs hmap hT hnorm (hw q)
    have hh' := weighted_conjugate_pair_swap s (w q)
      (fun x => P (sourceObservation p x)) (fun x => Q (sourceObservation p x))
      (A*C*K^ε) _ _ hh
    simpa only [f,G,sourceFixedMode,sourceGeometricMean,sourceChildEnergy,P,Q,
      Bool.false_eq_true,ite_false,ite_true] using hh'
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0 (A*C*K^ε) M (by positivity) hM hpoint
end OAI.InitialMeanSquare
