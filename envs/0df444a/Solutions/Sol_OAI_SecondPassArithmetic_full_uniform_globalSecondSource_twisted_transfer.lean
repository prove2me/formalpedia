-- Prove2me | solution 1 for OAI.SecondPassArithmetic.full_uniform_globalSecondSource_twisted_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:00:39.739776+00:00
-- url     : https://prove2.me/submissions/f0bb338e-2cbb-4f72-b4d6-62753de8516c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Theorems.Thm_OAI_SecondPassIntegration_full_uniform_tupleSource_twisted_transfer
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondRecover_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondSource_eq_tupleSource
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondTuple_valid
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_child_coefficient_density_bound
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
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
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i})), ∀ (R : ℝ),0 < R → ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htransfer⟩ := SecondPassIntegration.full_uniform_tupleSource_twisted_transfer
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro ι _ p hp _ hcop hg hinj
    R hR θ₁ θ₂ s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  obtain ⟨b,hsep⟩ := htransfer R hR
  obtain ⟨hb,htrans⟩ := hsep θ₁ θ₂
  have htrans := htrans p hp hcop hg
  let r := globalSecondRecover p s
  have hr (x : GlobalSecondData ι) (hx : x∈s) : r (globalSecondTuple p x)=x :=
    globalSecondRecover_apply p hinj s q hs hfixed x hx
  have hvalid : ∀ y∈s.image (globalSecondTuple p),
      SecondPassFiber.Valid y (newLabel y) q.1 (newRow y) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hv := globalSecondTuple_valid p x (hs x hx)
    simpa only [hfixed x hx] using hv
  have hmap' : ∀ y∈s.image (globalSecondTuple p),(newLabel y,newRow y)∈T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hmap x hx
  have hw' : ∀ y∈s.image (globalSecondTuple p),
      ‖(w ∘ r) y‖*‖outerWindow V ((z ∘ r) y) ((ud ∘ r) y) ((ue ∘ r) y) ((uv ∘ r) y) ((kap ∘ r) y)‖ ≤ B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using hw x hx
  have hlabel : ∀ y∈s.image (globalSecondTuple p),Ideal.span {(globalSecondLabel p ∘ r) y}=newLabel y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using globalSecondLabel_span p x
  have hh := htrans (s.image (globalSecondTuple p)) T q.1 (w ∘ r) B lengthScale (globalSecondLabel p ∘ r)
    F Ψ₁ Ψ₂ (fixedTripleMask m q) (z ∘ r) (ud ∘ r) (ue ∘ r) (uv ∘ r) (kap ∘ r) X₁ X₂
    hq hB hL hvalid hmap' ht hn hw' hlabel
  rw [← globalSecondSource_eq_tupleSource p hp hcop hg hinj s q hs hfixed] at hh
  apply hh.trans
  have hd := SecondPassIntegration.child_coefficient_density_bound p hp hcop hg F Ψ₁ Ψ₂
    (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b J ((1+R)^A)
    (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)) hb
  have hpow : 0 < (1+R)^A := pow_pos (by linarith) _
  have hi := (le_div_iff₀' hpow).mpr hd
  have hnn : 0 ≤ B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε := by positivity
  have hbnd := mul_le_mul_of_nonneg_left hi hnn
  convert hbnd using 1 ; ring
end OAI.SecondPassArithmetic
