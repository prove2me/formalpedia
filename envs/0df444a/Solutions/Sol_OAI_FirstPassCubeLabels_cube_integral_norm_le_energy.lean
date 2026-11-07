-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.cube_integral_norm_le_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:09.793379+00:00
-- url     : https://prove2.me/submissions/de365087-0e29-41f4-bd20-637fb90e5d86

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Theorems.Thm_OAI_FirstPassCubeLabels_rayIdealEnergy_nonneg
import Theorems.Thm_OAI_FirstPassCubeLabels_idealPairReindex_norm_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
end
open ActualEisensteinCubic CompletedGauss
end CanonicalQuadraticSieve
section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge
end FourierBridge
namespace LocalLogFourier
end LocalLogFourier
namespace EisensteinSchwartzPoisson
end EisensteinSchwartzPoisson
end
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)
private theorem rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, ConcretePrimeRowBridge.conjugateIdealRowSum,
    ConcretePrimeRowBridge.mobiusIdealColumn]
  fun_prop
private theorem rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let P := fun i => Ideal.span {p i}
  let s := supportIdealFamily P (F \ D)
  let T := fun (t : ℝ) (I : Ideal O) =>
    ConcretePrimeRowBridge.mobiusIdealColumn
      (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
        else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C t (D ∪ recoveredSupport P (F \ D) I)) I *
      star (ConcretePrimeRowBridge.idealSexticRow s (supportIdealFamily_pos P (F \ D))
        (supportIdealFamily_good P hg (F \ D)) I h)
  refine ⟨∑ I ∈ s, ‖T 0 I‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ I ∈ s, T t I‖ ≤ _
  apply (norm_sum_le s (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  simp only [T, ConcretePrimeRowBridge.mobiusIdealColumn, norm_mul, hC]
private theorem rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)
private theorem rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)
private theorem integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hb⟩ := rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hb t)
end FirstPassCubeLabels
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : 𝓢(ℝ, ℂ)) (a : ℂ) :
    ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : ℝ => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert (integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₁]
    ring
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert (integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₂]
    ring
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal
end OAI.FirstPassCubeLabels
