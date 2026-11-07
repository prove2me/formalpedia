-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.fourier_prod_eq_iterated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:57:25.18721+00:00
-- url     : https://prove2.me/submissions/f56a5754-5783-48bf-97a2-84a1988f2718

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]
end OAI.EisensteinSchwartzPoisson
