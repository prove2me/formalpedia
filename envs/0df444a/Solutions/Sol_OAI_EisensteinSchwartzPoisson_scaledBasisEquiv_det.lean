-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.scaledBasisEquiv_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:27.632012+00:00
-- url     : https://prove2.me/submissions/ee56d54e-505c-43a4-bac8-83fb9518c6cb

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_basisEquiv_det
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_complexMulEquiv_det

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
open OAI.EisensteinSchwartzPoisson
open scoped RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    LinearMap.det ((scaledBasisEquiv w hw c hc) : ℂ →ₗ[ℝ] ℂ) =
      Complex.normSq c * w.im := by
  change LinearMap.det
    (((complexMulEquiv c hc) : ℂ →ₗ[ℝ] ℂ).comp ((basisEquiv w hw) : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp, complexMulEquiv_det, basisEquiv_det]
end OAI.EisensteinSchwartzPoisson
