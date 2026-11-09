-- Prove2me | solution 1 for OAI.CubicEisenstein.cuspChartL2_dense_smooth_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T20:05:15.799028+00:00
-- url     : https://prove2.me/submissions/9d44a80b-0a36-494c-b40c-1d1e3326df94

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CubicEisenstein_cuspChartVolume_finite
import Theorems.Thm_OAI_CubicEisenstein_cusp_compact_smooth_memLp

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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution (a : ℝ) (ha : 0<a) :
    Dense {f : CuspChartL2 a | ∃g : CuspChartCoordinates → ℂ,
      f=ᵐ[cuspChartVolume a] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      ∀j : Fin 3,MemLp (fun q => cuspCoordinateVelocity g q j) 2 (cuspChartVolume a)} := by
  let : IsFiniteMeasure (cuspChartVolume a) := cuspChartVolume_finite a ha
  apply (Lp.dense_hasCompactSupport_contDiff («μ» := cuspChartVolume a)
    (F := ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)).mono
  rintro f ⟨g,hg,hC,hgD⟩
  exact ⟨g,hg,hC,hgD,(cusp_compact_smooth_memLp g hgD hC a ha).2⟩
end OAI.CubicEisenstein
