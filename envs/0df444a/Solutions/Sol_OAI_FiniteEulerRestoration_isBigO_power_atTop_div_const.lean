-- Prove2me | solution 1 for OAI.FiniteEulerRestoration.isBigO_power_atTop_div_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:32.180427+00:00
-- url     : https://prove2.me/submissions/fd7a2f6b-0f49-4cff-a94c-f06b38ddc795

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration

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
open OAI.FiniteEulerRestoration
namespace OAI.FiniteEulerRestoration
theorem _root_.solution {A : ℝ → ℂ} {σ N : ℝ}
    (hN : 0 < N) (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => A (D / N)) =O[atTop] (fun D : ℝ => D ^ σ) := by
  have hshift : (fun D : ℝ => A (D / N)) =O[atTop]
      (fun D : ℝ => (D / N) ^ σ) :=
    hA.comp_tendsto ((tendsto_div_const_atTop_of_pos hN).2 tendsto_id)
  have hconst : (fun D : ℝ => (N ^ σ)⁻¹ * D ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) :=
    isBigO_const_mul_self (N ^ σ)⁻¹ (fun D : ℝ => D ^ σ) atTop
  have hpower : (fun D : ℝ => (D / N) ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply hconst.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
    rw [Real.div_rpow hD hN.le]
    ring
  exact hshift.trans hpower
end OAI.FiniteEulerRestoration
