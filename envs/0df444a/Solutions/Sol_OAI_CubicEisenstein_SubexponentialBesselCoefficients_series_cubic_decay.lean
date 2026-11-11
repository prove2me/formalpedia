-- Prove2me | solution 1 for OAI.CubicEisenstein.SubexponentialBesselCoefficients.series_cubic_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:40:47.233077+00:00
-- url     : https://prove2.me/submissions/f0c58696-522a-4e87-a984-d3694f66ecd7

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_series_cusp_decay
import Theorems.Thm_OAI_CubicEisenstein_residualCuspDecayRate_pos


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
local notation "O" => ActualEisensteinCubic.O
open OAI.CubicEisenstein.SubexponentialBesselCoefficients
namespace OAI.CubicEisenstein.SubexponentialBesselCoefficients
theorem _root_.solution (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cusp_decay a ha
  let k := residualCuspDecayRate
  have hk : 0<k := residualCuspDecayRate_pos
  refine ⟨C*(6/k^3),by positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have he : Real.exp (-k*v)*v^3≤6/k^3 := by
    have hb := Real.pow_div_factorial_le_exp (k*v) (mul_nonneg hk.le hv.le) 3
    norm_num only [Nat.factorial] at hb
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-k*v)).le
    rw [←Real.exp_add,show k*v+ -k*v=0 by ring,Real.exp_zero] at hm
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    nlinarith [hm]
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  calc
    _ ≤ (C*Real.exp (-k*v))*v^3 := mul_le_mul_of_nonneg_right (hbound v z hav) (pow_nonneg hv.le 3)
    _ = C*(Real.exp (-k*v)*v^3) := by ring
    _ ≤ C*(6/k^3) := mul_le_mul_of_nonneg_left he hC
end OAI.CubicEisenstein.SubexponentialBesselCoefficients
