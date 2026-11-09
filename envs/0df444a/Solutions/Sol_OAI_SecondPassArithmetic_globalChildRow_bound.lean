-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalChildRow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:45:34.589973+00:00
-- url     : https://prove2.me/submissions/aace8e1d-7cfb-4f09-89a8-9afffe71a200

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_HighKernelGeometry
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondDelta_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalNominalChildRow_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalNominalChildRow_bound

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K B F : ℝ) (hK : 0 < K) (hB : 0 < B) (hF : 0 < F)
    (x : GlobalSecondData ι) (side : Bool) (j : SecondLogIndex)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : secondLogK j/globalNominalChildRow p K B F x side ≤ globalSecondDelta p B F x side) :
    secondLogK j*Real.exp 1 ≤ Real.exp 1*K/globalSecondDelta p B F x side := by
  have hD := globalSecondDelta_pos p hp B F hB hF x side
  have hK' := globalNominalChildRow_pos p hp K B F hK hB hF x side
  have hk := (div_le_iff₀ hK').mp hretained
  have hsmall := globalNominalChildRow_bound p hp K B F hK hB hF x side hb₁ hb₂
  calc
    _ ≤ (globalSecondDelta p B F x side*globalNominalChildRow p K B F x side)*Real.exp 1 := by gcongr
    _ ≤ (globalSecondDelta p B F x side*(K/(globalSecondDelta p B F x side)^2))*Real.exp 1 := by gcongr
    _ = _ := by field_simp
end OAI.SecondPassArithmetic
