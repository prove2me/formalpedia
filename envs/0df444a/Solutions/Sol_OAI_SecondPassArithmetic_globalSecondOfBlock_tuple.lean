-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondOfBlock_tuple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:05:41.078943+00:00
-- url     : https://prove2.me/submissions/8a4126f0-8f37-400f-8f2d-faad7ca3b4e7

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_cubeCoordinatesOfBlock_primeProduct

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)
variable {ι : Type*} [DecidableEq ι]
variable (p : ι → OAI.SecondPassArithmetic.O) [∀ i,(Ideal.span {p i}).IsMaximal]
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondTuple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      actualSecondTuple p B C D x.divisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency := by
  have hpoly := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
  have hspan (f : ℕ → ℕ → Bool → Bool → ℕ) := congrArg (fun a : O => (Ideal.span {a} : Ideal O)) (hpoly f)
  let c := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  have hJ : jLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  have hS : squarefreeLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) =
      squarefreeLabel p B (fun i => v₁ i+v₂ i) := hpoly (fun a b _ _ => bit (parity (a+b)))
  have hP₁ : primeProduct p c.support c.leftExponent = primeProduct p B v₁ := hpoly (fun a _ _ _ => a)
  have hP₂ : primeProduct p c.support c.rightExponent = primeProduct p B v₂ := hpoly (fun _ b _ _ => b)
  have hA₁ : aLabel p c.support c.leftBit = aLabel p B ε₁ := hpoly (fun _ _ e₁ _ => bit e₁)
  have hA₂ : aLabel p c.support c.rightBit = aLabel p B ε₂ := hpoly (fun _ _ _ e₂ => bit e₂)
  have hJ₂ : j2Label p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (FirstPassCubeLabels.evenDouble (a+b) e₁ e₂))
  change actualSecondTuple p c.support C D x.divisor x.overlap c.leftExponent c.rightExponent c.leftBit c.rightBit x.frequency = _
  unfold actualSecondTuple
  rw [hJ,hS,hP₁,hA₁,hA₂,hJ₂,hP₂]
end OAI.SecondPassArithmetic
