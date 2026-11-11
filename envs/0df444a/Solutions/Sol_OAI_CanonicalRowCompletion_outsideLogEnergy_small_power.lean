-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outsideLogEnergy_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:51:36.049334+00:00
-- url     : https://prove2.me/submissions/4d132d99-57c4-43f0-bc6f-c0591362e3cc

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CompletedEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_DensityTransfer
import Theorems.Thm_OAI_CanonicalRowCompletion_canonicalDescentPadding_budget
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideLogEnergy_state_small_power

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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z (canonicalDescentPadding ε) Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  have h:=canonicalDescentPadding_budget ε hε
  exact outsideLogEnergy_state_small_power S hSp hbad base hbase ρ q levelBound hρ hq hlevel hmodels
    ε (canonicalDescentPadding ε) h.1 h.2.1 h.2.2.1 h.2.2.2 A hA
end OAI.CanonicalRowCompletion
