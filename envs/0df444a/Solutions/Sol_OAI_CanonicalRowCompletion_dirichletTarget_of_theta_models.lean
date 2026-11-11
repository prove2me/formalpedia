-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.dirichletTarget_of_theta_models
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:01:00.825209+00:00
-- url     : https://prove2.me/submissions/f0d6c06b-47d3-4896-9931-c19e800c1617

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_ThetaNonvanishing
import Theorems.Thm_OAI_CanonicalRowCompletion_dirichlet_nonvanishing_of_theta_models

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
open scoped BigOperators Classical ContDiff Topology
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (hmodels : ∀(q₀ : ℕ) [NeZero q₀] (χ : DirichletCharacter ℂ q₀),
      ∃S : Finset (Ideal ActualEisensteinCubic.O),fixedBadPrimes⊆S ∧ (∀P∈S,Prime P) ∧
      ∃ρ q levelBound : ℝ,0<ρ ∧ 1<q ∧ 1≤levelBound ∧
        HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    ShortDraft.DirichletTarget := by
  intro q₀ _ χ z hz hpole
  obtain ⟨S,hbad,hSp,ρ,q,level,hρ,hq,hl,hm⟩:=hmodels q₀ χ
  exact dirichlet_nonvanishing_of_theta_models χ S hbad hSp ρ q level hρ hq hl hm z hz hpole
end OAI.CanonicalRowCompletion
