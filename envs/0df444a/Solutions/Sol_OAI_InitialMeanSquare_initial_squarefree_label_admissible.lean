-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_squarefree_label_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:39:15.4552+00:00
-- url     : https://prove2.me/submissions/95d816cc-47cc-4a5b-a999-b5788214af3e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_InitialMeanSquare_sourceLabel_span


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
open scoped BigOperators Classical SchwartzMap
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp hg
omit [DecidableEq ι]
namespace OAI.InitialMeanSquare
theorem _root_.solution
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (x : SecondExpansionData ι) (hs : Squarefree (Ideal.span {(sourceObservation p x).2})) :
    Admissible (Ideal.span {(sourceObservation p x).2}) := by
  have hn : (sourceObservation p x).2 ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hnI : Ideal.span {(sourceObservation p x).2} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr hn
  refine ⟨hnI,hs,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hnI).mp hP
  rw [sourceLabel_span] at hdiv
  have hfactor (S : Finset ι) (hd : P ∣ ∏ i ∈ S,Ideal.span {p i}) :
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 := by
    obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hd
    have hpi : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have he := (prime_dvd_prime_iff_eq hprime hpi).mp hPi
    rw [he]
    exact ⟨hg i,hc i⟩
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · exact hfactor _ h1
  · exact hfactor _ h2
end OAI.InitialMeanSquare
