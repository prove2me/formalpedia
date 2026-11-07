-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.supportFamily_primePool_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:16:45.976418+00:00
-- url     : https://prove2.me/submissions/077a0575-8d4a-4f1e-8551-c55b8e490763

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_smoothed_poisson
import Theorems.Thm_OAI_ConcretePrimeRowBridge_conjugateIdealRowSum_smoothed_summable


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
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcretePrimeRowBridge (conjugateIdealRowSum mobiusIdealColumn idealPairPoissonKernel
  primePool mem_primePool_iff conjugateIdealRowSum_smoothed_summable
  conjugateIdealRowSum_smoothed_poisson)
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good
  recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ∀ Q : primePool (supportIdealFamily (fun i => Ideal.span {p i}) S),
      ringChar (O ⧸ Q.val) ≠ 2 := by
  intro Q
  obtain ⟨I, hI, hQ⟩ := mem_primePool_iff.mp Q.property
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
  have hp' (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hU0 : (∏ i ∈ U, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => (hp' i).ne_zero)
  obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hU0).mp hQ
  obtain ⟨i, hi, hdi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hdiv
  have he : Q.val = Ideal.span {p i} := associated_iff_eq.mp (hprime.associated_of_dvd (hp' i) hdi)
  change ringChar (O ⧸ Q.val) ≠ 2
  rw [he]
  exact hc i
end OAI.FirstPassCubeLabels
