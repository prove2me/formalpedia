-- Prove2me | solution 1 for OAI.SmoothMobiusCorrection.prod_cut_primes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:55:19.896639+00:00
-- url     : https://prove2.me/submissions/c92d1fdd-bfd4-444e-b386-05d6b511c958

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Theorems.Thm_OAI_SmoothMobiusCorrection_outside_primeProduct_iff
import Theorems.Thm_OAI_CanonicalRowCompletion_primeValueHom_prime


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SmoothMobiusCorrection
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
open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)
namespace OAI.SmoothMobiusCorrection
theorem _root_.solution (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) (f : Ideal ActualEisensteinCubic.O→ℂ) :
    (∏Q∈t,if Q.val∈S then 0 else f Q.val)=outsideMask S (primeProduct t)*(∏Q∈t,f Q.val) := by
  by_cases ho : ∀P∈S,¬P∣primeProduct t
  · rw [outsideMask,if_pos ho,one_mul]
    apply Finset.prod_congr rfl
    intro Q hQ
    exact if_neg ((outside_primeProduct_iff S hS t).mp ho Q hQ)
  · rw [outsideMask,if_neg ho,zero_mul]
    have hh : ¬∀Q∈t,Q.val∉S := fun h => ho ((outside_primeProduct_iff S hS t).mpr h)
    push Not at hh
    obtain ⟨Q,hQ,hQS⟩ := hh
    exact Finset.prod_eq_zero hQ (if_pos hQS)
end OAI.SmoothMobiusCorrection
