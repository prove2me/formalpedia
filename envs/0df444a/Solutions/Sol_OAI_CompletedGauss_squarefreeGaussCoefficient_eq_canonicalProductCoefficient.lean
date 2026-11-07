-- Prove2me | solution 1 for OAI.CompletedGauss.squarefreeGaussCoefficient_eq_canonicalProductCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:31:50.507011+00:00
-- url     : https://prove2.me/submissions/28868cb7-9ded-4a30-a522-786b683689c7

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_CompletedGauss_product_primary
import Theorems.Thm_OAI_CompletedGauss_gaussTwo_eq_canonicalProductGauss
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span
import Theorems.Thm_OAI_CompletedGauss_squarefreeGaussCoefficient_eq


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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    squarefreeGaussCoefficient (Ideal.span {∏ i, p i}) =
      FiniteGaussPhase.canonicalProductCoefficient p hp hcop hgood := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  have hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0 := by rwa [hgen]
  have hsq : Squarefree (Ideal.span {∏ i, p i}) := by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      (Ideal.span_singleton_eq_bot.not.mpr hpall)).mpr
    rw [normalizedFactors_product]
    apply Multiset.Nodup.map
    · intro i j hij
      by_contra hne
      have ht := (hcop hne).sup_eq
      rw [hij, sup_idem] at ht
      exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
    · exact Finset.univ.nodup
  rw [squarefreeGaussCoefficient_eq _ hsq hI,
    gaussTwo_eq_canonicalProductGauss p hp hcop hgood hprimary hI, hgen]
  rfl
end OAI.CompletedGauss
