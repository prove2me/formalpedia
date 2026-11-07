-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.canonicalProductGauss_eq_gaussBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:10:52.814921+00:00
-- url     : https://prove2.me/submissions/ff776185-4634-48ed-8972-4fff043eb8ce

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_cross_factors


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
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))
end OAI.FirstPassCubeLabels
