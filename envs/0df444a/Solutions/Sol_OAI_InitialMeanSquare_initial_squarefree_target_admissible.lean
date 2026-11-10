-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_squarefree_target_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:49:10.689306+00:00
-- url     : https://prove2.me/submissions/79ba46ee-e029-488f-b116-6c13a17931a6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_InitialMeanSquare_initial_squarefree_label_admissible

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
    (s : Finset (SecondExpansionData ι)) :
    ∀ z ∈ sourceIdealTarget ((initialSquarefreeSector p s).image (sourceObservation p)),
      Admissible z.1 := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact initial_squarefree_label_admissible p hp hg hc x (Finset.mem_filter.mp hx).2
end OAI.InitialMeanSquare
