-- Prove2me | solution 1 for OAI.CubicEisenstein.arithmeticDirichletSeries_ramified_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:44:15.14923+00:00
-- url     : https://prove2.me/submissions/94b83dde-703b-4b01-8792-c90556f639ac

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
import Theorems.Thm_OAI_CubicEisenstein_arithmeticDirichlet_support_nonzero
import Theorems.Thm_OAI_CubicEisenstein_arithmeticDirichletTerm_summable_norm


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 2<s.re) (h : Eis) :
    arithmeticDirichletSeries s h=
      ∑'u:Eisˣ,∑'n:ℕ,∑'I:GoodIdeal,
        arithmeticDirichletTerm s h (ramifiedLowerMap (u,n,I)).1 := by
  have hsum:Summable (arithmeticDirichletTerm s h):=(arithmeticDirichletTerm_summable_norm s hs h).of_norm
  have hsub:Summable (fun c:NonzeroLevelLower=>arithmeticDirichletTerm s h c.1):=hsum.subtype _
  have hp:=ramifiedLowerEquiv.summable_iff.mpr hsub
  change Summable (fun p:Eisˣ×ℕ×GoodIdeal=>arithmeticDirichletTerm s h (ramifiedLowerMap p).1) at hp
  calc
    _=∑'c:NonzeroLevelLower,arithmeticDirichletTerm s h c.1:=
      (tsum_subtype_eq_of_support_subset (arithmeticDirichlet_support_nonzero s h)).symm
    _=∑'p:Eisˣ×ℕ×GoodIdeal,arithmeticDirichletTerm s h (ramifiedLowerMap p).1:=
      (ramifiedLowerEquiv.tsum_eq _).symm
    _=_:=by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro u
      exact (hp.prod_factor u).tsum_prod
end OAI.CubicEisenstein
