-- Prove2me | solution 1 for OAI.CubicEisenstein.arithmeticResidueSum_eq_explicitRamifiedCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:47:41.134196+00:00
-- url     : https://prove2.me/submissions/5532bc72-9cc1-48cf-a55b-be644a2a4951

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringResidues
import Theorems.Thm_OAI_CubicEisenstein_ramified_arithmetic_explicit_table
import Theorems.Thm_OAI_CubicEisenstein_ramifiedUnitIndex_spec
import Theorems.Thm_OAI_CubicEisenstein_ramified_arithmetic_support


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
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h:Eis) (u:Eisˣ)
    (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=explicitRamifiedCoefficient h u n := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · exact ramified_arithmetic_explicit_table h (Classical.choose hd) u n
      (ramifiedUnitIndex u).val hn (ramifiedUnitIndex_spec u) (Classical.choose_spec hd)
  · by_contra hne
    exact hd (ramified_arithmetic_support h u n hn hne)
end OAI.CubicEisenstein
