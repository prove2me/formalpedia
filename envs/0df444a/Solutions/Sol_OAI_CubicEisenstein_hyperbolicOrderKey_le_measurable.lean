-- Prove2me | solution 1 for OAI.CubicEisenstein.hyperbolicOrderKey_le_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:43:15.948089+00:00
-- url     : https://prove2.me/submissions/99cfeb6d-0d68-4c97-a6b6-782fd8cff463

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicOrderKey_lt_measurable
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFrobenius_continuous
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous
namespace OAI.CubicEisenstein
theorem _root_.solution {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)} := by
  have he : {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)}=
      {x | hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)}ᶜ := by
    ext x
    change hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x) ↔ ¬hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)
    exact ⟨fun h => not_lt_of_ge h,fun h => le_of_not_gt h⟩
  rw [he]
  exact (hyperbolicOrderKey_lt_measurable g f hg hf).compl
end OAI.CubicEisenstein
