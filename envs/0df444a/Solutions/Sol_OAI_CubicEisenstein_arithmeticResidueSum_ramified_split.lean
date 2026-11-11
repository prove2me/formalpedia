-- Prove2me | solution 1 for OAI.CubicEisenstein.arithmeticResidueSum_ramified_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:59:46.064297+00:00
-- url     : https://prove2.me/submissions/19f7f48d-6aa0-4f5e-99db-e10afc79197f

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
import Theorems.Thm_OAI_CubicEisenstein_ramified_primary_coprime
import Theorems.Thm_OAI_CubicEisenstein_arithmeticResidueSum_coprime_product
import Theorems.Thm_OAI_CubicJacobiGlobal_primary_ne_zero


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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h : Eis) (u : Eisˣ) (n : ℕ)
    (hn : 2≤n) (b : Eis) (hb : lambda^2∣b-1) :
    arithmeticResidueSum h ((u.val*lambda^n)*b)=
      eisEmbedding (symbol (u.val*lambda^n) b)*
      eisEmbedding (symbol (3*(u.val*lambda^n)) b)*
      arithmeticResidueSum h (u.val*lambda^n)*cubicUnitGaussSum h b :=
  arithmeticResidueSum_coprime_product h _ b (ramifiedElement_ne_zero u n)
    (primary_ne_zero b hb) (ramifiedElement_level u n hn) hb (ramified_primary_coprime u n b hb)
end OAI.CubicEisenstein
