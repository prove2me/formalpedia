-- Prove2me | solution 1 for OAI.TwoPassProfiles.child_column_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:41.955997+00:00
-- url     : https://prove2.me/submissions/e9cbe969-e578-4af2-bfc3-58429313c42a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights

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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution
    (Lᵢ g v n : ℝ)
    (hLᵢ : Lᵢ ≠ 0) (hg : g ≠ 0) (hv : v ≠ 0) :
    (g * v * n) / Lᵢ = n / (Lᵢ / (g * v)) := by
  field_simp
end OAI.TwoPassProfiles
