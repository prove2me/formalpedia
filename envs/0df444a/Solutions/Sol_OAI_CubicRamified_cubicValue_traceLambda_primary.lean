-- Prove2me | solution 1 for OAI.CubicRamified.cubicValue_traceLambda_primary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:08:22.475949+00:00
-- url     : https://prove2.me/submissions/f6d7877d-e82e-4ee5-b5e6-2b8571ea95cd

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_CubicRamified_cubicExp_eq_of_dvd_sub
import Theorems.Thm_OAI_CubicRamified_cubicExp_add
import Theorems.Thm_OAI_ActualEisensteinCubic_omega_sq_for_norm
import Theorems.Thm_OAI_CubicRamified_cubicValue_lambda_primary
import Theorems.Thm_OAI_CubicRamified_cubicValue_neg
import Theorems.Thm_OAI_CubicRamified_cubicValue_omega_primary


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
open OAI.CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
namespace OAI.CubicRamified
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P traceLambda) = cubicExp (-B) := by
  have htrace : traceLambda = -omega * lambda := by
    change 1 + 2 * omega = -omega * (omega - 1)
    linear_combination omega_sq_for_norm
  rw [htrace, map_mul, map_mul, cubicValue_neg,
    cubicValue_omega_primary P hg A B hP, cubicValue_lambda_primary P hg A B hP]
  change cubicExp (2*A-B) * cubicExp A = cubicExp (-B)
  rw [← cubicExp_add]
  exact cubicExp_eq_of_dvd_sub ⟨A, by ring⟩
end OAI.CubicRamified
