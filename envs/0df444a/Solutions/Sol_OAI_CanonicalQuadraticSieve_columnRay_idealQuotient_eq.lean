-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.columnRay_idealQuotient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:52:18.963915+00:00
-- url     : https://prove2.me/submissions/aadb8d5b-b4e9-43ec-8a11-6aeda850f061

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
import Theorems.Thm_OAI_CanonicalQuadraticSieve_primaryGenerator_unit_mod_four
import Theorems.Thm_OAI_ActualEisensteinCoordinates_congr_mod_four_of_residue_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_of_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul


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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (D I J : Ideal O) (hI : Admissible I) (_hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : columnRay I = columnRay J) :
    columnRay (idealQuotient D I) = columnRay (idealQuotient D J) := by
  have hD : Admissible D := admissible_of_dvd hI hDI
  have hu := primaryGenerator_unit_mod_four D hD
  obtain ⟨u, hu⟩ := hu
  have hray : residue (primaryGenerator I) = residue (primaryGenerator J) := hIJ
  obtain ⟨z, hz⟩ := congr_mod_four_of_residue_eq hray
  have hquot : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator I) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryGenerator J) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨z, hz⟩
  have hprodI : primaryGenerator I = primaryGenerator D * primaryGenerator (idealQuotient D I) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDI]
  have hprodJ : primaryGenerator J = primaryGenerator D * primaryGenerator (idealQuotient D J) := by
    rw [← primaryGenerator_mul, idealQuotient_mul hDJ]
  rw [hprodI, hprodJ, map_mul, map_mul, ← hu] at hquot
  have heq := (Units.mul_right_inj u).mp hquot
  exact QuadraticGaussRay.residue_eq_of_quotient_four_eq _ _ heq
end OAI.CanonicalQuadraticSieve
