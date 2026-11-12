-- Prove2me | solution 1 for OAI.CubicKubota.levelTwo_cube_phase_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:05:50.647229+00:00
-- url     : https://prove2.me/submissions/1c25333a-c7a4-4f7f-a40a-821366a29db3

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_three_shift_integer
import Theorems.Thm_OAI_CubicEisenstein_cubicSymbol_pow_denominator
import Theorems.Thm_OAI_CubicJacobiGlobal_primary_ne_zero
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_denominator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_pow_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity
import Theorems.Thm_OAI_CubicKubota_levelTwoComplexCharacter_primary
import Theorems.Thm_OAI_CubicKubota_levelTwo_entry_integer


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
open scoped Classical MatrixGroups
open OAI.CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicKubota
theorem _root_.solution (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring
end OAI.CubicKubota
