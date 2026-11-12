-- Prove2me | solution 1 for OAI.CubicKubota.CubeCuspData.comparison_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:19:43.113495+00:00
-- url     : https://prove2.me/submissions/21f7cd02-2f3c-4a22-b463-77f06c67f63a

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_PrimaryCongruences
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeResidueStrata
import Theorems.Thm_OAI_CubicKubota_comparison_primary
import Theorems.Thm_OAI_CubicKubota_comparison_levelTwo
import Theorems.Thm_OAI_CubicEisenstein_cubicSymbol_pow_denominator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicKubota_levelTwo_cube_comparison_phase


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
open scoped Classical MatrixGroups
open scoped Classical MatrixGroups BigOperators
open OAI.CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
open OAI.CubicKubota.CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}
namespace OAI.CubicKubota.CubeCuspData
theorem _root_.solution (A2:levelTwo) (d:CubeCuspData (A2:SL(2,Eis)) p q)
    (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A2:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A2:SL(2,Eis)) 1 0) p) :
    complexCharacter ⟨d.matrix*(A2:SL(2,Eis))⁻¹,d.congruent⟩ =
      cubeStratumSymbol p ((A2:SL(2,Eis)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N2:levelTwo:=⟨d.matrix,comparison_levelTwo A2 d.matrix d.congruent⟩
  have hN:lambda^2∣d.matrix 0 0-1:=comparison_primary _ _ d.congruent hA
  have he:=levelTwo_cube_comparison_phase A2 N2 p q d.exponent.val
    (by omega:d.exponent.val≤3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [←map_pow,←cubicSymbol_pow_denominator]
  apply congrArg eisEmbedding
  apply symbol_congr
  have hd:=gaussRep_mk_congr (p^(3-d.exponent.val)) (d.matrix 0 0)
  change p^(3-d.exponent.val)∣d.matrix 0 0*((A2:SL(2,Eis)) 1 0)-
    GaussianShiftedPartition.representative (p^(3-d.exponent.val))
      (Ideal.Quotient.mk _ (d.matrix 0 0))*((A2:SL(2,Eis)) 1 0)
  convert dvd_mul_of_dvd_left (dvd_neg.mpr hd) ((A2:SL(2,Eis)) 1 0) using 1 ; ring
end OAI.CubicKubota.CubeCuspData
