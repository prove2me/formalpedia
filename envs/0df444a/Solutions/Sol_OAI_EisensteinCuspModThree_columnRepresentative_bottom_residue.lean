-- Prove2me | solution 1 for OAI.EisensteinCuspModThree.columnRepresentative_bottom_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:47:54.875453+00:00
-- url     : https://prove2.me/submissions/ac39b461-e472-4ab7-b6ce-9a3db78dd780

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateCuspProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
import Theorems.Thm_OAI_EisensteinCuspModThree_residue_intCast
import Theorems.Thm_OAI_EisensteinCuspModThree_residue_add
import Theorems.Thm_OAI_EisensteinCuspModThree_residue_mul
import Theorems.Thm_OAI_EisensteinCuspModThree_residue_mul_intCast
import Theorems.Thm_OAI_EisensteinCuspModThree_unitRepresentative_residue
import Theorems.Thm_OAI_EisensteinCuspModThree_cuspParameter_residue
import Theorems.Thm_OAI_EisensteinCuspModThree_columnRepresentative_entry
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul


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
open OAI.EisensteinCuspModThree
open scoped Classical MatrixGroups Matrix
local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein
namespace OAI.EisensteinCuspModThree
theorem _root_.solution (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl
end OAI.EisensteinCuspModThree
