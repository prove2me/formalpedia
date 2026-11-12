-- Prove2me | solution 1 for OAI.CubicEisenstein.diagonal_once_block_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:26:42.776198+00:00
-- url     : https://prove2.me/submissions/4baaf6d4-a232-4630-8615-33e8a7a4ff6e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CubeCuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Theorems.Thm_OAI_CubicEisenstein_diagonal_once_eisenstein_rows
import Theorems.Thm_OAI_CubicEisenstein_diagonal_once_summand
import Theorems.Thm_OAI_CubicEisenstein_summable_summand


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
open Filter MeasureTheory
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s=
    ∑l:Fin 3,affineCuspBlock (onceCuspScale t*omega^l.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s := by
  have hsum:=(diagonalOnceCuspIndex u t).summable_iff.mpr
    (summable_summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s hs)
  have ht:Summable (fun p:OnceRamifiedData=>affineLowerTerm (onceCuspScale t*omega^p.1.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val):=
    hsum.congr (fun p=>diagonal_once_summand u t z v hv s p)
  rw [mul_assoc,diagonal_once_eisenstein_rows,ht.tsum_prod,tsum_fintype]
  rfl
end OAI.CubicEisenstein
