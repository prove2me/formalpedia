-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSourcePullback_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:32:32.534201+00:00
-- url     : https://prove2.me/submissions/d863a948-b449-4953-9237-f7b29535a276

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceQuotient
import Theorems.Thm_OAI_CubicEisenstein_kernelSourcePullback_rational_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceProjection_apply
import Theorems.Thm_OAI_CubicEisenstein_sourceSection_mul_reduction

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
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open CubicKubota
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (r : SL(2,ℤ)) (F : KernelQuotientL2) :
    kernelSourcePullback (rationalLift r) (kernelSourceProjection F)=kernelSourceProjection F := by
  rw [kernelSourceProjection_apply,map_smul,map_sum]
  apply congrArg (fun v : KernelQuotientL2 => (24:ℂ)⁻¹ • v)
  simp_rw [kernelSourcePullback_comp,←map_mul]
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q*r)) F=
      kernelSourcePullback (rationalLift (sourceRationalSection (q*rationalQuotient r))) F :=
    fun q => kernelSourcePullback_rational_eq _ _ (sourceSection_mul_reduction q r) F
  simp_rw [he]
  exact Function.Bijective.sum_comp (Group.mulRight_bijective (rationalQuotient r))
    (fun q => kernelSourcePullback (rationalLift (sourceRationalSection q)) F)
end OAI.CubicEisenstein
