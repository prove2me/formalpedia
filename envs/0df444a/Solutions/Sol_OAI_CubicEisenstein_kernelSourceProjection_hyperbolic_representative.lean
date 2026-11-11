-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelSourceProjection_hyperbolic_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:49:34.969731+00:00
-- url     : https://prove2.me/submissions/e82cf23e-c906-45da-b88d-46b9498db27d

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_OppositeCusp
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierExpansion
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_quasiMeasurePreserving
import Theorems.Thm_OAI_CubicEisenstein_sourceProjection_congr_ae
import Theorems.Thm_OAI_CubicEisenstein_kernelSourceProjection_ae_eq


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding
open CubicKubota
namespace OAI.CubicEisenstein
theorem _root_.solution (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f) :
    (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceProjection f := by
  have he := kernelProjection_quasiMeasurePreserving.ae_eq_comp
    (kernelSourceProjection_ae_eq F)
  change (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume]
      sourceProjection (fun w => F (integralOrbitProjection globalKubotaKernel w)) at he
  exact he.trans (sourceProjection_congr_ae _ _ hrep)
end OAI.CubicEisenstein
