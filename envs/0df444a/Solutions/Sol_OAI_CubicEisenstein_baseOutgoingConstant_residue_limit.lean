-- Prove2me | solution 1 for OAI.CubicEisenstein.baseOutgoingConstant_residue_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:32:08.085389+00:00
-- url     : https://prove2.me/submissions/c89f5b6d-9e46-4cb7-9b99-71bc3e2d0471

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceProjection
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringResidues
import Theorems.Thm_OAI_CubicEisenstein_scalar_residue_sub_continuous
import Theorems.Thm_OAI_CubicEisenstein_cubicEisensteinResidue_cusp_average
import Theorems.Thm_OAI_CubicEisenstein_cuspMainHeightFactor_differentiableAt
import Theorems.Thm_OAI_CubicEisenstein_kernelCuspAverageFamily_residue_limit


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
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution :
    Tendsto (fun s : ℂ => (s-4/3)*baseOutgoingConstant s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cuspConstantAverageResidue) := by
  have hf := kernelCuspAverageFamily_residue_limit 2 3 (by norm_num) (by norm_num)
  change Tendsto _ _ (𝓝 (kernelCuspStripAverage cubicEisensteinResidue)) at hf
  rw [cubicEisensteinResidue_cusp_average] at hf
  apply scalar_residue_sub_continuous _ _ _ _ hf
  exact continuousAt_const.mul
    (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt
end OAI.CubicEisenstein
