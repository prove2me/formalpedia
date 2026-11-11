-- Prove2me | solution 1 for OAI.CubicEisenstein.cubicEisensteinResidue_continuous_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:48:58.443424+00:00
-- url     : https://prove2.me/submissions/0002f2db-0c31-48ae-83e5-6b8240a5b2ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ScatteringResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_OppositeCusp
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierExpansion
import Theorems.Thm_OAI_CubicEisenstein_cubicEisensteinResidue_cell_slices_ae
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_upper_period
import Theorems.Thm_OAI_CubicEisenstein_hyperbolic_eq_ae_of_period_cells
import Theorems.Thm_OAI_CubicEisenstein_cubicResidualFunction_continuous
import Theorems.Thm_OAI_CubicEisenstein_cubicResidualFunction_period
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection


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
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicEisenstein
theorem _root_.solution :
    (fun w => cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
      (measurable_integralOrbitProjection _)) cubicResidualFunction_continuous.measurable
  · intro v hv z n
    exact congrArg cubicEisensteinResidue (kernelProjection_upper_period v hv z n)
  · exact cubicResidualFunction_period
  · exact cubicEisensteinResidue_cell_slices_ae
end OAI.CubicEisenstein
