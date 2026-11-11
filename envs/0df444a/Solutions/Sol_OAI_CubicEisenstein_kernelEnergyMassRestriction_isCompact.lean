-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelEnergyMassRestriction_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:47:02.067209+00:00
-- url     : https://prove2.me/submissions/08be5e8b-645b-4704-90a9-e9ce0ed32750

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_VariationalLaplacian
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopenedFibers
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactEnergyFamilies
import Theorems.Thm_OAI_CubicEisenstein_compact_of_norm_le_compact
import Theorems.Thm_OAI_CubicEisenstein_kernelMassRestriction_smooth_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyChartFamily_isCompact
import Theorems.Thm_OAI_CubicEisenstein_kernelCompact_mass_bound
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_dense
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyMass_core
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



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
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (K : Set KernelQuotient) (hK : IsCompact K) :
    IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) := by
  obtain ⟨t,C,hC,hbound⟩ := kernelCompact_mass_bound K hK
  have hsq : ∀u : KernelEnergyGraph,
      ‖kernelEnergyMassRestriction K hK.measurableSet u‖^2≤
        C*‖kernelEnergyChartFamily t u‖^2 := by
    intro u
    exact kernelEnergyGraphCore_dense.induction_on u
      (isClosed_le (by fun_prop : Continuous (fun v => ‖kernelEnergyMassRestriction K hK.measurableSet v‖^2))
        (by fun_prop : Continuous (fun v => C*‖kernelEnergyChartFamily t v‖^2)))
      (fun f => by
        change ‖kernelMassRestrictionCLM K hK.measurableSet
          (kernelEnergyMass (kernelEnergyGraphCore f))‖^2≤_
        rw [kernelEnergyMass_core,kernelMassRestriction_smooth_norm_sq]
        exact hbound f)
  apply compact_of_norm_le_compact _ (kernelEnergyChartFamily t)
    (kernelEnergyChartFamily_isCompact t)
  refine ⟨Real.sqrt C,fun u => ?_⟩
  have hs := hsq u
  have hc := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (kernelEnergyChartFamily t u))
  have he : (Real.sqrt C*‖kernelEnergyChartFamily t u‖)^2=C*‖kernelEnergyChartFamily t u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg (kernelEnergyMassRestriction K hK.measurableSet u)]
end OAI.CubicEisenstein
