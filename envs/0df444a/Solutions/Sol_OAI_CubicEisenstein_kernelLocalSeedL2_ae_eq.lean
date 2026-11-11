-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelLocalSeedL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:45:49.1352+00:00
-- url     : https://prove2.me/submissions/eb7ab10d-f678-4299-a5b6-8f59781a963f

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
import Theorems.Thm_OAI_CubicEisenstein_kernelCompactProfile_seed
import Theorems.Thm_OAI_CubicEisenstein_compactProfileL2_ae_eq


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalSeedL2 S hS a b ha s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelQuotientSeed a b s) := by
  let B := kernelSeedHeightBound a S hS
  have hB := kernelSeedHeightBound_spec a S hS
  filter_upwards [kernelMassRestriction_coe S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)),
    compactProfileL2_ae_eq a B hB.1 (compactSeedProfile a b B ha s)] with q hr hp
  change kernelMassRestriction S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)) q=S.indicator (kernelQuotientSeed a b s) q
  rw [hr]
  by_cases hq : q∈S
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hp]
    exact kernelCompactProfile_seed a b B ha hab hB.1 hB.2.1 s q (hB.2.2 q hq)
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]
end OAI.CubicEisenstein
