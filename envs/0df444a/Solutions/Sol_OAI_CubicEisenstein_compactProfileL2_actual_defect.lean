-- Prove2me | solution 1 for OAI.CubicEisenstein.compactProfileL2_actual_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:32:55.549246+00:00
-- url     : https://prove2.me/submissions/10b44df5-7912-4aeb-9bac-d84323e3b59e

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Theorems.Thm_OAI_CubicEisenstein_kernelL2Defect_ae_eq
import Theorems.Thm_OAI_CubicEisenstein_compactProfileL2_ae_eq
import Theorems.Thm_OAI_CubicEisenstein_compactHeightProfile_actual_defect

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactProfileL2 a b hab.le (compactDefectProfile a b ha s)=kernelL2Defect a b ha hab s := by
  apply Lp.ext
  grw [compactProfileL2_ae_eq,kernelL2Defect_ae_eq]
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a b hab.le (compactDefectProfile a b ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s) w
    rw [compactHeightProfile_actual_defect a b ha hab s]
end OAI.CubicEisenstein
