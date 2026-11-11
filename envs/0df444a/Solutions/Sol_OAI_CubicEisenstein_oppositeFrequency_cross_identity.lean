-- Prove2me | solution 1 for OAI.CubicEisenstein.oppositeFrequency_cross_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:48:49.804144+00:00
-- url     : https://prove2.me/submissions/248b1393-acc0-469f-90bc-cb4f4c87c7bd

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Theorems.Thm_OAI_CubicEisenstein_cuspWhittakerHeightFactor_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_opposite_cusp_fourier_average
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_analyticAt_nonreal
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_initial
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_opposite_initial


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
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith [hs.1]),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
end OAI.CubicEisenstein
