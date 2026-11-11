-- Prove2me | solution 1 for OAI.SmoothMobiusCorrection.eulerCorrection_differentiableOn_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:24:32.925292+00:00
-- url     : https://prove2.me/submissions/36dac62e-73c3-467c-85f6-cb7a52ea4bb5

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Theorems.Thm_OAI_SmoothMobiusCorrection_correctionTerm_differentiableOn
import Theorems.Thm_OAI_SmoothMobiusCorrection_eulerCorrection_locally_uniform

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SmoothMobiusCorrection
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
open scoped BigOperators Classical
open ActualEisensteinCubic
open Filter
namespace OAI.SmoothMobiusCorrection
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  apply (eulerCorrection_locally_uniform χ S σ hσ).differentiableOn
  · apply Filter.Eventually.of_forall
    intro t
    change DifferentiableOn ℂ (fun z => ∏ P ∈ t, (1+correctionTerm χ S P z)) _
    apply DifferentiableOn.fun_finsetProd
    intro P hP
    exact (differentiableOn_const (𝕜 := ℂ) (c := (1:ℂ))).add
      (correctionTerm_differentiableOn χ S P σ hσ.le)
  · exact isOpen_lt continuous_const Complex.continuous_re
end OAI.SmoothMobiusCorrection
