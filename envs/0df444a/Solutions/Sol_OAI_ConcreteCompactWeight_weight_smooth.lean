-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.weight_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:46.831497+00:00
-- url     : https://prove2.me/submissions/fc0f7ceb-2baa-406e-89f1-8612dc684e82

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_bump_smooth
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_smooth
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_pos

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
open OAI.ConcreteCompactWeight
namespace OAI.ConcreteCompactWeight
theorem _root_.solution (ρ : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (weight ρ) := by
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (bump y : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp bump_smooth
  have hlog : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Real.log (positiveExtension y)) :=
    positiveExtension_smooth.log (fun y => ne_of_gt (positiveExtension_pos y))
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => (Real.log (positiveExtension y) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hlog
  have hexp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))) :=
    (hc.mul contDiff_const).cexp
  exact hb.mul hexp
end OAI.ConcreteCompactWeight
