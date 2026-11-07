-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.weight_mellin_eq_bump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:45.750601+00:00
-- url     : https://prove2.me/submissions/d38e40ba-dc5e-424c-991a-80bdee0dce22

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_eq_cpow
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
    mellin (weight ρ) ρ = mellin (fun y : ℝ => (bump y : ℂ)) 0 := by
  have hpoint : Set.EqOn (weight ρ)
      (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) (Set.Ioi 0) := by
    intro y hy
    exact weight_eq_cpow ρ y hy
  rw [mellin]
  have heq :
      (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (ρ - 1) * weight ρ y) =
      mellin (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) ρ := by
    rw [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => by
      simp only [smul_eq_mul]
      rw [hpoint hy])
  simp only [smul_eq_mul]
  rw [heq]
  simpa only [smul_eq_mul, add_neg_cancel] using
    (mellin_cpow_smul (fun y : ℝ => (bump y : ℂ)) ρ (-ρ))
end OAI.ConcreteCompactWeight
