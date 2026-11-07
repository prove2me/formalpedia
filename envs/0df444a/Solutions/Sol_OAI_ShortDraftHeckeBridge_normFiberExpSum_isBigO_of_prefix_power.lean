-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_isBigO_of_prefix_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:16:50.525393+00:00
-- url     : https://prove2.me/submissions/5ac0cce6-1094-42d7-8c7a-645679630e24

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_le_of_prefix_power
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ)) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  apply IsBigO.of_bound (3 * C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have h := normFiberExpSum_le_of_prefix_power χ ψ weight hcoeff ha0
    σ C hσ0 hσ1 hC hprefix D hD
  have hDnonneg : 0 ≤ D := (zero_le_one.trans hD)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hDnonneg σ)] using h
end OAI.ShortDraftHeckeBridge
