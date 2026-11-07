-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_flat_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:15.298724+00:00
-- url     : https://prove2.me/submissions/667a22ad-c204-4e5c-aa46-c9ae06be2414

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_norm_le_exp
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (b : ℝ) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  let C : ℝ := ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)
  have hExp : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => Real.exp (-t / 2)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨C, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      normFiberExpSum_norm_le_exp χ ψ weight hcoeff ha0 t ht
  have hpow : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    have heq : (fun t : ℝ => Real.exp (-t / 2)) =
        (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) := by
      funext t
      congr 1
      ring
    rw [heq]
    exact
      (isLittleO_exp_neg_mul_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2) (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp
end OAI.ShortDraftHeckeBridge
