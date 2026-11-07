-- Prove2me | solution 1 for OAI.CompactMellinBridge.compact_weight_mellin_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:40.118226+00:00
-- url     : https://prove2.me/submissions/c5c5d0fe-1292-4466-812a-99d12c6228ea

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic
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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ) :
    AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re} := by
  let A : ℝ → ℂ := fun D => W D⁻¹
  have hcont : ContinuousOn A (Set.Ioi (0 : ℝ)) := by
    have hcontW : ContinuousOn W Set.univ := hW.continuous.continuousOn
    apply hcontW.comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    simp
  have hlocal : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
    have hDpos : 0 < D := hD.1
    have hDsmall : D < 1 / 2 := hD.2
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
    have hinv : 2 ≤ D⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inr hinv)
  have hzeroTop : A =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right hD hDinvpos.le
    have hinv : D⁻¹ ≤ 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inl hinv)
  have htop : A =O[atTop] (fun D : ℝ => D ^ σ) :=
    hzeroTop.isBigO.trans (isBigO_zero _ _)
  have hM := ShortDraftMellin.inverse_mellin_analytic A σ hlocal htop hzero
  simpa only [A, mellin_comp_inv, neg_neg] using hM
end OAI.CompactMellinBridge
