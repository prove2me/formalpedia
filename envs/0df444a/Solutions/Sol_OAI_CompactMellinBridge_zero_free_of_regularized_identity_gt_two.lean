-- Prove2me | solution 1 for OAI.CompactMellinBridge.zero_free_of_regularized_identity_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:37.228209+00:00
-- url     : https://prove2.me/submissions/8db00eec-5413-401b-9162-02034dd77cb9

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactMellinBridge_zero_free_of_analytic_identity_gt_two

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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    (σ : ℝ) (hσ : σ < 2) (G Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * G s)
    (heq : ∀ s : ℂ, 2 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hWregular : AnalyticOnNhd ℂ
      (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity_gt_two σ hσ
    Lregular M (fun s : ℂ => (s - 1) * W s)
    hLregular hM hWregular heq ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2
end OAI.CompactMellinBridge
