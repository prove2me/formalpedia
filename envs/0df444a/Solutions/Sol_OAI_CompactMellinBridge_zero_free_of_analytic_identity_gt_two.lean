-- Prove2me | solution 1 for OAI.CompactMellinBridge.zero_free_of_analytic_identity_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:22.937307+00:00
-- url     : https://prove2.me/submissions/8a8e1256-941e-4fa3-9c0c-4dafd025e8d6

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale

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
    (σ : ℝ) (hσ : σ < 2) (G M W : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re → G s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hthree : (3 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (3 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => G s * M s) =ᶠ[𝓝 (3 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 2).mem_nhds
      (by norm_num : (3 : ℂ) ∈ {s : ℂ | 2 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => G s * M s) W
      {s | σ < s.re} :=
    (hG.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hthree heventual
  intro hGρ
  have heqρ := hident hρ
  change G ρ * M ρ = W ρ at heqρ
  rw [hGρ, zero_mul] at heqρ
  exact hWρ heqρ.symm
end OAI.CompactMellinBridge
