-- Prove2me | solution 1 for OAI.CompactMellinBridge.outside_compact_euler_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:43.776485+00:00
-- url     : https://prove2.me/submissions/d498a472-3207-4baf-acd5-2b555bdb212e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactMellinBridge_compact_weight_mellin_convergent
import Theorems.Thm_OAI_CompactMellinBridge_weighted_term_integrable
import Theorems.Thm_OAI_CompactMellinBridge_weighted_terms_fubini
import Theorems.Thm_OAI_CompactMellinBridge_outsideCoeff_baseChange_zero
import Theorems.Thm_OAI_CompactMellinBridge_outsideCompactSum_hasSum
import Theorems.Thm_OAI_CompactMellinBridge_mellin_weighted_sum
import Theorems.Thm_OAI_FiniteSFactor_normFiberLSeries_finiteEuler_baseChange
import Theorems.Thm_OAI_FiniteSFactor_outsideCoeff_LSeriesSummable_baseChange
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_baseChange_eq_pairInverseCoeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_inverse_euler_identity


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
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) (hs : 2 < s.re) :
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
      (finiteEulerFactor χ S s *
        mellin (fun D : ℝ => (outsideCompactSum χ S W) D⁻¹) (-s)) =
      mellin W s := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlsum : LSeriesSummable a s :=
    FiniteSFactor.outsideCoeff_LSeriesSummable_baseChange χ S s hs
  have hM := mellin_weighted_sum a W (outsideCompactSum χ S W) s
    ha0 hF
    (weighted_term_integrable a ha0 W s
      (compact_weight_mellin_convergent W hW hsupp s))
    (weighted_terms_fubini a ha0 W s hlsum) hlsum
  have hnorm := FiniteSFactor.normFiberLSeries_finiteEuler_baseChange
    χ S hS s hs
  change LSeries (ShortDraftHeckeBridge.normFiberCoeff
    (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
    finiteEulerFactor χ S s * LSeries a s at hnorm
  have hcoeff := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
  have hpair := ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
    χ (ShortDraftHeckeBridge.baseChangeChar χ)
    (ShortDraftHeckeBridge.baseChangeWeight χ) hcoeff s
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity
    χ (ShortDraftHeckeBridge.baseChangeChar χ) s (by linarith : 1 < s.re)
  have hfinite :
      (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s) = 1 := by
    rw [← hnorm, hpair]
    exact hEuler
  rw [hM]
  calc
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * (mellin W s * LSeries a s)) =
      ((χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s)) * mellin W s := by ring
    _ = mellin W s := by rw [hfinite]; ring
end OAI.CompactMellinBridge
