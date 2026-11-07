-- Prove2me | solution 1 for OAI.CompactMellinBridge.normFiber_compact_euler_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:19:05.275581+00:00
-- url     : https://prove2.me/submissions/96dc2f38-5940-4c43-8c40-5da59df9c482

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_CompactMellinBridge_mellin_weighted_sum
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairInverseCoeff_LSeriesSummable
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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (s : ℂ) (hs : 1 < s.re)
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖)) :
    (χ.LFunction s * ψ.LFunction s) *
      mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
  have hM := mellin_weighted_sum
    (ShortDraftHeckeBridge.normFiberCoeff weight) W F s hcoeff0 hF
    hint hsumint
    ((LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs))
  rw [hM,
    ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
  calc
    (χ.LFunction s * ψ.LFunction s) *
        (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
        (χ.LFunction s * ψ.LFunction s *
          LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
    _ = mellin W s := by rw [hEuler]; ring
end OAI.CompactMellinBridge
