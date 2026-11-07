-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pair_zero_free_of_normFiber_continuation_principal_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:48:59.405327+00:00
-- url     : https://prove2.me/submissions/5cb93772-41ff-4568-9156-dcf36d4c0f2b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_continuation_principal_left
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairInverseCoeff_comm

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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff χ (1 : DirichletCharacter ℂ r) n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 ∧
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) ρ ≠ 0 := by
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ r) χ n := by
    intro n hn
    rw [hcoeff n hn, pairInverseCoeff_comm]
  have h := pair_zero_free_of_normFiber_continuation_principal_left
    (q := r) (r := q) χ hχ weight hcoeff' σ hσ M hM hMseries ρ hρ hρone
  exact ⟨h.2, h.1⟩
end OAI.ShortDraftHeckeBridge
