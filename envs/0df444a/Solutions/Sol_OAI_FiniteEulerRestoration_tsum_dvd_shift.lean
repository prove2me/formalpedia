-- Prove2me | solution 1 for OAI.FiniteEulerRestoration.tsum_dvd_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:36.930666+00:00
-- url     : https://prove2.me/submissions/19dc45fd-ecfd-45c9-b711-28ada958955e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.FiniteEulerRestoration
namespace OAI.FiniteEulerRestoration
theorem _root_.solution {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (φ : ℕ → ℂ) :
    (∑' n : ℕ, if N ∣ n then b (n / N) * φ n else 0) =
      ∑' m : ℕ, b m * φ (N * m) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  let g : ℕ → ℂ := fun m => b m * φ (N * m)
  have hindex (m : ℕ) : f (N * m) = g m := by
    simp [f, g, hN]
  change (∑' n : ℕ, f n) = ∑' m : ℕ, g m
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x : Function.support g => N * x.1) ?_ ?_ ?_
  · intro x y hxy
    apply Subtype.ext
    exact Nat.mul_left_cancel hN hxy
  · intro n hn
    have hdiv : N ∣ n := by
      by_contra hnot
      have : f n = 0 := by simp [f, hnot]
      exact hn this
    let m := n / N
    have hnm : N * m = n := Nat.mul_div_cancel' hdiv
    have hgm : g m ≠ 0 := by
      intro hg
      apply hn
      rw [← hnm, hindex, hg]
    exact ⟨⟨m, hgm⟩, hnm⟩
  · intro x
    exact hindex x.1
end OAI.FiniteEulerRestoration
