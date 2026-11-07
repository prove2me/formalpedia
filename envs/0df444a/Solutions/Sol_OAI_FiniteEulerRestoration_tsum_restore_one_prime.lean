-- Prove2me | solution 1 for OAI.FiniteEulerRestoration.tsum_restore_one_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:01.201364+00:00
-- url     : https://prove2.me/submissions/d61b03aa-71d2-4c34-a786-d02664ccfebc

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_FiniteEulerRestoration_tsum_dvd_shift
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
    (c : ℂ) (a b φ : ℕ → ℂ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * φ n))
    (hshift : Summable (fun m => b m * φ (N * m))) :
    (∑' n : ℕ, a n * φ n) =
      (∑' n : ℕ, b n * φ n) +
        c * (∑' m : ℕ, b m * φ (N * m)) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  have hcomp : (fun m => f (N * m)) = (fun m => b m * φ (N * m)) := by
    funext m
    simp [f, hN]
  have hinj : Function.Injective (fun m : ℕ => N * m) :=
    fun _ _ h => Nat.mul_left_cancel hN h
  have hsupport : ∀ n, n ∉ Set.range (fun m : ℕ => N * m) → f n = 0 := by
    intro n hn
    have hnot : ¬N ∣ n := by
      intro hd
      exact hn ⟨n / N, Nat.mul_div_cancel' hd⟩
    simp [f, hnot]
  have hf : Summable f := by
    rw [← (hinj.summable_iff hsupport)]
    change Summable (fun m => f (N * m))
    rw [hcomp]
    exact hshift
  have hfc : Summable (fun n => c * f n) := hf.mul_left c
  have hpoint (n : ℕ) : a n * φ n = b n * φ n + c * f n := by
    rw [hcoeff n]
    by_cases hd : N ∣ n
    · simp [f, hd]
      ring
    · simp [f, hd]
  calc
    (∑' n : ℕ, a n * φ n) = ∑' n : ℕ, (b n * φ n + c * f n) := by
      congr 1
      funext n
      exact hpoint n
    _ = (∑' n : ℕ, b n * φ n) + ∑' n : ℕ, c * f n :=
      hb.tsum_add hfc
    _ = (∑' n : ℕ, b n * φ n) + c * (∑' m : ℕ, b m * φ (N * m)) := by
      rw [tsum_mul_left, tsum_dvd_shift hN b φ]
end OAI.FiniteEulerRestoration
