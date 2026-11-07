-- Prove2me | solution 1 for OAI.FiniteEulerRestoration.tsum_restore_one_prime_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:23.686075+00:00
-- url     : https://prove2.me/submissions/31b8f384-3205-4718-ba68-9f99c775cb54

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_FiniteEulerRestoration_tsum_restore_one_prime
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
    (c : ℂ) (a b : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun m => b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t)))) :
    (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
      (∑' n : ℕ, b n * Real.exp (-(n : ℝ) * t)) +
        c * (∑' m : ℕ, b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t))) := by
  have hscale (m : ℕ) :
      Real.exp (-((N * m : ℕ) : ℝ) * t) =
        Real.exp (-(m : ℝ) * ((N : ℝ) * t)) := by
    congr 1
    simp only [Nat.cast_mul]
    ring
  have hshift : Summable (fun m : ℕ =>
      b m * Real.exp (-((N * m : ℕ) : ℝ) * t)) := by
    convert hscaled using 1
    funext m
    rw [hscale]
  simpa only [hscale] using
    tsum_restore_one_prime hN c a b
      (fun n : ℕ => (Real.exp (-(n : ℝ) * t) : ℂ)) hcoeff hb hshift
end OAI.FiniteEulerRestoration
