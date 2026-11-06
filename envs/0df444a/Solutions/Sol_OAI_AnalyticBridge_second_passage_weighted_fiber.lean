-- Prove2me | solution 1 for OAI.AnalyticBridge.second_passage_weighted_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:27.004507+00:00
-- url     : https://prove2.me/submissions/d4965a0e-b848-44b7-963e-0a44c5951418

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_AnalyticBridge_fixed_crt_choice_count
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
open OAI.AnalyticBridge
namespace OAI.AnalyticBridge
theorem _root_.solution
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K)
    (w : CRTChoice → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hw : ∀ q ∈ Q, w q ≤ M) :
    (∑ q ∈ Q, w q) ≤ M *
      ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) := by
  have hcard := fixed_crt_choice_count Q F K b0 hF hK hb0 hQ
  calc
    (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact hw q hq
    _ = (Q.card : ℝ) * M := by simp
    _ ≤ ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) * M := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
    _ = _ := by ring
end OAI.AnalyticBridge
