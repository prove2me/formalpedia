-- Prove2me | solution 1 for OAI.AnalyticBridge.second_passage_positive_reassembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:20:27.576683+00:00
-- url     : https://prove2.me/submissions/4e6eb990-5048-424c-a3d4-7e93a291060f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_AnalyticBridge_second_passage_weighted_fiber
import Theorems.Thm_OAI_AnalyticBridge_fiber_mass_bound
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
    (Q : Finset CRTChoice) (T : Finset (ℕ × ℕ)) (b0 : ℕ)
    (hb0 : b0 ≠ 0)
    (w : CRTChoice → ℝ) (A : (ℕ × ℕ) → ℂ)
    (wmax M : ℝ) (hwmax : 0 ≤ wmax)
    (hweight : ∀ q ∈ Q, w q ≤ wmax)
    (hvalid : ∀ q ∈ Q,
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ (CRTChoice.childPair q).2 * b0)
    (hmap : ∀ q ∈ Q, CRTChoice.childPair q ∈ T)
    (hT : ∀ a ∈ T, a.1 ≠ 0 ∧ a.2 ≠ 0 ∧
      wmax *
        (((a.2.divisors.card ^ 6 *
          (b0 ^ 2 * a.2 ^ 3).divisors.card ^ 4 *
          (a.2 * b0).divisors.card * a.1.divisors.card : ℕ) : ℝ)) ≤ M) :
    (∑ q ∈ Q, w q * ‖A (CRTChoice.childPair q)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  apply fiber_mass_bound Q T CRTChoice.childPair w A M hmap
  intro a ha
  obtain ⟨hK, hF, hbound⟩ := hT a ha
  let S := Q.filter (fun q => CRTChoice.childPair q = a)
  have hS : ∀ q ∈ S,
      q.J * q.C * q.e * q.v = a.2 ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ a.2 * b0 ∧ q.d * q.e * q.kpp = a.1 := by
    intro q hq
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
    have hqa : CRTChoice.childPair q = a := (Finset.mem_filter.mp hq).2
    obtain ⟨hJ, hb, hA1, hA2, hd⟩ := hvalid q hqQ
    have hrow : q.d * q.e * q.kpp = a.1 := congrArg Prod.fst hqa
    have hlabel : q.J * q.C * q.e * q.v = a.2 := congrArg Prod.snd hqa
    simp only [CRTChoice.childPair] at hrow hlabel hd
    rw [hlabel] at hd
    exact ⟨hlabel, hJ, hb, hA1, hA2, hd, hrow⟩
  have hsum := second_passage_weighted_fiber S a.2 a.1 b0
    hF hK hb0 hS w wmax hwmax (by
      intro q hq
      exact hweight q (Finset.mem_filter.mp hq).1)
  exact hsum.trans hbound
end OAI.AnalyticBridge
