-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneIntegerIncrementBudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:50.972802+00:00
-- url     : https://prove2.me/submissions/dd7c45c6-db79-46c3-8889-0e9e095b73ae

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Successive increments of a monotone integer sequence in [0,1] have sum at most one. -/
theorem solution
    (f : Int → Real) (hm : Monotone f)
    (hn : ∀ k, 0 ≤ f k) (hb : ∀ k, f k ≤ 1) :
    Summable (fun k : Int => f (k+1)-f k) ∧
      (∑' k : Int, (f (k+1)-f k)) ≤ 1 := by
  classical
  let D := fun k : Int => f (k+1)-f k
  have hnn (k : Int) : 0 ≤ D k := sub_nonneg.mpr (hm (by omega))
  have hsum (s : Finset Int) : ∀ b : Int, (∀ k ∈ s, k < b) → ∑ k ∈ s, D k ≤ f b := by
    induction s using Finset.induction_on_max with
    | empty => intro b hb'; simpa using hn b
    | insert a s hmax ih =>
      intro b hb'
      have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
      rw [Finset.sum_insert ha]
      have h1 := ih a hmax
      have h2 : f (a+1) ≤ f b := hm (by have := hb' a (Finset.mem_insert_self _ _); omega)
      dsimp [D] at *
      linarith
  have hbound (s : Finset Int) : ∑ k ∈ s, D k ≤ 1 := by
    obtain ⟨b,hb'⟩ := s.bddAbove
    exact (hsum s (b+1) (fun k hk => by have := hb' hk; omega)).trans (hb (b+1))
  have hs : Summable D := summable_of_sum_le hnn hbound
  exact ⟨hs,hs.tsum_le_of_sum_le hbound⟩
