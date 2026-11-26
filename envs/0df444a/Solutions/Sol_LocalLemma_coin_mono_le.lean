-- Prove2me | solution 1 for LocalLemma.coin_mono_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:22:37.764426+00:00
-- url     : https://prove2.me/submissions/bf27b02e-92ee-4d68-99d6-4d70331573dc

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Theorems.Thm_LocalLemma_coin_const_eq

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {ι : Type*} [Fintype ι] (E : Finset ι) :
    (coinMeasure ι).real {ω | ∃ b, ∀ i ∈ E, ω i = b} ≤ 2 * (1 / 2) ^ E.card := by
  have hs : {ω : ι → Bool | ∃ b, ∀ i ∈ E, ω i = b} =
      {ω | ∀ i ∈ E, ω i = true} ∪ {ω | ∀ i ∈ E, ω i = false} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨b, hb⟩; cases b <;> simp_all
    · rintro (h | h) <;> exact ⟨_, h⟩
  rw [hs]
  refine (measureReal_union_le _ _).trans ?_
  have h : ∀ b, (coinMeasure ι).real {ω | ∀ i ∈ E, ω i = b} = (1 / 2) ^ E.card := by
    intro b
    rw [Measure.real, coin_const_eq, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp
  rw [h, h]; linarith
end LocalLemma
