-- Prove2me | solution 1 for Kyprianou.Ch01.measureFirstMarkUnionEqFloorFromAESupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:54:00.769801+00:00
-- url     : https://prove2.me/submissions/0aa32742-1048-4177-aee0-b82a1b16044c

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (m : Ω → ℝ)
    (hSupport : ∀ᵐ ω ∂Q, ∃ j : ℕ, m ω = (j : ℝ) - 1)
    (F : ℕ → Ω → ℕ) (B : Ω → Prop) (k : ℕ) :
    Q (⋃ j : ℕ, {ω : Ω |
        m ω = (j : ℝ) - 1 ∧ F j ω = k ∧ B ω}) =
      Q {ω : Ω |
        F (Int.floor (m ω + 1)).toNat ω = k ∧ B ω} := by
  apply measure_congr
  filter_upwards [hSupport] with ω ⟨j, hj⟩
  have hfloor : (Int.floor (m ω + 1)).toNat = j := by
    rw [hj]
    simp
  apply propext
  constructor
  · intro hh
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
    have hm : m ω = (i : ℝ) - 1 := hi.1
    have hij : i = j := by
      have hhij : (i : ℝ) = (j : ℝ) := by linarith
      exact_mod_cast hhij
    subst i
    exact ⟨by simpa only [hfloor] using hi.2.1, hi.2.2⟩
  · intro hh
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    exact ⟨hj, by simpa only [hfloor] using hh.1, hh.2⟩
