-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.error_of_perRoundCorrect
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:57:31.31508+00:00
-- url     : https://prove2.me/submissions/fa65a9b5-9101-4ef0-b70c-f35902e0284d

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants

open MeasureTheory
open scoped ENNReal
open ITPIRPreproc.MatchVec

/-- A uniform per-round error bound gives the advertised `T δ` bound for all adaptive
experiments. -/
theorem solution (S : Scheme) (n lam : ℕ) (δ : ℝ≥0∞)
    (h : PerRoundCorrect S n lam δ) :
    Correct S n lam (fun T => (T : ℝ≥0∞) * δ) := by
  intro D A hA T
  induction T with
  | zero => simp [history]
  | succ T ih =>
      have hset :
          {ω | ∃ r ∈ history S n lam D A ω (T + 1), r.output ≠ some (D r.index)} =
            {ω | ∃ r ∈ history S n lam D A ω T, r.output ≠ some (D r.index)} ∪
              {ω | RoundFailure S n lam D A ω T} := by
        ext ω
        simp only [history_succ_roundAt, List.mem_append, List.mem_singleton, Set.mem_setOf_eq,
          Set.mem_union]
        constructor
        · rintro ⟨r, (hr | rfl), hbad⟩
          · exact Or.inl ⟨r, hr, hbad⟩
          · exact Or.inr hbad
        · rintro (⟨r, hr, hbad⟩ | hbad)
          · exact ⟨r, Or.inl hr, hbad⟩
          · exact ⟨roundAt S n lam D A ω T, Or.inr rfl, hbad⟩
      rw [hset]
      calc
        tapeLaw ({ω | ∃ r ∈ history S n lam D A ω T, r.output ≠ some (D r.index)} ∪
            {ω | RoundFailure S n lam D A ω T}) ≤
            tapeLaw {ω | ∃ r ∈ history S n lam D A ω T, r.output ≠ some (D r.index)} +
              tapeLaw {ω | RoundFailure S n lam D A ω T} := measure_union_le _ _
        _ ≤ (T : ℝ≥0∞) * δ + δ := add_le_add ih (h D A hA T)
        _ = ((T + 1 : ℕ) : ℝ≥0∞) * δ := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
