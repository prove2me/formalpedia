-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.WordRAM.code_relocation_correct
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T17:56:55.372746+00:00
-- url     : https://prove2.me/submissions/463d84fd-e83d-433a-929b-e161bfc97079

import Definitions.Def_ITPIRPreproc_MatchVec_RAMRelocation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace ITPIRPreproc.MatchVec.WordRAM

@[simp] theorem relocate_space (offset : ℕ) (s : State) :
    space (relocateState offset s) = space s := rfl

@[simp] theorem relocate_wordSize (inp : List Bool) (offset : ℕ) (s : State) :
    wordSize inp (relocateState offset s) = wordSize inp s := rfl

theorem relocate_fetch (precode P : Program) (pc : ℕ) :
    (placeAfter precode P)[precode.length+pc]? = (P[pc]?).map (relocateInstr precode.length) := by
  unfold placeAfter
  rw [List.getElem?_append_right (by omega)]
  simp

theorem relocate_step (precode P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) :
    step (placeAfter precode P) inp ω (relocateState precode.length s) =
      relocateState precode.length (step P inp ω s) := by
  by_cases hs : s.halted = true
  · simp [step, relocateState, hs]
  · unfold step
    simp only [relocateState, hs, Bool.false_eq_true, ↓reduceIte]
    rw [relocate_fetch]
    cases hf : P[s.pc]? with
    | none => rfl
    | some op =>
      cases op <;> simp [relocateInstr, Nat.add_assoc, wordSize, space]
      split_ifs <;> rfl

theorem relocate_deterministic (precode P : Program) :
    Deterministic (placeAfter precode P) ↔ Deterministic precode ∧ Deterministic P := by
  constructor
  · intro h
    constructor
    · intro op hop d
      exact h op (List.mem_append_left _ hop) d
    · intro op hop d hc
      apply h (.coin d) _ d rfl
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨op, hop, by simp [hc, relocateInstr]⟩
  · rintro ⟨ha,hb⟩ op hop d
    rcases List.mem_append.mp hop with hop | hop
    · exact ha op hop d
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hop
      have hx := hb old hold d
      cases old <;> simp_all [relocateInstr]

theorem relocate_streaming (precode P : Program) :
    Streaming (placeAfter precode P) ↔ Streaming precode ∧ Streaming P := by
  constructor
  · intro h
    constructor
    · intro op hop d a
      exact h op (List.mem_append_left _ hop) d a
    · intro op hop d a hc
      apply h (.inBitAt d a) _ d a rfl
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨op, hop, by simp [hc, relocateInstr]⟩
  · rintro ⟨ha,hb⟩ op hop d a
    rcases List.mem_append.mp hop with hop | hop
    · exact ha op hop d a
    · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hop
      have hx := hb old hold d a
      cases old <;> simp_all [relocateInstr]

theorem relocate_execution (precode P : Program) (inp : List Bool) (ω : ℕ → Bool)
    (s : State) (k : ℕ) :
    (step (placeAfter precode P) inp ω)^[k] (relocateState precode.length s) =
      relocateState precode.length ((step P inp ω)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, relocate_step]

end ITPIRPreproc.MatchVec.WordRAM

open ITPIRPreproc.MatchVec.WordRAM

theorem solution (precode P : Program) :
    (Deterministic (placeAfter precode P) ↔ Deterministic precode ∧ Deterministic P) ∧
    (Streaming (placeAfter precode P) ↔ Streaming precode ∧ Streaming P) ∧
    ∀ (inp : List Bool) (ω : ℕ → Bool) (s : State) (k : ℕ),
      (step (placeAfter precode P) inp ω)^[k] (relocateState precode.length s) =
        relocateState precode.length ((step P inp ω)^[k] s) := by
  exact ⟨relocate_deterministic precode P, relocate_streaming precode P,
    fun inp ω s k => relocate_execution precode P inp ω s k⟩
