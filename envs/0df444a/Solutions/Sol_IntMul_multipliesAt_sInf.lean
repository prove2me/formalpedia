-- Prove2me | solution 1 for IntMul.multipliesAt_sInf
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T08:49:39.946291+00:00
-- url     : https://prove2.me/submissions/ee6687c2-f619-4172-835a-d4f4fc7359a8

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Definitions.Def_IntMul_MultitapeModel

open IntMul

/-- The worst-case time `sInf {τ | MultipliesAt M n τ}` is itself a valid budget. -/
theorem solution {M : MultitapeTM} {n : ℕ} (h : ∃ τ, MultipliesAt M n τ) :
    MultipliesAt M n (sInf {τ : ℝ | MultipliesAt M n τ}) := by
  set S : Set ℝ := {τ : ℝ | MultipliesAt M n τ}
  have hS : S = ⋂ (x : List Bool) (y : List Bool) (_ : x.length = n) (_ : y.length = n),
      {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} := by
    ext τ; simp [S, MultipliesAt]
  have hclosed : IsClosed S := by
    rw [hS]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    classical
    by_cases hex : ∃ t : ℕ, M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))
    · have : {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} =
          Set.Ici ((Nat.find hex : ℕ) : ℝ) := by
        ext τ; simp only [Set.mem_ofPred_eq, Set.mem_Ici]; constructor
        · rintro ⟨t, ht, hh⟩; exact le_trans (by exact_mod_cast Nat.find_min' hex hh) ht
        · intro hτ; exact ⟨_, hτ, Nat.find_spec hex⟩
      rw [this]; exact isClosed_Ici
    · have : {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} = ∅ := by
        ext τ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨t, -, hh⟩; exact hex ⟨t, hh⟩
      rw [this]; exact isClosed_empty
  have hbdd : BddBelow S := by
    refine ⟨0, fun τ hτ => ?_⟩
    obtain ⟨t, ht, -⟩ := hτ (List.replicate n false) (List.replicate n false) (by simp) (by simp)
    exact le_trans (Nat.cast_nonneg t) ht
  exact hclosed.csInf_mem h hbdd
