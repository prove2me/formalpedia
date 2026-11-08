-- Prove2me | solution 1 for HardyFLocal.eq25_26_single_vertex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:04:48.697322+00:00
-- url     : https://prove2.me/submissions/e73d61ae-c5de-4226-8901-f13bbf0c0bb9

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

open HardyFLocal in
theorem solution (S : FiducialFamily) (l : Ω) :
    S.map l = ∑ k, (Pi.single l 1 : Ω → ℝ) k • S.map k ∧
    coordsOf S.map (S.map l) = Pi.single l 1 ∧
    ∀ {V : Type} (T : V → V → PairTable) (x : V), chain T [(x, l)] = Pi.single l 1 := by
  have part1 : S.map l = ∑ k, (Pi.single l 1 : Ω → ℝ) k • S.map k := by
    rw [Fintype.sum_eq_single l]
    · simp
    · intro k hk
      simp [Pi.single_apply, hk]
  refine ⟨part1, ?_, ?_⟩
  · unfold coordsOf
    have hex : ∃ c : Ω → ℝ, S.map l = ∑ i, c i • S.map i := ⟨_, part1⟩
    rw [dif_pos hex]
    have hc := hex.choose_spec
    funext i
    have key := (Fintype.linearIndependent_iff.mp S.linearIndependent)
      (fun k => hex.choose k - (Pi.single l 1 : Ω → ℝ) k) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc, ← part1, sub_self]) i
    exact sub_eq_zero.mp key
  · intro V T x
    rfl
