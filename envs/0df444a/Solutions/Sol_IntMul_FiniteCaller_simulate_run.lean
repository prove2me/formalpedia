-- Prove2me | solution 1 for IntMul.FiniteCaller.simulate_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T19:46:34.57581+00:00
-- url     : https://prove2.me/submissions/5c3db8fd-ec63-44b2-84ba-aa7abae3751e

import Definitions.Def_IntMul_FiniteCaller
import Mathlib.Tactic

namespace IntMul.FiniteCaller

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem halted_step (M : MultitapeTM) (c : M.Cfg) (h : c.state = M.qHalt) :
    M.step c = c := by
  apply cfg_ext
  · simp [MultitapeTM.step, h, M.halt_fixed]
  · funext i
    simp only [MultitapeTM.step, h, M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step, h, M.halt_fixed]

private theorem halted_iterate (M : MultitapeTM) (c : M.Cfg)
    (h : c.state = M.qHalt) (n : ℕ) : M.step^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, halted_step M c h]

/-- Refine any bounded terminal run to its first halt, keeping its entire final
configuration. This prevents a caller from simulating padded frozen steps after
the subroutine has already returned. -/
private theorem first_halt (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (h : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T ∧ M.step^[t] c = M.step^[T] c ∧
      ∀ s : ℕ, s < t → (M.step^[s] c).state ≠ M.qHalt := by
  classical
  have hex : ∃ t : ℕ, (M.step^[t] c).state = M.qHalt := ⟨T, h⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex h
  have hh : (M.step^[t] c).state = M.qHalt := Nat.find_spec hex
  refine ⟨t, ht, ?_, ?_⟩
  · have he : T = (T - t) + t := by omega
    rw [he, Function.iterate_add_apply, halted_iterate M _ hh]
  · intro s hs
    exact Nat.find_min hex hs

private theorem nonhalt_step (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (h : c.state ≠ M.qHalt) :
    (machine M E initial dispatch).step (embed M E initial e dispatch c) =
      embed M E initial e dispatch (M.step c) := by
  classical
  apply cfg_ext
  · simp [MultitapeTM.step, embed, transition, h]
  · simp [MultitapeTM.step, embed, transition, h]
  · simp [MultitapeTM.step, embed, transition, h]

private theorem nonhalt_iterate (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (n : ℕ)
    (h : ∀ s : ℕ, s < n → (M.step^[s] c).state ≠ M.qHalt) :
    (machine M E initial dispatch).step^[n] (embed M E initial e dispatch c) =
      embed M E initial e dispatch (M.step^[n] c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by intro s hs; exact h s (by omega)),
        nonhalt_step M E initial e dispatch _ (h n (by omega)), Function.iterate_succ_apply']

private theorem return_step (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (h : c.state = M.qHalt) :
    (machine M E initial dispatch).step (embed M E initial e dispatch c) =
      returned M E initial e dispatch c := by
  classical
  apply cfg_ext
  · simp [MultitapeTM.step, embed, returned, transition, h]
  · funext i
    simp only [MultitapeTM.step, embed, transition, h, if_pos rfl]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step, embed, returned, transition, h]

/-- A genuine finite-table caller runs an arbitrary terminating subroutine and
takes exactly one additional dispatch transition. Both complete tape contents
and every head position are retained at the continuation boundary. -/
private theorem bounded_return (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (T : ℕ)
    (h : (M.step^[T] c).state = M.qHalt) :
    ∃ t : ℕ, t ≤ T + 1 ∧
      (machine M E initial dispatch).step^[t] (embed M E initial e dispatch c) =
        returned M E initial e dispatch (M.step^[T] c) := by
  obtain ⟨t, ht, he, hn⟩ := first_halt M c T h
  refine ⟨t + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', nonhalt_iterate M E initial e dispatch c t hn, he,
    return_step M E initial e dispatch _ h]

/-- A segment ending before halt is simulated for exactly its actual length.
Frozen-halt stability rules out an earlier halt in this segment. -/
private theorem nonterminal_run (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (T : ℕ)
    (h : (M.step^[T] c).state ≠ M.qHalt) :
    (machine M E initial dispatch).step^[T] (embed M E initial e dispatch c) =
      embed M E initial e dispatch (M.step^[T] c) := by
  apply nonhalt_iterate
  intro s hs hh
  have ht : T = (T - s) + s := by omega
  apply h
  rw [ht, Function.iterate_add_apply, halted_iterate M _ hh]
  exact hh

/-- The complete compiler interface covers both live segments and completed
subroutine calls. The latter include one actual continuation transition. -/
theorem simulate_run (M : MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (T : ℕ) :
    ((M.step^[T] c).state ≠ M.qHalt →
      (machine M E initial dispatch).step^[T] (embed M E initial e dispatch c) =
        embed M E initial e dispatch (M.step^[T] c)) ∧
    ((M.step^[T] c).state = M.qHalt →
      ∃ t : ℕ, t ≤ T + 1 ∧
        (machine M E initial dispatch).step^[t] (embed M E initial e dispatch c) =
          returned M E initial e dispatch (M.step^[T] c)) :=
  ⟨nonterminal_run M E initial e dispatch c T,
    bounded_return M E initial e dispatch c T⟩

end IntMul.FiniteCaller

#print axioms IntMul.FiniteCaller.bounded_return
#print axioms IntMul.FiniteCaller.simulate_run

open IntMul.FiniteCaller

theorem solution (M : IntMul.MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (T : ℕ) :
    ((M.step^[T] c).state ≠ M.qHalt →
      (machine M E initial dispatch).step^[T] (embed M E initial e dispatch c) =
        embed M E initial e dispatch (M.step^[T] c)) ∧
    ((M.step^[T] c).state = M.qHalt →
      ∃ t : ℕ, t ≤ T + 1 ∧
        (machine M E initial dispatch).step^[t] (embed M E initial e dispatch c) =
          returned M E initial e dispatch (M.step^[T] c)) :=
  IntMul.FiniteCaller.simulate_run M E initial e dispatch c T

#print axioms solution
