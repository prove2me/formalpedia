-- Prove2me | solution 1 for NadlerCLS.mem_P_of_bits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:26:16.982017+00:00
-- url     : https://prove2.me/submissions/a037939d-309e-4dda-87eb-53b4e892a424

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Theorems.Thm_NadlerCLS_binarize_polyTime
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp

set_option autoImplicit false

namespace NadlerCLS.MemP

open CookPvsNP

/-- A one-tape machine deciding the language `{[true]}` in two steps. -/
def M : TM Bool where
  Q := Fin 4
  q₀ := 0
  qaccept := 2
  qreject := 3
  accept_ne_reject := by decide
  δ := fun q s =>
    if q = 0 then (if s = some true then (1, s, Move.right) else (3, s, Move.right))
    else if q = 1 then (if s = none then (2, s, Move.right) else (3, s, Move.right))
    else (q, s, Move.right)

theorem step_halting (c : Cfg Bool M.Q) (h : M.IsHalting c) : M.step c = c := by
  simp [TM.step, h]

theorem run_halting (c : Cfg Bool M.Q) (h : M.IsHalting c) (n : ℕ) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.run] at ih ⊢
    rw [Function.iterate_succ_apply', ih, step_halting c h]

theorem run_two (w : List Bool) :
    M.IsHalting (M.run 2 (M.init w)) ∧
      ((M.run 2 (M.init w)).state = M.qaccept ↔ w = [true]) := by
  rcases w with _ | ⟨b, _ | ⟨c, w⟩⟩
  · simp [TM.run, TM.init, TM.step, TM.IsHalting, M]
  · rcases b <;> simp [TM.run, TM.init, TM.step, TM.IsHalting, M]
  · rcases b <;> rcases c <;> simp [TM.run, TM.init, TM.step, TM.IsHalting, M]

theorem run_ge_two (w : List Bool) (n : ℕ) (hn : 2 ≤ n) :
    M.run n (M.init w) = M.run 2 (M.init w) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have : M.run (2 + m) (M.init w) = M.run m (M.run 2 (M.init w)) := by
    simp only [TM.run]
    rw [add_comm, Function.iterate_add_apply]
  rw [this, run_halting _ (run_two w).1]

theorem accepts_iff (w : List Bool) : M.Accepts w ↔ w = [true] := by
  constructor
  · rintro ⟨n, hn⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [TM.run, TM.init, M] at hn
      · rcases w with _ | ⟨b, w⟩
        · simp [TM.run, TM.init, TM.step, TM.IsHalting, M] at hn
        · rcases b <;> simp [TM.run, TM.init, TM.step, TM.IsHalting, M] at hn
    · rw [run_ge_two w n h] at hn
      exact (run_two w).2.mp hn
  · intro h
    exact ⟨2, (run_two w).2.mpr h⟩

theorem singleton_true_mem_P : ({[true]} : Lang Bool) ∈ P Bool := by
  have hmap : ∀ w : List Bool, w.map (Function.Embedding.refl Bool) = w := by
    intro w; induction w <;> simp_all
  refine ⟨Bool, inferInstance, Function.Embedding.refl _, M, 1, fun w => ?_, fun w => ?_⟩
  · rw [hmap, pow_one]
    unfold TM.HaltsWithin
    rcases Nat.lt_or_ge (w.length + 1) 2 with h | h
    · have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      simp [TM.run, TM.init, TM.step, TM.IsHalting, M]
    · rw [run_ge_two w _ h]
      exact (run_two w).1
  · rw [hmap, Set.mem_singleton_iff]
    exact (accepts_iff w).symm

end NadlerCLS.MemP

theorem solution (L : CookPvsNP.Lang (Option (Bool ⊕ Bool))) (χ : List Bool → List Bool)
    (hχ : CookPvsNP.PolyTimeComputable χ)
    (hL : ∀ x, x ∈ L ↔ χ (x.flatMap (fun c => match c with
      | none => [false]
      | some (Sum.inl b) => [true, false, b]
      | some (Sum.inr b) => [true, true, b])) = [true]) :
    L ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by
  refine CookPvsNP.mem_P_of_polyReducible L ({[true]} : CookPvsNP.Lang Bool) ⟨_,
    CookPvsNP.polyTimeComputable_comp _ χ NadlerCLS.binarize_polyTime hχ, fun x => ?_⟩
    NadlerCLS.MemP.singleton_true_mem_P
  rw [hL x]
  rfl
